open Util
open Names
open Nameops
open Context
open Constr
open Globnames
open Pp
open List
open Libnames
open Tactics
open Tacticals
open Tacmach
open EConstr
open Equations_common
open Printer
open Ppconstr

open Syntax
open Context_map
open Splitting
open Covering
open Vars

open Cc_plugin.Cctac

type where_map = (constr * Names.Id.t * splitting) PathMap.t

type equations_info = {
 equations_id : Names.Id.t;
 equations_where_map : where_map;
 equations_f : EConstr.t;
 equations_prob : Context_map.context_map }

type ind_info = {
  term_info : term_info;
  pathmap : (Names.Id.t * Constr.t list) PathMap.t; (* path -> inductive name *)
  wheremap : where_map }

   
let find_helper_info env sigma info f =
  try List.find (fun (cst, arg') ->
         try Environ.QConstant.equal env cst (fst (destConst sigma f))
         with DestKO -> false)
	info.helpers_info
  with Not_found -> anomaly (str"Helper not found while proving induction lemma.")

let below_transparent_state () =
  Hints.Hint_db.transparent_state (Hints.searchtable_map "Below")

let simpl_star = 
  tclTHEN (to82 simpl_in_concl) (onAllHyps (fun id -> to82 (simpl_in_hyp (id, Locus.InHyp))))

let eauto_with_below ?depth ?(strategy=Class_tactics.Dfs) l =
  Class_tactics.typeclasses_eauto ~depth ~st:(below_transparent_state ()) 
    ~strategy (l@["subterm_relation"; "Below"; "rec_decision"])
    
let wf_obligations_base info =
  info.base_id ^ "_wf_obligations"

let simp_eqns l =
  let open Tacticals.New in
  tclREPEAT
    (tclTHENLIST [Autorewrite.autorewrite tclIDTAC l; tclTRY (eauto_with_below l)])

let simp_eqns_in clause l =
  let open Tacticals.New in
  tclREPEAT (tclTHENLIST 
		[Autorewrite.auto_multi_rewrite l clause;
		 tclTRY (eauto_with_below l)])

let autorewrites b = 
  let open Tacticals.New in
  tclREPEAT (Autorewrite.autorewrite Tacticals.New.tclIDTAC [b])

exception RewriteSucceeded of EConstr.t

let _rewrite_try_change tac = 
  Proofview.Goal.enter (fun gl ->
    let concl = Proofview.Goal.concl gl in
    Proofview.tclORELSE 
      (Proofview.tclTHEN tac 
      (Proofview.Goal.enter (fun gl ->
          let env = Proofview.Goal.env gl in
          let sigma = Proofview.Goal.sigma gl in
          let concl' = Proofview.Goal.concl gl in
          match Reductionops.infer_conv ~pb:Reduction.CONV env sigma concl concl' with
          | Some _ -> Proofview.tclZERO (RewriteSucceeded concl')
          | None -> Proofview.tclUNIT ())))
    (function
      | (RewriteSucceeded concl', _) -> convert_concl ~cast:true ~check:false concl' DEFAULTcast
      | (exn, info) -> Proofview.tclZERO ~info exn))

let autorewrite_one b =
  let rew_rules = Autorewrite.find_rewrites b in
  let rec aux rules =
    match rules with
    | [] -> Tacticals.New.tclFAIL 0 (str"Couldn't rewrite")
    | r :: rules ->
       let global, _univs = Constr.destRef r.Autorewrite.rew_lemma in
       let tac =
         Proofview.tclBIND
         (Tacticals.New.pf_constr_of_global global)
         (if r.Autorewrite.rew_l2r then Equality.rewriteLR else Equality.rewriteRL)
       in
       Proofview.tclOR tac
         (fun e -> if !debug then Feedback.msg_debug (str"failed"); aux rules)
  in aux rew_rules

let revert_last =
  Proofview.Goal.enter (fun gl ->
      let hyp = Tacmach.New.pf_last_hyp gl in
      revert [get_id hyp])

(** fix generalization *)

let rec mk_holes env sigma = function
| [] -> (sigma, [])
| arg :: rem ->
  let (sigma, arg) = Evarutil.new_evar env sigma arg in
  let (sigma, rem) = mk_holes env sigma rem in
  (sigma, arg :: rem)

let rec check_mutind env sigma k cl = match EConstr.kind sigma (Termops.strip_outer_cast sigma cl) with
| Prod (na, c1, b) ->
  if Int.equal k 1 then
    try
      let ((sp, _), u), _ = Inductiveops.find_inductive env sigma c1 in
      (sp, u)
    with Not_found -> error "Cannot do a fixpoint on a non inductive type."
  else
    check_mutind (push_rel (Context.Rel.Declaration.LocalAssum (na, c1)) env) sigma (pred k) b
| LetIn (na, c1, t, b) ->
    check_mutind (push_rel (Context.Rel.Declaration.LocalDef (na, c1, t)) env) sigma k b
| _ -> CErrors.user_err (str"Not enough products in " ++ Printer.pr_econstr_env env sigma cl)

open Context.Named.Declaration
(* Refine as a fixpoint *)
let mutual_fix li l =
  let open Proofview in
  let open Notations in
  let mfix env sigma gls =
    let gls = List.map Proofview.drop_state gls in
    let types = List.map (fun ev -> Evd.evar_concl (Evd.find sigma ev)) gls in
    let env =
      let ctxs = List.map (fun ev -> EConstr.Unsafe.to_named_context @@
                            Evd.evar_context (Evd.find sigma ev)) gls in
      let fst, rest = List.sep_last ctxs in
      if List.for_all (fun y -> Context.Named.equal Constr.equal fst y) rest then
        Environ.push_named_context fst env
      else env
    in
    let li =
      match li with
      | [] ->
         List.mapi (fun i ev -> match Evd.evar_ident ev sigma with
                                | Some id -> id
                                | None -> Id.of_string ("fix_" ^ string_of_int i)) gls
      | l -> List.map Id.of_string l
    in
    let () =
      let lenid = List.length li in
      let lenidxs = List.length l in
      let lengoals = List.length types in
      if not (Int.equal lenid lenidxs && Int.equal lenid lengoals) then
        CErrors.user_err
                         (str "Cannot apply mutual fixpoint, invalid arguments: " ++
                            int lenid ++ (str (String.plural lenid " name")) ++ str " " ++
                            int lenidxs ++ str (if lenidxs == 1 then " index"
                                                else " indices") ++ str" and " ++
                            int lengoals ++ str(String.plural lengoals " subgoal"))
    in
    let all = CList.map3 (fun id n ar -> (id,n,ar)) li l types in
    let (_, n, ar) = List.hd all in
    let (sp, u) = check_mutind env sigma n ar in
    let rec mk_sign sign = function
      | [] -> sign
      | (f, n, ar) :: oth ->
         let (sp', u')  = check_mutind env sigma n ar in
         if not (Environ.QMutInd.equal env sp sp') then
           error "Fixpoints should be on the same mutual inductive declaration.";
         if try ignore (Context.Named.lookup f sign); true with Not_found -> false then
           CErrors.user_err
                    (str "Name " ++ pr_id f ++ str " already used in the environment");
         mk_sign (LocalAssum (annotR f, EConstr.to_constr sigma ar) :: sign) oth
    in
    let sign = mk_sign (Environ.named_context env) all in
    let idx = Array.map_of_list pred l in
    let nas = Array.map_of_list nameR li in
    let body = ref (fun i -> assert false) in
    let one_body =
      Refine.refine ~typecheck:false
      (fun sigma ->
        let nenv = Environ.reset_with_named_context (Environ.val_of_named_context sign) env in
        let (sigma, evs) = mk_holes nenv sigma types in
        let evs = Array.map_of_list (Vars.subst_vars (List.rev li)) evs in
        let types = Array.of_list types in
        let decl = (nas,types,evs) in
        let () = body := (fun i -> mkFix ((idx,i),decl)) in
        sigma, !body 0)
    in
    let other_body i =
      Refine.refine ~typecheck:false
      (fun sigma -> sigma, !body (succ i))
    in
    tclDISPATCH (one_body :: List.init (Array.length idx - 1) other_body)
  in
  tclENV >>= fun env ->
  tclEVARMAP >>= fun sigma ->
  Unsafe.tclGETGOALS >>= mfix env sigma

let check_guard gls env sigma =
  let gl = Proofview.drop_state (List.hd gls) in
  try
    let evi = Evd.find sigma gl in
    match evi.Evd.evar_body with
    | Evd.Evar_defined b -> Inductiveops.control_only_guard (Evd.evar_env env evi) sigma b; true
    | Evd.Evar_empty -> true
  with Type_errors.TypeError _ -> false

let find_helper_arg env sigma info f args =
  let (cst, arg) = find_helper_info env sigma info f in
  cst, snd arg, args.(snd arg)
      
let find_splitting_var sigma pats var constrs =
  let rec find_pat_var p c =
    match p, decompose_app sigma c with
    | PRel i, (c, l) when i = var -> Some (destVar sigma c)
    | PCstr (c, ps), (f,l) -> aux ps l
    | _, _ -> None
  and aux pats constrs =
    assert(List.length pats = List.length constrs);
    List.fold_left2 (fun acc p c ->
      match acc with None -> find_pat_var p c | _ -> acc)
      None pats constrs
  in
    Option.get (aux (rev pats) constrs)

let rec intros_reducing () =
  let open Tacticals.New in
  Proofview.Goal.enter (fun gl ->
  let concl = Proofview.Goal.concl gl in
    match kind (Proofview.Goal.sigma gl) concl with
    | LetIn (_, _, _, _) -> tclTHEN hnf_in_concl (intros_reducing ())
    | Prod (_, _, _) -> tclTHEN intro (intros_reducing ())
    | _ -> tclIDTAC)
  
let cstrtac =
  Tacticals.New.tclTHENLIST [any_constructor false None]

let destSplit = function
  | Split (_, _, _, splits) -> Some splits
  | _ -> None

let destRefined = function
  | Refined (_, _, s) -> Some s
  | _ -> None

let destWheres = function
  | Compute (ctx, wheres, _, _) -> Some (ctx, wheres)
  | _ -> None

let map_opt_split f s =
  match s with
  | None -> None
  | Some s -> f s

let solve_ind_rec_tac info =
  observe_new "eauto with below"
    (eauto_with_below ~depth:20 ~strategy:Class_tactics.Bfs [info.base_id; wf_obligations_base info])

let change_in_app f args idx arg =
  let args' = Array.copy args in
  args'.(idx) <- arg;
  mkApp (f, args')

let hyps_after sigma env pos args =
  let open Context.Named.Declaration in
  List.fold_left (fun acc d -> Id.Set.add (get_id d) acc) Id.Set.empty env

let simpl_of csts =
  let opacify () = List.iter (fun (cst,_) ->
    Global.set_strategy (ConstKey cst) Conv_oracle.Opaque) csts
  and transp () = List.iter (fun (cst, level) ->
    Global.set_strategy (ConstKey cst) level) csts
  in opacify, transp

let gather_subst env sigma ty args len =
  let rec aux ty args n =
    if n = 0 then [] else
      match kind sigma ty, args with
      | Prod (_, _, ty), a :: args -> a :: aux (subst1 a ty) args (pred n)
      | LetIn (_, b, _, ty), args -> b :: aux (subst1 b ty) args (pred n)
      | _ -> assert false
  in aux ty args len

let annot_of_rec r = match r.struct_rec_arg with
  | MutualOn (Some (i, _)) -> Some (i + 1)
  | MutualOn None -> assert false
  | NestedOn (Some (i, _)) -> Some (i + 1)
  | NestedOn None -> Some 1
  | _ -> None

let aux_ind_fun info chop nested unfp unfids p =
  let open Tacticals.New in
  let rec solve_nested () =
    let open Proofview.Goal in
    Proofview.Goal.enter (fun gl ->
        let sigma = sigma gl in
        let concl = concl gl in
        let nested_goal =
          match kind sigma concl with
          | App (ind, args) ->
            let last = Array.last args in
            let hd, args = decompose_app sigma last in
            (try let fn, args = destConst sigma hd in
               let fnid = Label.to_id (Constant.label fn) in
               Some (CList.find (fun (p, _, _) -> Id.equal p fnid) nested)
             with DestKO | Not_found -> None)
          | _ -> None
        in
        match nested_goal with
        | Some (p, ty, prog) ->
          let fixtac =
            match prog.program_rec with
            | Some { rec_node = StructRec sr; rec_args } ->
              tclTHENLIST [fix prog.program_info.program_id (Option.default 1 (annot_of_rec sr));
                           tclDO rec_args intro]
            | _ -> Proofview.tclUNIT ()
          in
          let program_tac =
            tclTHEN fixtac (aux chop None [] prog.program_splitting)
          in
          tclTHEN (assert_by (Name (program_id prog)) ty program_tac)
            (observe_new "solving nested premises of compute rule"
              (solve_ind_rec_tac info.term_info))
        | None -> Proofview.tclUNIT ())

  and aux_program lctx chop unfp unfids porig p =
    let unfs = Option.map (fun s -> s.program_splitting) unfp in
    match p.program_rec with
    | None ->
      let is_rec, fixtac =
        let open Tacticals.New in
        match porig with
        | Some { Syntax.program_rec = Some (Structural ann) } ->
          (let idx =
             match ann with
             | NestedOn None -> Some 0
             | NestedNonRec -> None
             | MutualOn None -> assert false
             | NestedOn (Some (idx, _)) | MutualOn (Some (idx, _)) -> Some idx
           in
           match idx with
           | None -> false, intros
           | Some idx ->
             let recid = add_suffix p.program_info.program_id "_rec" in
             (* The recursive argument is local to the where, shift it by the
                length of the enclosing context *)
             let newidx = match unfs with None -> idx | Some _ -> idx in
             true, observe_new "struct fix norec" (tclTHENLIST [(* unftac false; *)
                 fix recid (succ newidx);
                 intros
                 (* unftac true *)]))
        | _ -> false, intros
      in
      tclTHEN fixtac (aux (fst chop, if is_rec then succ (snd chop) else snd chop) unfs unfids p.program_splitting)
    | Some t ->
      let cs = p.program_splitting in
      let ctx = t.rec_lets in
      let refine =
        let open Proofview.Goal in
        enter (fun gl ->
        let env = Proofview.Goal.env gl in
        let sigma = ref (Proofview.Goal.sigma gl) in
        match t with
        | { rec_node = WfRec r } ->
          let inctx, concl = decompose_prod_n_assum !sigma t.rec_args (concl gl) in
          Refine.refine ~typecheck:false (fun sigma ->
              let evd = ref sigma in
              let sort = Sorts.univ_of_sort (Retyping.get_sort_of env sigma concl) in
              let hd, args = decompose_app sigma concl in
              let subst =
                gather_subst env sigma (Retyping.get_type_of env sigma hd) args (List.length ctx)
              in
              let arity, arg, rel =
                let arg = substl (List.rev subst) r.wf_rec_arg in
                let term = (applistc arg (extended_rel_list 0 inctx)) in
                (* Feedback.msg_debug (str"Typing:" ++ Printer.pr_econstr_env (push_rel_context inctx env) sigma term ++
                 *                     str " in context " ++ pr_context env sigma inctx ++ str "subst " ++
                 *                     prlist_with_sep (fun () -> str " ") (Printer.pr_econstr_env env sigma) subst
                 *                    ); *)
                let envsign = push_rel_context inctx env in
                let sigma, arity = Typing.type_of envsign sigma term in
                let ty = Reductionops.nf_all envsign sigma arity in
                let arity =
                  if noccur_between sigma 1 (length inctx) ty then
                    lift (- length inctx) ty
                  else assert false
                in
                arity, arg, r.wf_rec_rel
              in
              let _functional_type, functional_type, fix =
                Covering.wf_fix_constr env evd inctx concl sort arity arg rel
              in
              (* TODO solve WellFounded evar *)
              let sigma, evar = new_evar env !evd functional_type in
              (sigma, mkApp (fix, [| evar |])))
        | { rec_node = StructRec r } ->
          let open Tacticals.New in
          let fixtac =
            let idx = match r.struct_rec_arg with
              | NestedOn None -> Some 0
              | NestedNonRec -> None
              | MutualOn None -> assert false
              | NestedOn (Some (idx, _)) | MutualOn (Some (idx, _)) -> Some idx
            in
            match idx with
            | None -> intros
            | Some idx ->
              let recid = add_suffix p.program_info.program_id "_rec" in
              (* The recursive argument is local to the where, shift it by the
                 length of the enclosing context *)
              equations_debug (fun () -> str"Fixpoint on " ++ int idx ++ str " rec args " ++ int t.rec_args ++
                                         str " lctx " ++ int (List.length lctx));
              let newidx = match unfs with None -> idx | Some _ -> idx in
              observe_new "struct fix" (tclTHENLIST [(* unftac false; *)
                  fix recid (succ newidx);
                  intros
                 (* unftac true *)])
          in fixtac)
      in
      tclTHENLIST [intros;
                   tclDO t.rec_args revert_last;
                   observe_new "wf_fix"
                     (tclTHEN refine
                        (tclTHEN intros (aux chop unfs unfids cs)))]

  and aux chop unfs unfids = function
    | Split ((ctx,pats,_ as lhs), var, _, splits) ->
      let splits = List.map_filter (fun x -> x) (Array.to_list splits) in
      let unfs_splits =
        let unfs = map_opt_split destSplit unfs in
        match unfs with
        | None -> None
        | Some f -> Some (List.map_filter (fun x -> x) (Array.to_list f))
      in
      of82 (observe "split"
        (Tacticals.tclTHEN_i
           (fun gl ->
              match kind (project gl) (pf_concl gl) with
              | App (ind, args) ->
                let pats' = List.drop_last (Array.to_list args) in
                let pats' =
                  if fst chop < 0 then pats'
                  else snd (List.chop (fst chop) pats') in
                let pats, var =
                  match unfs with
                  | Some (Split (ctx, var, _, _)) -> filter_def_pats ctx, var
                  | _ ->
                    filter (fun x -> not (hidden x)) (filter_def_pats lhs), var
                in
                let id = find_splitting_var (project gl) pats var pats' in
                to82 (Depelim.dependent_elim_tac (None, id)) gl
              | _ -> to82 (tclFAIL 0 (str"Unexpected goal in functional induction proof")) gl)
           (fun i gl ->
              let split = nth splits (pred i) in
              let unfsplit = Option.map (fun s -> nth s (pred i)) unfs_splits in
              to82 (aux chop unfsplit unfids split) gl)))

    | Refined ((ctx, _, _), refinfo, s) ->
      let unfs = map_opt_split destRefined unfs in
      let id = pi1 refinfo.refined_obj in
      let elimtac gl =
        let open Proofview.Goal in
        let sigma = sigma gl in
        match kind sigma (concl gl) with
        | App (ind, args) ->
          let before, last_arg = CArray.chop (Array.length args - 1) args in
          let f, fargs = destApp sigma last_arg.(0) in
          let _, pos, elim = 
            find_helper_arg (env gl) sigma info.term_info f fargs 
          in
          let id = Tacmach.New.pf_get_new_id id gl in
          let hyps = Id.Set.elements (hyps_after sigma (hyps gl) (pos + 1 - snd chop) before) in
          let occs = Some (List.map (fun h -> (Locus.AllOccurrences, h), Locus.InHyp) hyps) in
          let occs = Locus.{ onhyps = occs; concl_occs = NoOccurrences } in
          let newconcl =
            let fnapp = change_in_app f fargs pos (mkVar id) in
            let indapp = change_in_app ind before (pos - snd chop) (mkVar id) in
            mkApp (indapp, [| fnapp |])
          in
          Tacticals.New.tclTHENLIST
            [observe_new "letin" (letin_pat_tac true None (Name id) (sigma, elim) occs);
             observe_new "convert concl" (convert_concl ~cast:false ~check:false newconcl DEFAULTcast);
             observe_new "clear body" (clear_body [id]);
             aux chop unfs unfids s]
        | _ ->
          Tacticals.New.tclFAIL 0 (str"Unexpected refinement goal in functional induction proof")
      in
      let open Tacticals.New in
      (observe_new "refine"
              (tclTHENLIST [ intros;
                             tclTHENLAST (tclTHEN (tclTRY (autorewrite_one info.term_info.base_id))
                                cstrtac)
                               (tclSOLVE [Proofview.Goal.enter elimtac]);
                             (solve_ind_rec_tac info.term_info)]))

    | Compute ((lctx,_,_), wheres, _, c) ->
      let unfctx, unfswheres =
        let unfs = map_opt_split destWheres unfs in
        match unfs with
        | None -> [], List.map (fun _ -> None) wheres
        | Some (unfctx, wheres) -> pi1 unfctx, List.map (fun w -> Some w) wheres
      in
      let wheretac =
        if not (List.is_empty wheres) then
          let wheretac env evd s unfs (acc, subst) =
            let wp = s.where_program in
            let revert, ctx, where_term, fstchop, unfids = match unfs with
              | None ->
                let term = where_term s in
                let sign = wp.program_info.program_sign in
                let ctxlen = List.length sign - List.length subst in
                let before, after = List.chop ctxlen sign in
                let newwhere = substl subst term in
                let ctx = subst_rel_context 0 subst before in
                if !Equations_common.debug then
                  Feedback.msg_debug (str" where " ++ str"term: " ++ pr_econstr_env env evd (where_term s) ++
                                      str " subst " ++ prlist_with_sep spc (Printer.pr_econstr_env env evd) subst ++
                                      str " final term " ++ pr_econstr_env env evd newwhere ++
                                      str "context " ++ pr_context env evd sign);
                0, ctx, newwhere, fst chop (* + List.length ctx *), unfids
              | Some w ->
                let assoc, unf, split =
                  try PathMap.find w.where_path info.wheremap
                  with Not_found -> assert false
                in
                if !Equations_common.debug then
                  Feedback.msg_debug (str"Unfolded where " ++ str"term: " ++ pr_econstr_env env evd (where_term w) ++
                                      str" type: " ++ pr_econstr_env env evd w.where_type ++ str" assoc " ++
                                      pr_econstr_env env evd assoc);
                let unfwp = w.where_program in
                let ctxlen = List.length unfwp.program_info.program_sign - List.length unfctx in
                let before, after = List.chop ctxlen unfwp.program_info.program_sign in
                let subst =
                  if not (List.length subst >= List.length after) then
                    anomaly (str"Mismatch between hypotheses in named context and program")
                  else subst
                in
                let newwhere = substl subst (where_term w) in
                let ctx = subst_rel_context 0 subst before in
                if !Equations_common.debug then
                  Feedback.msg_debug (str"Unfolded where substitution:  " ++
                                      prlist_with_sep spc (Printer.pr_econstr_env env evd) subst ++
                                      str"New where term" ++ Printer.pr_econstr_env env evd newwhere ++
                                      str" context map " ++ pr_context env Evd.empty ctx);
                0, ctx, newwhere, -1 (* + List.length ctx *), unf :: unfids
            in
            let chop = fstchop, snd chop in
            let wheretac =
              let open Tacticals.New in
              observe_new "one where"
                (tclTHENLIST [
                    tclDO revert revert_last;
                    observe_new "moving section id" (tclTRY (move_hyp coq_end_of_section_id Logic.MoveLast));
                    (aux_program lctx chop (Option.map (fun s -> s.where_program) unfs)
                             unfids (Some s.where_program_orig) s.where_program)])
            in
            let wherepath, _args =
              try PathMap.find s.where_path info.pathmap
              with Not_found ->
                error "Couldn't find associated args of where"
            in
            if !debug then
              (let env = Global.env () in
               Feedback.msg_debug
                 (str"Found path " ++ str (Id.to_string wherepath) ++ str" where: " ++
                  pr_id (where_id s) ++ str"term: " ++
                  Printer.pr_econstr_env env Evd.empty where_term ++
                  str" context map " ++
                  pr_context_map env Evd.empty (id_subst ctx)));
            let ind = Nametab.locate (qualid_of_ident wherepath) in
            let ty ind =
              let hd, args = decompose_app Evd.empty where_term in
              let indargs = List.filter (fun x -> isVar Evd.empty x) args in
              let rels = extended_rel_list 0 ctx in
              let indargs = List.append indargs rels in
              let app = applistc ind (List.append indargs [applistc where_term rels]) in
              it_mkProd_or_LetIn app ctx
            in
            let tac =
              Tacticals.New.tclTHEN acc
                (Proofview.tclBIND (Tacticals.New.pf_constr_of_global ind)
                   (fun ind ->
                      if !debug then
                        (let env = Global.env () in
                         Feedback.msg_debug
                           (str"Type of induction principle for " ++ str (Id.to_string (where_id s)) ++ str": " ++
                            Printer.pr_econstr_env env Evd.empty (ty ind)));
                      assert_by (Name (where_id s)) (ty ind) wheretac))
            in (tac, where_term :: subst)
          in
          let () = assert (List.length wheres = List.length unfswheres) in
          let tac =
            Proofview.Goal.enter (fun gl ->
                let env = Proofview.Goal.env gl in
                let sigma = Proofview.Goal.sigma gl in
                let subst =
                  let concl = Proofview.Goal.concl gl in
                  let hd, args = decompose_app sigma concl in
                  let args = drop_last args in
                  let rec collect_vars acc c =
                    let hd, args = decompose_app sigma c in
                    match kind sigma hd with
                    | Var id -> if not (List.mem id acc) then id :: acc else acc
                    | Construct _ -> List.fold_left collect_vars acc args
                    | _ -> acc
                  in
                  let args_vars = List.fold_left collect_vars [] args in
                  let args_vars = List.filter (fun id -> not (Termops.is_section_variable (Global.env ()) id)) args_vars in
                  List.map mkVar args_vars
                in
                let tac, _ = List.fold_right2 (wheretac env sigma) wheres unfswheres (Tacticals.New.tclIDTAC, subst) in
                tac)
          in
          Tacticals.New.tclTHENLIST [tac; Tacticals.New.tclTRY (autorewrite_one info.term_info.base_id)]
        else Tacticals.New.tclIDTAC
      in
      (match c with
       | REmpty _ ->
         observe_new "compute empty"
           (tclTHENLIST [intros_reducing (); wheretac; find_empty_tac ()])
       | RProgram _ ->
         observe_new "compute "
           (tclTHENLIST
              [intros_reducing ();
               tclTRY (autorewrite_one info.term_info.base_id);
               observe_new "wheretac" wheretac;
               observe_new "applying compute rule" cstrtac;
               (* Each of the recursive calls result in an assumption. If it
                   is a rec call in a where clause to itself we need to
                   explicitely rewrite with the unfolding lemma (as the where
                   clause induction hypothesis is about the unfolding whereas
                   the term itself might mentions the original function. *)
               tclTHEN Tactics.intros
                 (tclMAP (fun i ->
                      (tclTRY (Proofview.tclBIND
                              (Tacticals.New.pf_constr_of_global
                                  (Equations_common.global_reference i))
                                Equality.rewriteLR))) unfids);
               tclORELSE (tclCOMPLETE
                (observe_new "solving premises of compute rule" (solve_ind_rec_tac info.term_info)))
                (observe_new "solving nested recursive call" (solve_nested ()))]))

    | Mapping (_, s) -> aux chop unfs unfids s
  in aux_program [] chop unfp unfids None p

let observe_tac s tac =
  let open Proofview in
  let open Proofview.Notations in
  if not !debug then tac
  else
    tclENV >>= fun env ->
    tclEVARMAP >>= fun sigma ->
    Unsafe.tclGETGOALS >>= fun gls ->
    let gls = List.map Proofview.drop_state gls in
    Feedback.msg_debug (str"Applying " ++ str s ++ str " on " ++
                          Printer.pr_subgoals None sigma ~seeds:[] ~shelf:[] ~stack:[] ~unfocused:[] ~goals:gls);
    Proofview.tclORELSE
      (Proofview.tclTHEN tac
                         (Proofview.numgoals >>= fun gls ->
                          if gls = 0 then (Feedback.msg_debug (str s ++ str "succeeded");
                                           Proofview.tclUNIT ())
             else
               (of82
                  (fun gls -> Feedback.msg_debug (str "Subgoal: " ++ Printer.pr_goal gls);
                           Evd.{ it = [gls.it]; sigma = gls.sigma }))))
      (fun iexn -> Feedback.msg_debug
                     (str"Failed with: " ++
                        (match fst iexn with
                         | Tacticals.FailError (n,expl) ->
                            (str" Fail error " ++ int n ++ str " for " ++ str s ++
                               spc () ++ Lazy.force expl ++
                               str " on " ++
                             Printer.pr_subgoals None sigma ~seeds:[] ~shelf:[] ~stack:[] ~unfocused:[] ~goals:gls)
                         | _ -> CErrors.iprint iexn));
                   Proofview.tclUNIT ())

exception NotGuarded

let check_guard tac =
  let open Proofview in
  let open Notations in
  Unsafe.tclGETGOALS >>= (fun gls ->
  tac >>= (fun () ->
  tclENV >>= fun env ->
  tclEVARMAP >>= (fun sigma ->
    if check_guard gls env sigma then tclUNIT ()
    else tclZERO NotGuarded)))

let ind_fun_tac is_rec f info fid nestedinfo progs =
  let open Tacticals.New in
  let open Proofview in
  let open Notations in
  match is_rec with
  | Some (Guarded l) :: context ->
     let mutual, nested = List.partition (function (_, MutualOn _) -> true | _ -> false) l in
     let mutannots = List.map (function (_, MutualOn (Some (ann, _))) -> ann + 1 | _ -> -1) mutual in
     let mutprogs, nestedprogs =
       List.partition (fun (p,_,_,e) -> match p.program_info.Syntax.program_rec with
                                      | Some (Structural (MutualOn _)) -> true
                                      | _ -> false) progs
     in
     let eauto = Class_tactics.typeclasses_eauto ["funelim"; info.term_info.base_id] in
     let rec splits l =
       match l with
       | [] | _ :: [] -> tclUNIT ()
       | _ :: l -> Tactics.split Tactypes.NoBindings <*> tclDISPATCH [tclUNIT (); splits l]
     in
     let prove_progs progs =
       intros <*>
       tclDISPATCH (List.map (fun (p,_unfp,cpi,e) ->
                    (* observe_tac "proving one mutual " *)
                    let proginfo =
                      { info with term_info = { info.term_info
                                                with helpers_info =
                                                       info.term_info.helpers_info @
                                                       cpi.program_split_info.helpers_info } }
                    in
                    (aux_ind_fun proginfo (0, List.length l) nestedinfo None []
                             { p with program_rec = None }))
                    progs)
     in
     let prove_nested =
       tclDISPATCH
         (List.map (function (id,NestedOn (Some (ann,_))) -> fix id (ann + 1)
                           | (id,NestedOn None) -> fix id 1
                         | _ -> tclUNIT ()) nested) <*>
         prove_progs nestedprogs
     in
     let try_induction () =
       match mutannots with
       | [n] ->
         (* Try using regular induction instead *)
         let _ =
           if !Equations_common.debug then
             Feedback.msg_debug
               (str "Proof of mutual induction principle is not guarded, trying induction")
         in
         let splits =
           match progs with
           | [(p, _, _, e)] ->
             (match p.program_splitting with
              | Split (_, _, _, splits) ->
                Some (p, CList.map_filter (fun x -> x) (Array.to_list splits))
              | _ -> None)
           | _ -> None
         in
         (match splits with
         | Some (p, s) ->
           observe_new "induction"
             (tclDISPATCH
                [tclDO n intro <*>
                 observe_new "induction on last var"
                   (onLastDecl (fun decl ->
                        Equations_common.depind_tac (Context.Named.Declaration.get_id decl) <*>
                        intros <*>
                        specialize_mutfix_tac () <*>
                        tclDISPATCH (List.map (fun split ->
                            aux_ind_fun info (0, 1) nestedinfo None []
                              { p with program_rec = None;
                                program_splitting = split }) s)))])
         | None -> tclZERO NotGuarded)
       | _ -> tclZERO NotGuarded
     in
     let mutfix =
       let tac = mutual_fix [] mutannots <*> specialize_mutfix_tac () <*> prove_progs mutprogs in
       tclORELSE (if List.length nested > 0 then tac else check_guard tac)
         (fun (e, einfo) ->
           match e with
           | NotGuarded ->
             tclORELSE (check_guard (try_induction ())) (fun (e, einfo) ->
                 match e with
                 | NotGuarded ->
                   Feedback.msg_info (str "Proof of mutual induction principle is not guarded " ++
                                       str"and cannot be proven by induction");
                   tclIDTAC
                 | _ -> tclZERO ~info:einfo e)
           | _ -> tclZERO ~info:einfo e)
     in
     let mutlen = List.length mutprogs in
     let tac gl =
       let mutprops, nestedprops =
         let rec aux concl i =
           match kind (Goal.sigma gl) concl with
             | App (conj, [| a; b |]) ->
                if i == 1 then
                  a, Some b
                else
                  let muts, nested = aux b (pred i) in
                  mkApp (conj, [| a ; muts |]), nested
             | _ -> if i == 1 then concl, None
                    else assert false
         in aux (Goal.concl gl) mutlen
       in
       set_eos_tac () <*>
         (match nestedprops with
          | Some p ->
             assert_before Anonymous (mkProd (anonR, mutprops, p)) <*>
               tclDISPATCH
                 [observe_tac "assert mut -> nest first subgoal " (* observe_tac *)
                  (*   "proving mut -> nested" *)
                              (intro <*> observe_tac "splitting nested" (splits nestedprogs) <*> prove_nested);
                  tclUNIT ()]
          | None -> tclUNIT ()) <*>
         assert_before Anonymous mutprops <*>
         tclDISPATCH
           [observe_tac "mutfix"
               (splits mutprogs <*> tclFOCUS 1 (List.length mutual) mutfix);
            tclUNIT ()] <*>
         (* On the rest of the goals, do the nested proofs *)
         observe_tac "after mut -> nested and mut provable" (eauto ~depth:None)
     in Proofview.Goal.enter (fun gl -> tac gl)

  | _ ->
    let helpercsts = List.map (fun (cst, i) -> cst) info.term_info.helpers_info in
    let opacify, transp =
      simpl_of (List.map (fun x -> x, Conv_oracle.Expand)
                  (fst (Constr.destConst f) :: helpercsts))
    in
    let p, unfp =
      match progs with
      | [p, unfp, cpi, ei] -> p, unfp
      | _ -> assert false
    in
    opacify ();
    let tac =
      Proofview.tclBIND
        (tclCOMPLETE (tclTHENLIST
                        [set_eos_tac (); intros;
                         aux_ind_fun info (0, 0) nestedinfo unfp [] p]))
        (fun r -> transp (); Proofview.tclUNIT r)
    in
    tclORELSE (check_guard tac)
      (fun (e, einfo) ->
         match e with
         | NotGuarded ->
           Feedback.msg_info (str "Proof of mutual induction principle is not guarded " ++
                              str" and cannot be proven by induction. Consider switching to well-founded recursion.");
           tclUNIT ()
         | _ -> tclZERO ~info:einfo e)

let ind_fun_tac is_rec f info fid nested progs =
  Proofview.tclORELSE (ind_fun_tac is_rec f info fid nested progs)
    (fun e ->
       match fst e with
       | Pretype_errors.PretypeError (env, evd, err) ->
         Feedback.msg_warning (Himsg.explain_pretype_error env evd err); 
        Exninfo.iraise e
       | _ -> Exninfo.iraise e)

let is_primitive env evd ctx var =
  let decl = List.nth ctx var in
  let indf, _ = find_rectype env evd (Context.Rel.Declaration.get_type decl) in
  let (ind,_), _ = dest_ind_family indf in
  let mspec = Inductive.lookup_mind_specif env ind in
  Inductive.is_primitive_record mspec

let myreplace_by a1 a2 tac =
  let open Proofview.Notations in
  Proofview.Goal.enter (fun gl ->
      let env = Proofview.Goal.env gl in
      let sigma = Proofview.Goal.sigma gl in
      if eq_constr sigma a1 a2 then Proofview.tclUNIT () else
        let ty = Retyping.get_type_of env sigma a1 in
        let sigma, eq = get_fresh sigma logic_eq_type in
        let eqty = mkApp (eq, [| ty; a1; a2 |]) in
        let sigma, _ = Typing.type_of env sigma eqty in
        let na = Tacmach.New.pf_get_new_id (Id.of_string "Heq") gl in
        Proofview.Unsafe.tclEVARS sigma <*>
        Tactics.assert_by (Name na) eqty tac <*>
        Equality.rewriteLR (mkVar na) <*>
        Tactics.clear [na])

let headcst sigma f =
  let f, _ = decompose_app sigma f in
  if isConst sigma f then fst (destConst sigma f)
  else assert false

let prove_unfolding_lemma info where_map f_cst funf_cst p unfp gl =
  let depelim h = Depelim.dependent_elim_tac (None, h) (* depelim_tac h *) in
  let helpercsts = List.map (fun (cst, i) -> cst) info.helpers_info in
  let opacify, transp = simpl_of ((destConstRef (Lazy.force coq_hidebody), Conv_oracle.transparent)
    :: List.map (fun x -> x, Conv_oracle.Expand) (f_cst :: funf_cst :: helpercsts)) in
  let opacified tac gl = opacify (); let res = tac gl in transp (); res in
  let transparent tac gl = transp (); let res = tac gl in opacify (); res in
  let simpltac gl = opacified (to82 (simpl_equations_tac ())) gl in
  let my_simpl = opacified (to82 (simpl_in_concl)) in
  let unfolds base base' =
    tclTHEN (autounfold_heads [base] [base'] None)
    (to82 (Tactics.reduct_in_concl ~cast:false ~check:false ((Reductionops.clos_norm_flags CClosure.betazeta), DEFAULTcast)))
  in
  let solve_rec_eq subst gl =
    match kind (project gl) (pf_concl gl) with
    | App (eq, [| ty; x; y |]) ->
       let sigma = project gl in
       let xf, _ = decompose_app sigma x and yf, _ = decompose_app sigma y in
       (try
          let f_cst, funf_cst =
            List.find (fun (f_cst, funf_cst) ->
                is_global sigma (GlobRef.ConstRef f_cst) xf && is_global sigma (GlobRef.ConstRef funf_cst) yf) subst
          in
          let unfolds = unfold_in_concl
	      [((Locus.OnlyOccurrences [1]), Tacred.EvalConstRef f_cst); 
               ((Locus.OnlyOccurrences [1]), Tacred.EvalConstRef funf_cst)]
          in tclTHENLIST [to82 unfolds; simpltac; to82 (pi_tac ())] gl
        with Not_found -> to82 (Tacticals.New.tclORELSE reflexivity (congruence_tac 10 [])) gl)
    | _ -> to82 reflexivity gl
  in
  let solve_eq subst = observe "solve_eq" (tclORELSE (transparent (to82 reflexivity)) (solve_rec_eq subst)) in
  let abstract tac = (* Abstract.tclABSTRACT None *) tac in
  let rec aux_program subst p unfp =
    Proofview.Goal.enter (fun gl ->
        let sigma = Proofview.Goal.sigma gl in
        let f_cst = headcst sigma p.program_term
        and funf_cst = headcst sigma unfp.program_term in
        let unfolds =
          tclTHENLIST
            [to82 (unfold_in_concl
                     [Locus.OnlyOccurrences [1], Tacred.EvalConstRef f_cst;
                      (Locus.OnlyOccurrences [1], Tacred.EvalConstRef funf_cst)]);
             my_simpl]
        in
        let set_opaque () =
          Global.set_strategy (ConstKey f_cst) Conv_oracle.Opaque;
          Global.set_strategy (ConstKey funf_cst) Conv_oracle.Opaque;
        in
        let subst, fixtac, extgl =
          match p.program_rec with
          | Some r ->
            let open Tacticals.New in
            let fixtac, extgl = match r with
              | { rec_node = WfRec _ } ->
                if !Equations_common.equations_with_funext then
                  tclTHENLIST [of82 unfolds; unfold_recursor_ext_tac ()], false
                else
                  tclTHENLIST [of82 unfolds; unfold_recursor_tac ()], true
              | { rec_node = StructRec sr } ->
                match annot_of_rec sr with
                | Some annot ->
                  tclTHENLIST [tclDO r.rec_args revert_last;
                               observe_new "mutfix" (mutual_fix [] [annot]);
                               tclDO r.rec_args intro; of82 unfolds], false
                | None -> Proofview.tclUNIT (), false
            in ((f_cst, funf_cst) :: subst), fixtac, extgl
          | _ -> subst, of82 unfolds, false
        in
        Tacticals.New.tclTHENLIST 
          [observe_new "program before unfold"  intros;
           if extgl then
            (Tacticals.New.tclTHENFIRST 
              (observe_new "program fixpoint" fixtac)
              (Tacticals.New.tclORELSE 
                (Tacticals.New.tclSOLVE
                  [of82 (fun gl -> set_opaque ();
                    observe "extensionality proof"
                    (aux subst info.base_id info.base_id p.program_splitting p.program_splitting) gl)])
                (Tacticals.New.tclFAIL 0 
                  (Pp.str "Could not prove extensionality automatically"))))
            else observe_new "program fixpoint" fixtac;
            (of82 (fun gl -> set_opaque ();
              (observe "program"
                (aux subst info.base_id (info.base_id ^ "_unfold") p.program_splitting unfp.program_splitting)) gl))])

  and aux subst base unfold_base split unfold_split =
    match split, unfold_split with
    | Split (_, _, _, splits), Split ((ctx,pats,_), var, _, unfsplits) ->
      observe "split"
        (fun gl ->
        if is_primitive (pf_env gl) (project gl) ctx (pred var) then
          aux subst base unfold_base (Option.get (Array.hd splits)) (Option.get (Array.hd unfsplits)) gl
        else
          match kind (project gl) (pf_concl gl) with
          | App (eq, [| ty; x; y |]) ->
            let sigma = project gl in
            let f, pats' = decompose_app sigma y in
            let c, unfolds =
              let _, _, _, _, _, c, _ = destCase sigma f in
              c, tclIDTAC
            in
            let id = destVar sigma (fst (decompose_app sigma c)) in
            let splits = List.map_filter (fun x -> x) (Array.to_list splits) in
            let unfsplits = List.map_filter (fun x -> x) (Array.to_list unfsplits) in
	            to82 (abstract (of82 (tclTHEN_i (to82 (depelim id))
				               (fun i -> let split = nth splits (pred i) in
                                 let unfsplit = nth unfsplits (pred i) in
                                 tclTHENLIST [unfolds; simpltac;
                                    aux subst base unfold_base split unfsplit])))) gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding goal") gl)

    | _, Mapping (lhs, s) -> aux subst base unfold_base split s
       
    | Refined (_, _, s), Refined ((ctx, _, _), refinfo, unfs) ->
	      let id = pi1 refinfo.refined_obj in
        let rec reftac gl =
          match kind (project gl) (pf_concl gl) with
          | App (f, [| ty; term1; term2 |]) ->
             let sigma = project gl in
             let cst, _ = destConst sigma (fst (decompose_app sigma refinfo.refined_term)) in
             let f1, arg1 = destApp sigma term1 and f2, arg2 = destApp sigma term2 in
             let _, posa1, a1 = find_helper_arg (pf_env gl) sigma info f1 arg1
             and ev2, posa2, a2 = find_helper_arg (pf_env gl) sigma info f2 arg2 in
             let id = pf_get_new_id id gl in
             if Environ.QConstant.equal (pf_env gl) ev2 cst then
               tclTHENLIST
               [to82 (myreplace_by a1 a2 (of82 (tclTHENLIST [solve_eq subst])));
                observe "refine after replace"
                  (to82 (letin_tac None (Name id) a2 None Locusops.allHypsAndConcl));
                Proofview.V82.of_tactic (clear_body [id]); 
                observe "unfoldings" (unfolds base unfold_base); 
                aux subst base unfold_base s unfs] gl
             else tclTHENLIST [unfolds base unfold_base; simpltac; reftac] gl
          | _ -> tclFAIL 0 (str"Unexpected unfolding lemma goal") gl
    	in
      let reftac = observe "refined" reftac in
	      to82 (abstract (of82 (tclTHENLIST [to82 intros; simpltac; reftac])))
	    
    | Compute (_, wheres, _, RProgram _), Compute ((lctx, _, _), unfwheres, _, RProgram c) ->
      let open Tacticals.New in
      let open Tacmach.New in
       let wheretac acc w unfw =
         let assoc, id, _ =
           try PathMap.find unfw.where_path where_map
           with Not_found -> assert false
         in
        Proofview.Goal.enter (fun gl ->
         let env = pf_env gl in
         let evd = ref (project gl) in
         let wp = w.where_program in
         let unfwp = unfw.where_program in
         (* let () = Feedback.msg_debug (str"Unfold where assoc: " ++
          *                              Printer.pr_econstr_env env !evd assoc) in
          * let () = Feedback.msg_debug (str"Unfold where problem: " ++
          *                              pr_context_map env !evd wp.program_prob) in
          * let () = Feedback.msg_debug (str"Unfold where problem: " ++
          *                              pr_context_map env !evd unfwp.program_prob) in *)
         let ty =
           let ctx = unfwp.program_info.program_sign in
           let len = List.length ctx - List.length lctx in
           let newctx, oldctx = List.chop len ctx in
           let lhs = mkApp (lift len assoc, extended_rel_vect 0 newctx) in
           let rhs = mkApp (unfwp.program_term, extended_rel_vect 0 ctx) in
           let eq = mkEq env evd unfwp.program_info.program_arity lhs rhs in
           it_mkProd_or_LetIn eq ctx
         in
         (* let _ = Typing.type_of env !evd ty in *)
         let progtac = aux_program subst wp unfwp in
         let tac =
           assert_by (Name id) ty
             (tclTHEN (keep [])
                      (Abstract.tclABSTRACT (Some id) progtac))
         in
         tclTHENLIST [Proofview.Unsafe.tclEVARS !evd; tac;
                      Equality.rewriteLR (mkVar id);
                      acc])
       in
       let wheretacs =
         assert(List.length wheres = List.length unfwheres);
         List.fold_left2 wheretac tclIDTAC wheres unfwheres
       in
       to82 (observe_new "compute"
         (tclTHENLIST [intros; wheretacs;
                       observe_new "compute rhs" (tclTRY (of82 (unfolds base unfold_base)));
                       of82 simpltac; of82 (solve_eq subst)]))

    | Compute (_, _, _, _), Compute ((ctx,_,_), _, _, REmpty (id, sp)) ->
      let d = nth ctx (pred id) in
      let id = Name.get_id (get_name d) in
      to82 (abstract (depelim id))

    | _, _ -> assert false
  in
    try
      let res =
        tclTHENLIST
          [to82 (set_eos_tac ()); to82 intros;
           to82 (aux_program [f_cst, funf_cst] p unfp)] gl
      in transp (); res
    with e -> transp (); raise e
  
let prove_unfolding_lemma info where_map f_cst funf_cst p unfp gl =
  let () =
    if !Equations_common.debug then
      let open Pp in
      let msg = Feedback.msg_debug in
      let env = pf_env gl in
      let evd = project gl in
      msg (str"Proving unfolding lemma of: ");
      msg (pr_splitting ~verbose:true env evd p.program_splitting);
      msg (fnl () ++ str"and of: " ++ fnl ());
      msg (pr_splitting ~verbose:true env evd unfp.program_splitting)
  in
  try prove_unfolding_lemma info where_map f_cst funf_cst p unfp gl
  with (Nametab.GlobalizationError e) as exn ->
    raise exn

(* let rec mk_app_holes env sigma = function *)
(* | [] -> (sigma, []) *)
(* | decl :: rem -> *)
(*   let (sigma, arg) = Evarutil.new_evar env sigma (Context.Rel.Declaration.get_type decl) in *)
(*   let (sigma, rem) = mk_app_holes env sigma (subst_rel_context 0 [arg] rem) in *)
(*   (sigma, arg :: rem) *)

let ind_elim_tac indid inds mutinds info ind_fun =
  let open Proofview in
  let open Notations in
  let open Tacticals.New in
  let eauto = Class_tactics.typeclasses_eauto ["funelim"; info.base_id] in
  let prove_methods c =
    Proofview.Goal.enter (fun gl ->
        let sigma, _ = Typing.type_of (Goal.env gl) (Goal.sigma gl) c in
        observe_new "prove_methods" (
        tclTHENLIST [Proofview.Unsafe.tclEVARS sigma;
                     observe_new "apply eliminator" (Tactics.apply c);
                     Tactics.simpl_in_concl;
                     observe_new "solve methods" (eauto ~depth:None)]))
  in
  let rec applyind leninds args =
    Proofview.Goal.enter (fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    match leninds, kind sigma (Goal.concl gl) with
    | 0, _ ->
      let app = applistc indid (List.rev args) in
      let sigma, ty = Typing.type_of env sigma app in
       if mutinds == 1 then
         tclTHENLIST [Proofview.Unsafe.tclEVARS sigma;
                      Tactics.simpl_in_concl; Tactics.intros;
                      prove_methods (Reductionops.nf_beta env sigma app)]
       else
         let ctx, concl = decompose_prod_assum sigma ty in
         Proofview.Unsafe.tclEVARS sigma <*>
         Tactics.simpl_in_concl <*> Tactics.intros <*>
         Tactics.cut concl <*>
         tclDISPATCH
           [tclONCE (Tactics.intro <*>
                     (pf_constr_of_global ind_fun >>= Tactics.pose_proof Anonymous <*>
                                                      eauto ~depth:None));
            tclONCE (Tactics.apply app <*> Tactics.simpl_in_concl <*> eauto ~depth:None)]

    | _, LetIn (_, b, _, t') ->
       tclTHENLIST [Tactics.convert_concl ~cast:false ~check:false (subst1 b t') DEFAULTcast;
                    applyind (pred leninds) (b :: args)]
    | _, Prod (_, _, t') ->
        tclTHENLIST [Tactics.intro;
                     onLastHypId (fun id -> applyind (pred leninds) (mkVar id :: args))]
    | _, _ -> assert false)
  in
  try observe_new "applyind" (applyind inds [])
  with e -> tclFAIL 0 (Pp.str"exception")
