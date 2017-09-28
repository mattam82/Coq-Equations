open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Vars
open Globnames
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type
open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Entries
open Constrexpr
open Vars
open Tacexpr
open Tactics
open Tacticals
open Tacmach
open Context
open Evd
open Evarutil
open Evar_kinds
open Equations_common
open Depelim
open Printer
open Ppconstr
open Decl_kinds
open Constrintern

open Syntax
open Covering
open Splitting


module PathOT =
  struct
    type t = Covering.path
    let rec compare p p' =
      match p, p' with
      | ev :: p, ev' :: p' ->
         let c = Evar.compare ev ev' in
         if c == 0 then compare p p'
         else c
      | _ :: _, [] -> -1
      | [], _ :: _ -> 1
      | [], [] -> 0
  end

module PathMap = struct

  include Map.Make (PathOT)

  let union f = merge (fun k l r ->
                  match l, r with
                  | Some l, Some r -> f k l r
                  | Some _, _ -> l
                  | _, Some _ -> r
                  | _, _ -> l)
end

type where_map = (constr * Names.Id.t * splitting) Evar.Map.t

type ind_info = {
  term_info : term_info;
  pathmap : (Names.Id.t * Constr.t list) PathMap.t; (* path -> inductive name *)
  wheremap : where_map }

   
let find_helper_info info f =
  try List.find (fun (ev', arg', id') ->
	 Globnames.eq_gr (Nametab.locate (qualid_of_ident id')) (global_of_constr f))
	info.helpers_info
  with Not_found -> anomaly (str"Helper not found while proving induction lemma.")

let below_transparent_state () =
  Hints.Hint_db.transparent_state (Hints.searchtable_map "Below")

let simpl_star = 
  tclTHEN (to82 simpl_in_concl) (onAllHyps (fun id -> to82 (simpl_in_hyp (id, Locus.InHyp))))

let eauto_with_below ?depth l =
  to82 (Class_tactics.typeclasses_eauto ~depth
    ~st:(below_transparent_state ()) (l@["subterm_relation"; "Below"; "rec_decision"]))

let wf_obligations_base info =
  info.base_id ^ "_wf_obligations"

let simp_eqns l =
  tclREPEAT (tclTHENLIST [Proofview.V82.of_tactic 
			     (Autorewrite.autorewrite (Tacticals.New.tclIDTAC) l);
			  (* simpl_star; Autorewrite.autorewrite tclIDTAC l; *)
			  tclTRY (eauto_with_below l)])

let simp_eqns_in clause l =
  tclREPEAT (tclTHENLIST 
		[Proofview.V82.of_tactic
		    (Autorewrite.auto_multi_rewrite l clause);
		 tclTRY (eauto_with_below l)])

let autorewrites b = 
  tclREPEAT (Proofview.V82.of_tactic (Autorewrite.autorewrite Tacticals.New.tclIDTAC [b]))

let autorewrite_one b =
  let rew_rules = Autorewrite.find_rewrites b in
  let rec aux rules =
    match rules with
    | [] -> Tacticals.New.tclFAIL 0 (str"Couldn't rewrite")
    | r :: rules ->
       let global = global_of_constr r.Autorewrite.rew_lemma in
       let tac = Tacticals.New.pf_constr_of_global global
          (if r.Autorewrite.rew_l2r then Equality.rewriteLR else Equality.rewriteRL)
       in
       Proofview.tclOR
         (if !debug then
            (Proofview.Goal.nf_enter
               Proofview.Goal.{
               enter = fun gl -> let concl = Proofview.Goal.concl gl in
                                 Feedback.msg_debug (str"Trying " ++ pr_global global ++ str " on " ++
                                                       pr_constr concl);
                                 tac })
          else tac)
         (fun e -> if !debug then Feedback.msg_debug (str"failed"); aux rules)
  in Proofview.V82.of_tactic (aux rew_rules)
                  
let find_helper_arg info f args =
  let (ev, arg, id) = find_helper_info info f in
    ev, args.(arg)
      
let find_splitting_var pats var constrs =
  let rec find_pat_var p c =
    match p, decompose_app c with
    | PRel i, (c, l) when i = var -> Some (destVar c)
    | PCstr (c, ps), (f,l) -> aux ps l
    | _, _ -> None
  and aux pats constrs =
    List.fold_left2 (fun acc p c ->
      match acc with None -> find_pat_var p c | _ -> acc)
      None pats constrs
  in
    Option.get (aux (rev pats) constrs)

let rec intros_reducing gl =
  let concl = pf_concl gl in
    match kind_of_term concl with
    | LetIn (_, _, _, _) -> tclTHEN (to82 hnf_in_concl) intros_reducing gl
    | Prod (_, _, _) -> tclTHEN (to82 intro) intros_reducing gl
    | _ -> tclIDTAC gl
  
let cstrtac info =
  tclTHENLIST [to82 (any_constructor false None)]

let destSplit = function
  | Split (_, _, _, splits) -> Some splits
  | _ -> None

let destRefined = function
  | Refined (_, _, s) -> Some s
  | _ -> None

let destWheres = function
  | Compute (_, wheres, _, _) -> Some wheres
  | _ -> None

let map_opt_split f s =
  match s with
  | None -> None
  | Some s -> f s

let solve_ind_rec_tac info =
  Tacticals.New.pf_constr_of_global info.term_id (fun c ->
  Proofview.tclTHEN (Tactics.pose_proof Anonymous c)
                    (of82 (eauto_with_below ~depth:10 [info.base_id; wf_obligations_base info])))

let rec aux_ind_fun info chop unfs unfids = function
  | Split ((ctx,pats,_), var, _, splits) ->
     let unfs =
       let unfs = map_opt_split destSplit unfs in
       match unfs with
       | None -> fun i -> None
       | Some f -> fun i -> f.(i)
     in
     observe "split"
     (tclTHEN_i
       (fun gl ->
	match kind_of_term (pf_concl gl) with
	| App (ind, args) -> 
	   let pats' = List.drop_last (Array.to_list args) in
           let pats' = 
             if chop < 0 then pats'
             else snd (List.chop chop pats') in
	   let pats = filter (fun x -> not (hidden x)) pats in
	   let id = find_splitting_var pats var pats' in
	      to82 (depelim_nosimpl_tac id) gl
	| _ -> tclFAIL 0 (str"Unexpected goal in functional induction proof") gl)
	(fun i -> 
	  match splits.(pred i) with
	  | None -> to82 (simpl_dep_elim_tac ())
	  | Some s ->
	      tclTHEN (to82 (simpl_dep_elim_tac ()))
		(aux_ind_fun info chop (unfs (pred i)) unfids s)))
	  
  | Valid ((ctx, _, _), ty, substc, tac, valid, rest) ->
     observe "valid"
    (tclTHEN (to82 intros)
      (tclTHEN_i tac (fun i -> let _, _, subst, invsubst, split = nth rest (pred i) in
				 tclTHEN (to82 (Lazy.force unfold_add_pattern))
				   (aux_ind_fun info chop unfs unfids split))))

  | RecValid (id, cs) -> aux_ind_fun info chop unfs unfids cs
      
  | Refined ((ctx, _, _), refinfo, s) -> 
    let unfs = map_opt_split destRefined unfs in
    let id = pi1 refinfo.refined_obj in
    let elimtac gl =
      match kind_of_term (pf_concl gl) with
      | App (ind, args) ->
	 let last_arg = args.(Array.length args - 1) in
	 let f, args = destApp last_arg in
	 let _, elim = find_helper_arg info.term_info f args in
	 let id = pf_get_new_id id gl in
	 tclTHENLIST
	 [to82 (letin_tac None (Name id) elim None Locusops.allHypsAndConcl); 
	  Proofview.V82.of_tactic (clear_body [id]); aux_ind_fun info chop unfs unfids s] gl
      | _ -> tclFAIL 0 (str"Unexpected refinement goal in functional induction proof") gl
    in
    observe "refine"
    (tclTHENLIST [ to82 intros;
                   tclTHENLAST (tclTHEN (tclTRY (autorewrite_one info.term_info.base_id))
                                        (cstrtac info.term_info)) (tclSOLVE [elimtac]);
		   to82 (solve_ind_rec_tac info.term_info)])

  | Compute (_, wheres, _, c) ->
    let unfswheres =
      let unfs = map_opt_split destWheres unfs in
      match unfs with
      | None -> List.map (fun _ -> None) wheres
      | Some wheres -> List.map (fun w -> Some w) wheres
    in
    let wheretac = 
      if not (List.is_empty wheres) then
        let wheretac acc s unfs =
          let where_term, chop, unfids, where_nctx = match unfs with
            | None -> s.where_term, chop + List.length s.where_nctx, unfids, s.where_nctx
            | Some w ->
               let assoc, unf, split =
                 try Evar.Map.find (List.hd w.where_path) info.wheremap
                 with Not_found -> assert false
               in
               (* msg_debug (str"Unfolded where " ++ str"term: " ++ pr_constr w.where_term ++ *)
               (*              str" type: " ++ pr_constr w.where_type ++ str" assoc " ++ *)
               (*              pr_constr assoc); *)
               assoc, chop + List.length w.where_nctx, unf :: unfids, w.where_nctx
          in
          let wheretac =
            observe "one where"
            (tclTHENLIST [tclTRY (to82 (move_hyp coq_end_of_section_id Misctypes.MoveLast));
                         to82 intros;
                         if Option.is_empty unfs then tclIDTAC
                         else autorewrite_one (info.term_info.base_id ^ "_where");
                         (aux_ind_fun info chop (Option.map (fun s -> s.where_splitting) unfs)
                                      unfids s.where_splitting)])
          in
          let wherepath, args =
            try PathMap.find s.where_path info.pathmap
            with Not_found ->
              error "Couldn't find associated args of where"
          in
          if !debug then
            Feedback.msg_debug (str"Found path " ++ str (Id.to_string wherepath) ++ str" where: " ++
                                  pr_id s.where_id ++ str"term: " ++ pr_constr s.where_term ++
                                  str" instance: " ++ prlist_with_sep spc pr_constr args ++ str" context map " ++
                                  pr_context_map (Global.env ()) s.where_prob);
          let ty =
            let ind = Nametab.locate (qualid_of_ident wherepath) in
            let ctx = pi1 s.where_prob in
            let subst = List.map (fun x -> mkVar (get_id x)) where_nctx in
            let fnapp = applistc (substl subst where_term) (extended_rel_list 0 ctx) in
            let args = List.append subst (extended_rel_list 0 ctx) in
            let app = applistc (Universes.constr_of_global ind) (List.append args [fnapp]) in
            it_mkProd_or_LetIn app ctx
          in
          tclTHEN acc (to82 (assert_by (Name s.where_id) ty (of82 wheretac)))
        in
        let tac = List.fold_left2 wheretac tclIDTAC wheres unfswheres in
        tclTHENLIST [tac;
                     tclTRY (autorewrite_one info.term_info.base_id);
                     cstrtac info.term_info;
                     if Option.is_empty unfs then tclIDTAC
                     else observe "whererev"
                                  (tclTRY (autorewrite_one (info.term_info.base_id ^ "_where_rev")));
                     eauto_with_below []]
      else tclIDTAC
    in
    (match c with
     | REmpty _ -> 
      observe "compute empty"
       (tclTHENLIST [intros_reducing; wheretac; to82 (find_empty_tac ())])
     | RProgram _ ->
      observe "compute "
      (tclTHENLIST
         [intros_reducing;
          tclTRY (autorewrite_one info.term_info.base_id);
          observe "wheretac" wheretac;
          cstrtac info.term_info;
          (** Each of the recursive calls result in an assumption. If it
              is a rec call in a where clause to itself we need to
              explicitely rewrite with the unfolding lemma (as the where
              clause induction hypothesis is about the unfolding whereas
              the term itself mentions the original function. *)
          tclMAP (fun i ->
              tclTRY (to82 (Tacticals.New.pf_constr_of_global
                              (Equations_common.global_reference i)
                              Equality.rewriteLR))) unfids;
          (to82 (solve_ind_rec_tac info.term_info))]))

  | Mapping (_, s) -> aux_ind_fun info chop unfs unfids s

open Sigma
       
let ind_fun_tac is_rec f info fid split unfsplit =
  if is_structural is_rec then
    let c = constant_value_in (Global.env ()) (destConst f) in
    let i = let (inds, _), _ = destFix c in inds.(0) in
    let recid = add_suffix fid "_rec" in
      (* tclCOMPLETE  *)
      (tclTHENLIST
	  [to82 (set_eos_tac ()); to82 (fix (Some recid) (succ i));
	   onLastDecl (fun decl gl ->
             let (n,b,t) = to_named_tuple decl in
	     let fixprot pats =
               { run = fun sigma ->
	       let c = 
		 mkLetIn (Anonymous, Universes.constr_of_global (Lazy.force coq_fix_proto),
			  Universes.constr_of_global (Lazy.force coq_unit), t) in
	       Sigma.here c sigma }
	     in
	     Proofview.V82.of_tactic
	       (change_in_hyp None fixprot (n, Locus.InHyp)) gl);
	   to82 intros; aux_ind_fun info 0 None [] split])
  else tclCOMPLETE (tclTHENLIST
      [to82 (set_eos_tac ()); to82 intros; aux_ind_fun info 0 unfsplit [] split])


let simpl_except (ids, csts) =
  let csts = Cset.fold Cpred.remove csts Cpred.full in
  let ids = Idset.fold Idpred.remove ids Idpred.full in
    CClosure.RedFlags.red_add_transparent CClosure.all
      (ids, csts)
      
let simpl_of csts =
  let opacify () = List.iter (fun cst -> 
    Global.set_strategy (ConstKey cst) Conv_oracle.Opaque) csts
  and transp () = List.iter (fun cst -> 
    Global.set_strategy (ConstKey cst) Conv_oracle.Expand) csts
  in opacify, transp

let get_proj_eval_ref p =
  match p with
  | LogicalDirect (loc, id) -> EvalVarRef id
  | LogicalProj r -> EvalConstRef r.comp_proj

let prove_unfolding_lemma info where_map proj f_cst funf_cst split unfold_split gl =
  let depelim h = depelim_tac h in
  let helpercsts = List.map (fun (_, _, i) -> fst (destConst (global_reference i)))
			    info.helpers_info in
  let opacify, transp = simpl_of (destConstRef (Lazy.force coq_hidebody) :: helpercsts) in
  let opacified tac gl = opacify (); let res = tac gl in transp (); res in
  let simpltac gl = opacified (to82 (simpl_equations_tac ())) gl in
  let my_simpl = opacified (to82 (simpl_in_concl)) in
  let unfolds = tclTHEN (autounfold_first [info.base_id] None)
    (autounfold_first [info.base_id ^ "_unfold"] None)
  in
  let solve_rec_eq gl =
    match kind_of_term (pf_concl gl) with
    | App (eq, [| ty; x; y |]) ->
	let xf, _ = decompose_app x and yf, _ = decompose_app y in
	  if eq_constr (mkConst f_cst) xf && is_rec_call proj yf then
            let proj_unf = get_proj_eval_ref proj in
	    let unfolds = unfold_in_concl 
	      [((Locus.OnlyOccurrences [1]), EvalConstRef f_cst); 
	       ((Locus.OnlyOccurrences [1]), proj_unf)]
	    in 
	      tclTHENLIST [to82 unfolds; simpltac; to82 (pi_tac ())] gl
	  else to82 reflexivity gl
    | _ -> to82 reflexivity gl
  in
  let solve_eq = tclORELSE (to82 reflexivity) solve_rec_eq in
  let abstract tac = tclABSTRACT None tac in
  let rec aux split unfold_split =
    match split, unfold_split with
    | Split (_, _, _, splits), Split ((ctx,pats,_), var, _, unfsplits) ->
       observe "split"
	(fun gl ->
	  match kind_of_term (pf_concl gl) with
	  | App (eq, [| ty; x; y |]) -> 
	     let f, pats' = decompose_app y in
             let c, unfolds =
                if !Equations_common.ocaml_splitting then
                  let _, _, c, _ = Term.destCase f in c, tclIDTAC
                else
                  List.nth (List.rev pats') (pred var), unfolds
             in
             let id = destVar (fst (decompose_app c)) in
	     let splits = List.map_filter (fun x -> x) (Array.to_list splits) in
	     let unfsplits = List.map_filter (fun x -> x) (Array.to_list unfsplits) in
	       to82 (abstract (of82 (tclTHEN_i (to82 (depelim id))
				               (fun i -> let split = nth splits (pred i) in
                                                      let unfsplit = nth unfsplits (pred i) in
					      tclTHENLIST [unfolds; aux split unfsplit])))) gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding goal") gl)
	    
    | Valid (_, _, _, _, _, rest), (* Valid ((ctx, _, _), ty, substc, tac, valid, unfrest) -> *) _ ->
       (* FIXME: Valid could take a splitting with more than 1 branch *)
       observe "valid"
               (aux (let (_, _, _, _, split) = List.nth rest 0 in split) unfold_split)
       (* tclTHEN_i tac (fun i -> let _, _, _, _, split = nth rest (pred i) in *)
       (*                      (\* let _, _, _, _, unfsplit = nth unfrest (pred i) in *\) *)
       (*  		    tclTHEN (Lazy.force unfold_add_pattern) (aux split unfold_split)) *)

    | RecValid (id, cs), unfsplit ->
       observe "recvalid"
	       (tclTHEN (to82 (unfold_recursor_tac ())) (aux cs unfsplit))

    | _, Mapping (lhs, s) -> aux split s
       
    | Refined (_, _, s), Refined ((ctx, _, _), refinfo, unfs) ->
	let id = pi1 refinfo.refined_obj in
	let ev = refinfo.refined_ex in
	let rec reftac gl = 
	  match kind_of_term (pf_concl gl) with
	  | App (f, [| ty; term1; term2 |]) ->
	      let f1, arg1 = destApp term1 and f2, arg2 = destApp term2 in
	      let _, a1 = find_helper_arg info f1 arg1 
	      and ev2, a2 = find_helper_arg info f2 arg2 in
	      let id = pf_get_new_id id gl in
		if Evar.equal ev2 ev then 
	  	  tclTHENLIST
	  	    [to82 (Equality.replace_by a1 a2
	  		     (of82 (tclTHENLIST [solve_eq])));
	  	     to82 (letin_tac None (Name id) a2 None Locusops.allHypsAndConcl);
	  	     Proofview.V82.of_tactic (clear_body [id]); unfolds; aux s unfs] gl
		else tclTHENLIST [unfolds; simpltac; reftac] gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding lemma goal") gl
	in
        let reftac = observe "refined" reftac in
	  to82 (abstract (of82 (tclTHENLIST [to82 intros; simpltac; reftac])))
	    
    | Compute (_, wheres, _, RProgram _), Compute (_, unfwheres, _, RProgram c) ->
       let wheretac acc w unfw =
         let assoc, id, _ =
           try Evar.Map.find (List.hd unfw.where_path) where_map
           with Not_found -> assert false
         in
         (* msg_debug (str"Found where: " ++ *)
         (*              pr_id unfw.where_id ++ str"term: " ++ pr_constr unfw.where_term ++ *)
         (*              str " where assoc " ++ pr_constr assoc); *)
         fun gl ->
         let env = pf_env gl in
         let evd = ref (project gl) in
         let ty =
           let ctx = pi1 unfw.where_prob in
           let lhs = mkApp (assoc, extended_rel_vect 0 ctx) in
           let rhs = mkApp (unfw.where_term, extended_rel_vect 0 ctx) in
           let eq = mkEq env evd unfw.where_arity lhs rhs in
           it_mkProd_or_LetIn eq ctx
         in
         let headcst f =
           let f, _ = decompose_app f in
           if isConst f then fst (destConst f)
           else assert false
         in
         let f_cst = headcst assoc and funf_cst = headcst unfw.where_term in
         let unfolds gl =
           let res = to82 (unfold_in_concl
	     [Locus.OnlyOccurrences [1], EvalConstRef f_cst;
	      (Locus.OnlyOccurrences [1], EvalConstRef funf_cst)]) gl in
           (* Global.set_strategy (ConstKey f_cst) Conv_oracle.Opaque; *)
	   (* Global.set_strategy (ConstKey funf_cst) Conv_oracle.Opaque; *)
           res
         in
         let tac =
           let tac =
             of82 (tclTHENLIST [to82 intros; unfolds;
                                (observe "where"
                                         (aux w.where_splitting unfw.where_splitting))])
           in
           assert_by (Name id) ty (of82 (tclTHEN (to82 (keep [])) (to82 (tclABSTRACT (Some id) tac))))
         in
         tclTHENLIST [Refiner.tclEVARS !evd; to82 tac;
                      to82 (Equality.rewriteLR (mkVar id));
                      acc] gl
       in
       let wheretacs =
         assert(List.length wheres = List.length unfwheres);
         List.fold_left2 wheretac tclIDTAC wheres unfwheres
       in
       observe "compute"
               (to82 (abstract (of82 (tclTHENLIST [to82 intros; wheretacs;
                                                   observe "compute rhs" (tclTRY unfolds);
                                                   simpltac; solve_eq]))))

    | Compute (_, _, _, _), Compute ((ctx,_,_), _, _, REmpty id) ->
	let d = nth ctx (pred id) in
	let id = out_name (get_name d) in
	to82 (abstract (depelim id))

    | _, _ -> assert false
  in
    try
      let unfolds = unfold_in_concl
	[Locus.OnlyOccurrences [1], EvalConstRef f_cst; 
	 (Locus.OnlyOccurrences [1], EvalConstRef funf_cst)]
      in
      let res =
	tclTHENLIST 
	  [to82 (set_eos_tac ()); to82 intros; to82 unfolds; my_simpl;
	   (* to82 (unfold_recursor_tac ()); *)
	   (fun gl ->
	     Global.set_strategy (ConstKey f_cst) Conv_oracle.Opaque;
	     Global.set_strategy (ConstKey funf_cst) Conv_oracle.Opaque;
	     aux split unfold_split gl)] gl
      in Global.set_strategy (ConstKey f_cst) Conv_oracle.Expand;
	Global.set_strategy (ConstKey funf_cst) Conv_oracle.Expand;
	res
    with e ->
      Global.set_strategy (ConstKey f_cst) Conv_oracle.Expand;
      Global.set_strategy (ConstKey funf_cst) Conv_oracle.Expand;
      raise e
  
