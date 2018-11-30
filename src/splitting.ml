(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Util
open Names
open Nameops
open Constr
open Inductiveops
open Globnames
open Reductionops
open Pp
open List
open Constrexpr
open Tactics
open Evarutil
open Evar_kinds
open Equations_common
open Syntax
open Covering
open EConstr
open Vars

let map_where f w =
  { w with
    where_nctx = map_named_context f w.where_nctx;
    where_prob = map_ctx_map f w.where_prob;
    where_term = f w.where_term;
    where_arity = f w.where_arity;
    where_type = f w.where_type }
    
let map_split f split =
  let rec aux = function
    | Compute (lhs, where, ty, RProgram c) ->
      let where' = 
        List.map
          (fun w -> let w' = map_where f w in
                 { w' with where_splitting = Lazy.from_val (aux (Lazy.force w.where_splitting)) })
          where
      in
      let lhs' = map_ctx_map f lhs in
	Compute (lhs', where', f ty, RProgram (f c))
    | Split (lhs, y, z, cs) ->
      let lhs' = map_ctx_map f lhs in
      Split (lhs', y, f z, Array.map (Option.map aux) cs)
    | Mapping (lhs, s) ->
       let lhs' = map_ctx_map f lhs in
       Mapping (lhs', aux s)
    | RecValid (id, c) -> RecValid (id, aux c)
    | Valid (lhs, y, z, w, u, cs) ->
      let lhs' = map_ctx_map f lhs in
	Valid (lhs', f y, z, w, u, 
	       List.map (fun (gl, cl, subst, invsubst, s) -> 
		 (gl, List.map f cl, map_ctx_map f subst, invsubst, aux s)) cs)
    | Refined (lhs, info, s) ->
      let lhs' = map_ctx_map f lhs in
      let (id, c, cty) = info.refined_obj in
      let (scf, scargs) = info.refined_app in
	Refined (lhs', { info with refined_obj = (id, f c, f cty);
	  refined_app = (f scf, List.map f scargs);
	  refined_rettyp = f info.refined_rettyp;
	  refined_revctx = map_ctx_map f info.refined_revctx;
	  refined_newprob = map_ctx_map f info.refined_newprob;
	  refined_newprob_to_lhs = map_ctx_map f info.refined_newprob_to_lhs;
	  refined_newty = f info.refined_newty}, aux s)
    | Compute (lhs, where, ty, (REmpty _ as em)) ->
       let lhs' = map_ctx_map f lhs in
       Compute (lhs', where, f ty, em)
  in aux split

let helper_evar evm evar env typ src =
  let sign, typ', instance, _ = push_rel_context_to_named_context env evm typ in
  let evm' = evar_declare sign evar typ' ~src evm in
    evm', mkEvar (evar, Array.of_list instance)

let term_of_tree status isevar env0 tree =
  let oblevars = ref Evar.Map.empty in
  let helpers = ref [] in
  let rec aux env evm = function
    | Compute ((ctx, _, _), where, ty, RProgram rhs) -> 
       let evm, ctx = 
         List.fold_right 
           (fun {where_id; where_nctx; where_prob; where_term;
               where_type; where_splitting }
              (evm, ctx) ->
             let env = push_named_context where_nctx env0 in
             (* FIXME push ctx too if mutual wheres *)
             let evm, c', ty' = aux env evm (Lazy.force where_splitting) in
             let inst = List.map get_id where_nctx in
             (** In de Bruijn context *)
             let tydb = Vars.subst_vars inst ty' in
             let evm, c', ty' =
               match kind evm where_term with
               | Evar (ev, _) ->
                 let term' = mkLetIn (Name (Id.of_string "prog"), c', ty', lift 1 ty') in
                 let evm, term =
                   helper_evar evm ev env term'
                    (dummy_loc, QuestionMark {
                        qm_obligation=Define false;
                        qm_name=Name where_id;
                        qm_record_field=None;
                    }) in
                 let ev = fst (destEvar !isevar term) in
                  oblevars := Evar.Map.add ev (List.length where_nctx) !oblevars;
                  helpers := (ev, 0) :: !helpers;
                  evm, subst_vars inst term, tydb
               | _ -> assert(false)
             in
             (evm, (make_def (Name where_id) (Some c') ty' :: ctx)))
           where (evm,ctx)
       in
       let body = it_mkLambda_or_LetIn rhs ctx and typ = it_mkProd_or_subst env evm ty ctx in
       evm, body, typ

    | Compute ((ctx, _, _), where, ty, REmpty split) ->
       assert (List.is_empty where);
       let evm, coq_nat = new_global evm (Lazy.force coq_nat) in
        let split = make_def (Name (Id.of_string "split"))
          (Some (of_constr (coq_nat_of_int (succ (length ctx - split)))))
          coq_nat
       in
       let ty' = it_mkProd_or_LetIn ty ctx in
       let let_ty' = mkLambda_or_LetIn split (lift 1 ty') in
       let evm, term = 
         new_evar env evm ~src:(dummy_loc, QuestionMark {
            qm_obligation=Define false;
            qm_name=Anonymous;
            qm_record_field=None;
        }) let_ty' in
       let ev = fst (destEvar evm term) in
       oblevars := Evar.Map.add ev 0 !oblevars;
       evm, term, ty'

    | Mapping ((ctx, p, ctx'), s) ->
       let evm, term, ty = aux env evm s in
       let args = Array.rev_of_list (snd (constrs_of_pats ~inacc_and_hide:false env evm p)) in
       let term = it_mkLambda_or_LetIn (whd_beta evm (mkApp (term, args))) ctx in
       let ty = it_mkProd_or_subst env evm (prod_appvect evm ty args) ctx in
         evm, term, ty
		    
    | RecValid (id, rest) -> aux env evm rest

    | Refined ((ctx, _, _), info, rest) ->
	let (id, _, _), ty, rarg, path, ev, (f, args), newprob, newty =
	  info.refined_obj, info.refined_rettyp,
	  info.refined_arg, info.refined_path,
	  info.refined_ex, info.refined_app, info.refined_newprob, info.refined_newty
	in
	let evm, sterm, sty = aux env evm rest in
	let evm, term, ty = 
          let term = mkLetIn (Name (Id.of_string "prog"), sterm, sty, lift 1 sty) in
	  let evm, term = helper_evar evm ev (Global.env ()) term
        (dummy_loc, QuestionMark {
            qm_obligation=Define false;
            qm_name=Name id;
            qm_record_field=None;
        })
	  in
	    oblevars := Evar.Map.add ev 0 !oblevars;
	    helpers := (ev, rarg) :: !helpers;
	    evm, term, ty
	in
	let term = applist (f, args) in
	let term = it_mkLambda_or_LetIn term ctx in
        let ty = it_mkProd_or_subst env evm ty ctx in
	  evm, term, ty

    | Valid ((ctx, _, _), ty, substc, tac, (entry, pv), rest) ->
	let tac = Proofview.tclDISPATCH 
          (List.map (fun (goal, args, subst, invsubst, x) ->
            Refine.refine ~typecheck:false begin fun evm ->
              let evm, term, ty = aux env evm x in
              (evm, applistc term args) end) rest)
	in
        let tac = Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm) tac in
	let _, pv', _, _ = Proofview.apply env tac pv in
	let c = List.hd (Proofview.partial_proof entry pv') in
	  Proofview.return pv', 
	  it_mkLambda_or_LetIn (subst_vars substc c) ctx, it_mkProd_or_LetIn ty ctx
	      
    | Split ((ctx, _, _) as subst, rel, ty, sp) ->
      (* Produce parts of a case that will be relevant. *)
      let evd = ref evm in
      let ctx', case_ty, branches_res, nb_cuts, rev_subst, to_apply, simpl =
        Sigma_types.smart_case env evd ctx rel ty in

      (* The next step is to use [simplify]. *)
      let simpl_step = if simpl then
          Simplify.simplify [None, Simplify.Infer_many] env evd
        else Simplify.identity env evd
      in
      let branches = Array.map2 (fun (ty, nb, csubst) next ->
        (* We get the context from the constructor arity. *)
        let new_ctx, ty = EConstr.decompose_prod_n_assum !isevar nb ty in
        let new_ctx = Namegen.name_context env !isevar new_ctx in
        let ty =
          if simpl || nb_cuts > 0 then
            let env = push_rel_context (new_ctx @ ctx') env in
            Tacred.hnf_constr env !evd ty
          else ty
        in
        (* Remove the cuts and append them to the context. *)
        let cut_ctx, ty = EConstr.decompose_prod_n_assum !isevar nb_cuts ty in
        (* TODO This context should be the same as (pi1 csubst). We could
           * either optimize (but names in [csubst] are worse) or just insert
           * a sanity-check. *)
        if !debug then begin
          let open Feedback in
          let ctx = cut_ctx @ new_ctx @ ctx' in
          msg_info(str"Simplifying term:");
          msg_info(let env = push_rel_context ctx env in
                   Printer.pr_econstr_env env !evd ty);
          msg_info(str"... in context:");
          msg_info(pr_context env !evd ctx)
        end;
        let ((hole, c), lsubst) = simpl_step (cut_ctx @ new_ctx @ ctx', ty) in
        let subst = Covering.compose_subst ~unsafe:true env ~sigma:!evd csubst subst in
        let subst = Covering.compose_subst ~unsafe:true env ~sigma:!evd lsubst subst in
        (* Now we build a term to put in the match branch. *)
        let c =
          match hole, next with
          (* Dead code: we should have found a proof of False. *)
          | None, None -> c
          (* Normal case: build recursively a subterm. *)
          | Some ((next_ctx, _), ev), Some s ->
            let evm, next_term, next_ty = aux env !evd s in
            (* Now we need to instantiate [ev] with the term [next_term]. *)
            (* [next_term] starts with lambdas, so we apply it to its context. *)
            let args = Equations_common.extended_rel_vect 0 next_ctx in
            let next_term = beta_appvect !isevar next_term args in
            (* We might need to permutate some rels. *)
            let next_subst = Covering.context_map_of_splitting s in
            let perm_subst = Covering.make_permutation ~env evm subst next_subst in
            let next_term = Covering.mapping_constr evm perm_subst next_term in
            (* We know the term is a correct instantiation of the evar, we
             * just need to apply it to the correct variables. *)
            let ev_info = Evd.find_undefined evm (fst ev) in
            let ev_ctx = Evd.evar_context ev_info in
            (* [next_term] is typed under [env, next_ctx] while the evar
             * is typed under [ev_ctx] *)
            let ev_ctx_constrs = List.map (fun decl ->
                let id = Context.Named.Declaration.get_id decl in
                EConstr.mkVar id) ev_ctx in
            let rels, named = List.chop (List.length next_ctx) ev_ctx_constrs in
            let vars_subst = List.map2 (fun decl c ->
                let id = Context.Named.Declaration.get_id decl in
                id, c) (Environ.named_context env) named in
            let term = Vars.replace_vars vars_subst next_term in
            let term = Vars.substl rels term in
            let _ =
              let env = Evd.evar_env ev_info in
              Typing.type_of env evm term
            in
            evd := Evd.define (fst ev) term evm;
            c
          (* This should not happen... *)
          | _ -> failwith "Should not fail here, please report."
        in
        EConstr.it_mkLambda_or_LetIn c (cut_ctx @ new_ctx)
        ) branches_res sp in

      (* Get back to the original context. *)
      let case_ty = Covering.mapping_constr !evd rev_subst case_ty in
      let branches = Array.map (Covering.mapping_constr !evd rev_subst) branches in

      (* Fetch the type of the variable that we want to eliminate. *)
      let after, decl, before = Covering.split_context (pred rel) ctx in
      let rel_ty = Context.Rel.Declaration.get_type decl in
      let rel_ty = Vars.lift rel rel_ty in
      let rel_t = EConstr.mkRel rel in
      let pind, args = find_inductive env !evd rel_ty in

      (* Build the case. *)
      let case_info = Inductiveops.make_case_info env (fst pind) Constr.RegularStyle in
      let indfam = Inductiveops.make_ind_family (from_peuniverses !evd pind, args) in
      let case = Inductiveops.make_case_or_project env !evd indfam case_info
          case_ty rel_t branches in
      let term = EConstr.mkApp (case, Array.of_list to_apply) in
      let term = EConstr.it_mkLambda_or_LetIn term ctx in
      let typ = it_mkProd_or_subst env evm ty ctx in
      let term = Evarutil.nf_evar !evd term in
      evd := Typing.check env !evd term typ;
      !evd, term, typ
  in
  let evm, term, typ = aux env0 !isevar tree in
    isevar := evm;
    !helpers, !oblevars, term, typ

let is_comp_obl sigma comp hole_kind =
  match comp with
  | None -> false
  | Some r -> 
      match hole_kind, r with 
      | ImplicitArg (ConstRef c, (n, _), _), LogicalProj r ->
	(* Constant.equal c r.comp_proj &&  *)n == 0
      | ImplicitArg (ConstRef c, (n, _), _), LogicalDirect (loc, id) ->
        is_rec_call sigma r (mkConst c)
      | _ -> false

let zeta_red =
  let red = Tacred.cbv_norm_flags
      CClosure.(RedFlags.red_add RedFlags.no_red RedFlags.fZETA)
  in
    reduct_in_concl (red, DEFAULTcast)

type term_info = {
  term_id : Names.GlobRef.t;
  term_ustate : UState.t;
  term_evars : (Id.t * Constr.t) list;
  base_id : string;
  decl_kind: Decl_kinds.definition_kind;
  helpers_info : (Evar.t * int * identifier) list;
  comp_obls : Id.Set.t; (** The recursive call proof obligations *)
  user_obls : Id.Set.t; (** The user obligations *)
}

type wf_rec_info =
  Constrexpr.constr_expr * Constrexpr.constr_expr option * Syntax.logical_rec

type rec_info =
  (rec_annot, wf_rec_info) Syntax.by_annot

type program_info = {
  program_id : Id.t;
  program_sign : EConstr.rel_context;
  program_arity : EConstr.t;
  program_rec : rec_info option;
  program_impls : Impargs.manual_explicitation list;
}

type compiled_program_info = {
    program_cst : Constant.t;
    program_split : splitting;
    program_split_info : term_info }
                  

let is_polymorphic info = pi2 info.decl_kind

let define_tree is_recursive fixprots poly impls status isevar env (i, sign, arity)
                comp split hook =
  let _ = isevar := Evarutil.nf_evar_map_undefined !isevar in
  let helpers, oblevs, t, ty = term_of_tree status isevar env split in
  let () = isevar := Evd.minimize_universes !isevar in
  let split = map_split (nf_evar !isevar) split in
  let obls, (emap, cmap), t', ty' =
    (* XXX: EConstr Problem upstream indeed. *)
    Obligations.eterm_obligations env i !isevar
      0 ~status (EConstr.to_constr ~abort_on_undefined_evars:false !isevar t)
                (EConstr.to_constr ~abort_on_undefined_evars:false !isevar (whd_betalet !isevar ty))
  in
  let compobls = ref Id.Set.empty in
  let userobls = ref Id.Set.empty in
  let obls = 
    Array.map (fun (id, ty, loc, s, d, t) ->
      let assc = rev_assoc Id.equal id emap in
      let tac = 
	if Evar.Map.mem assc oblevs 
	then 
          let intros = Evar.Map.find assc oblevs in
          Some (Tacticals.New.tclTHEN (Tacticals.New.tclDO intros intro) (equations_tac ()))
        else if is_comp_obl !isevar comp (snd loc) then
          let () = compobls := Id.Set.add id !compobls in
          let open Tacticals.New in
	    Some (tclORELSE
		    (tclTRY
                       (tclTHENLIST [zeta_red; Tactics.intros; solve_rec_tac ()]))
		    !Obligations.default_tactic)
        else (userobls := Id.Set.add id !userobls;
              Some ((!Obligations.default_tactic)))
      in (id, ty, loc, s, d, tac)) obls
  in
  let helpers = List.map (fun (ev, arg) ->
    (ev, arg, List.assoc ev emap)) helpers
  in
  let hook uctx evars locality gr =
    let l =
      Array.map_to_list (fun (id, ty, loc, s, d, tac) -> Libnames.qualid_of_ident id) obls in
    Extraction_plugin.Table.extraction_inline true l;
    let kind = (locality, poly, Decl_kinds.Definition) in
    let baseid = Id.to_string i in
    let term_info = { term_id = gr; term_ustate = uctx; term_evars = evars;
                      base_id = baseid; helpers_info = helpers; decl_kind = kind;
                      comp_obls = !compobls; user_obls = Id.Set.union !compobls !userobls } in
    let cmap = cmap (fun id -> try List.assoc id evars
                      with Not_found -> anomaly (Pp.str"Incomplete obligation to term substitution"))
    in
      hook split cmap term_info uctx
  in
  let univ_hook = Obligations.mk_univ_hook hook in
  let reduce x =
    let flags = CClosure.betaiotazeta in
    (* let flags = match comp with None -> flags *)
    (*   | Some f -> fCONST f.comp :: fCONST f.comp_proj :: flags *)
    (* in *)
    to_constr !isevar (clos_norm_flags flags (Global.env ()) !isevar (of_constr x))
  in
  let kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
  let ty' = it_mkProd_or_LetIn arity sign in
    match is_recursive with
    | Some (Syntax.Guarded [id]) ->
        let ty' = it_mkProd_or_LetIn ty' [make_assum Anonymous ty'] in
        let ty' = EConstr.to_constr !isevar ty' in
	let recarg =
	  match snd id with
          | MutualOn (_, Some (loc, id))
	  | NestedOn (Some (_, Some (loc, id))) -> Some (CAst.make ~loc id)
	  | _ -> None
	in
	ignore(Obligations.add_mutual_definitions [(i, t', ty', impls, obls)]
		 (Evd.evar_universe_context !isevar) [] ~kind
                 ~reduce ~univ_hook (Obligations.IsFixpoint [recarg, CStructRec]))
    | Some (Guarded ids) ->
        let ty' = it_mkProd_or_LetIn ty' fixprots in
        let ty' = EConstr.to_constr !isevar ty' in
        ignore(Obligations.add_definition
                 ~univ_hook ~kind
                 ~implicits:impls (add_suffix i "_functional") ~term:t' ty' ~reduce
		 (Evd.evar_universe_context !isevar) obls)
    | _ ->
       let ty' = EConstr.to_constr !isevar ty' in
       ignore(Obligations.add_definition ~univ_hook ~kind
	       ~implicits:impls i ~term:t' ty'
	       ~reduce (Evd.evar_universe_context !isevar) obls)

let mapping_rhs sigma s = function
  | RProgram c -> RProgram (mapping_constr sigma s c)
  | REmpty i ->
      try match nth (pi2 s) (pred i) with
      | PRel i' -> REmpty i'
      | _ -> assert false
      with Not_found -> assert false

let map_rhs f g = function
  | RProgram c -> RProgram (f c)
  | REmpty i -> REmpty (g i)
