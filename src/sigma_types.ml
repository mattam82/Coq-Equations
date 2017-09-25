(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Context
open Vars
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
open Coqlib
open Globnames
open Tactics
open Refiner
open Tacticals
open Tacmach
open Decl_kinds
open Equations_common

let mkConstructG c u =
  mkConstructU (destConstructRef (Lazy.force c), u)

let mkIndG c u =
  mkIndU (destIndRef (Lazy.force c), u)

let mkConstG c u =
  mkConstU (destConstRef (Lazy.force c), u)

let mkAppG evd gr args = 
  let c = e_new_global evd gr in
    mkApp (c, args)

let applistG evd gr args = 
  mkAppG evd gr (Array.of_list args)

let mkSig evd (n, c, t) = 
  let args = [| c; mkLambda (n, c, t) |] in
    mkAppG evd (Lazy.force coq_sigma) args

let constrs_of_coq_sigma env evd t alias = 
  let rec aux env proj c ty =
    match kind_of_term c with
    | App (f, args) when is_global (Lazy.force coq_sigmaI) f && 
	                   Array.length args = 4 ->
       let ty = Retyping.get_type_of env !evd args.(1) in
	(match kind_of_term ty with
	| Prod (n, b, t) ->
	    let p1 = mkProj (Lazy.force coq_pr1, proj) in
	    let p2 = mkProj (Lazy.force coq_pr2, proj) in
	    (n, args.(2), p1, args.(0)) ::
              aux (push_rel (of_tuple (n, None, b)) env) p2 args.(3) t
	| _ -> raise (Invalid_argument "constrs_of_coq_sigma"))
    | _ -> [(Anonymous, c, proj, ty)]
  in aux env alias t (Retyping.get_type_of env !evd t)

let decompose_coq_sigma t = 
  let s = Lazy.force coq_sigma in
    match kind_of_term t with
    | App (f, args) when is_global s f && Array.length args = 2 ->
       let ind, u = destInd f in
         Some (u, args.(0), args.(1))
    | _ -> None

let decompose_indapp f args =
  match kind_of_term f with
  | Construct ((ind,_),_)
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
	mkApp (f, pars), args
  | _ -> f, args


(* let sigT_info = lazy (make_case_info (Global.env ()) (Globnames.destIndRef (Lazy.force sigT).typ) LetStyle) *)

let telescope evd = function
  | [] -> assert false
  | [d] -> let (n, _, t) = to_tuple d in t, [of_tuple (n, Some (mkRel 1), lift 1 t)],
                                        mkRel 1
  | d :: tl ->
      let (n, _, t) = to_tuple d in
      let len = succ (List.length tl) in
      let ty, tys =
	List.fold_left
	  (fun (ty, tys) d ->
            let (n, b, t) = to_tuple d in
	    let pred = mkLambda (n, t, ty) in
	    let sigty = mkAppG evd (Lazy.force coq_sigma) [|t; pred|] in
            let _, u = destInd (fst (destApp sigty)) in
	      (sigty, (u, pred) :: tys))
	  (t, []) tl
      in
      let constr, _ = 
	List.fold_right (fun (u, pred) (intro, k) ->
	  let pred = Vars.lift k pred in
	  let (n, dom, codom) = destLambda pred in
	  let intro =
            mkApp (Universes.constr_of_global_univ
                     (Lazy.force coq_sigmaI, u), [| dom; pred; mkRel k; intro|]) in
	    (intro, succ k))
	  tys (mkRel 1, 2)
      in
      let (last, _, subst) = List.fold_right2
	(fun pred d (prev, k, subst) ->
          let (n, b, t) = to_tuple d in
	  let proj1 = mkProj (Lazy.force coq_pr1, prev) in
	  let proj2 = mkProj (Lazy.force coq_pr2, prev) in
	    (lift 1 proj2, succ k, of_tuple (n, Some proj1, liftn 1 k t) :: subst))
	(List.rev tys) tl (mkRel 1, 1, [])
      in ty, (of_tuple (n, Some last, liftn 1 len t) :: subst), constr

let sigmaize ?(liftty=0) env0 evd pars f =
  let env = push_rel_context pars env0 in
  let ty = Retyping.get_type_of env !evd f in
  let ctx, concl = splay_prod_assum env !evd ty in
  let ctx = smash_rel_context ctx in
  let argtyp, letbinders, make = telescope evd ctx in
    (* Everyting is in env, move to index :: letbinders :: env *) 
  let lenb = List.length letbinders in
  let pred =
    mkLambda (Name (id_of_string "index"), argtyp,
	      it_mkProd_or_LetIn
	        (mkApp (lift (succ lenb) f, 
		        rel_vect 0 lenb))
	        letbinders)
  in
  let tyargs = [| argtyp; pred |] in
  let tysig = mkAppG evd (Lazy.force coq_sigma) tyargs in
  let indexproj = Lazy.force coq_pr1 in
  let valproj = Lazy.force coq_pr2 in
  let indices = 
    (List.rev_map (fun l -> substl (tl l) (hd l)) 
     (Equations_common.proper_tails (map (fun d -> Option.get (pi2 (to_tuple d))) letbinders)))
  in
  let valsig =
    let argtyp = lift (succ lenb) argtyp in
    let pred = 
      mkLambda (Name (id_of_string "index"), argtyp,
	       it_mkProd_or_LetIn
		 (mkApp (lift (2 * succ lenb) f,
			rel_vect 0 lenb))
		 (Equations_common.lift_rel_contextn 1 (succ lenb) letbinders))
    in
    let _tylift = lift lenb argtyp in
      mkAppG evd (Lazy.force coq_sigmaI)
	[|argtyp; pred; lift 1 make; mkRel 1|]
  in
  let pred = it_mkLambda_or_LetIn pred pars in
  let _ = Typing.e_type_of env0 evd pred in
  let nf, _ = Evarutil.e_nf_evars_and_universes evd in
    (nf argtyp, nf pred, map_rel_context nf pars, List.map nf indices,
     indexproj, valproj, nf valsig, nf tysig)

let ind_name ind = Nametab.basename_of_global (Globnames.IndRef ind)

let signature_ref = lazy (init_reference ["Equations";"Signature"] "Signature")
let signature_sig = lazy (init_reference ["Equations";"Signature"] "signature")
let signature_pack = lazy (init_reference ["Equations";"Signature"] "signature_pack")

let signature_class evd =
  let evd, c = new_global evd (Lazy.force signature_ref) in
    evd, fst (snd (Option.get (Typeclasses.class_of_constr c)))

let build_sig_of_ind env sigma (ind,u as indu) =
  let (mib, oib as _mind) = Global.lookup_inductive ind in
  let ctx = inductive_alldecls indu in
  let ctx = smash_rel_context ctx in
  let lenpars = mib.mind_nparams_rec in
  let lenargs = List.length ctx - lenpars in
  if lenargs = 0 then
    user_err_loc (dummy_loc, "Derive Signature", 
		 str"No signature to derive for non-dependent inductive types");
  let args, pars = List.chop lenargs ctx in
  let parapp = mkApp (mkIndU indu, extended_rel_vect 0 pars) in
  let fullapp = mkApp (mkIndU indu, extended_rel_vect 0 ctx) in
  let evd = ref sigma in
  let idx, pred, pars, _, _, _, valsig, _ = 
    sigmaize env evd pars parapp 
  in
  let sigma = !evd in
    sigma, pred, pars, fullapp, valsig, ctx, lenargs, idx

let declare_sig_of_ind env sigma poly (ind,u) =
  let sigma, pred, pars, fullapp, valsig, ctx, lenargs, idx =
    build_sig_of_ind env sigma (ind, u) in
  let indid = ind_name ind in
  let simpl = Tacred.simpl env sigma in
  let indsig =
    let indsigid = add_suffix indid "_sig" in
      declare_constant indsigid pred
	None poly sigma (IsDefinition Definition)
  in
  let pack_id = add_suffix indid "_sig_pack" in
  let pack_fn = 
    let vbinder = of_tuple (Name (add_suffix indid "_var"), None, fullapp) in
    let term = it_mkLambda_or_LetIn valsig (vbinder :: ctx) 
    in
    (* let rettype = mkApp (mkConst indsig, extended_rel_vect (succ lenargs) pars) in *)
      declare_constant pack_id (simpl term)
	None (* (Some (it_mkProd_or_LetIn rettype (vbinder :: ctx))) *)
	poly sigma
	(IsDefinition Definition)
  in
  let sigma = if not poly then Evd.from_env (Global.env ()) else sigma in
  let sigma, c = signature_class sigma in
  let env = Global.env () in
  let sigma, indsig = Evd.fresh_global env sigma (ConstRef indsig) in
  let sigma, pack_fn = Evd.fresh_global env sigma (ConstRef pack_fn) in
  let signature_id = add_suffix indid "_Signature" in
  let inst = 
    declare_instance signature_id
      poly sigma ctx c
      [fullapp; lift lenargs idx;
       mkApp (indsig, extended_rel_vect lenargs pars);
       mkApp (pack_fn, extended_rel_vect 0 ctx)]
  in
  Extraction_plugin.Table.extraction_inline true [Ident (dummy_loc, pack_id)];
  Extraction_plugin.Table.extraction_inline true [Ident (dummy_loc, signature_id)];
  inst

let () =
  let fn env sigma ~polymorphic c = ignore (declare_sig_of_ind env sigma polymorphic c) in
  Derive.(register_derive
            { derive_name = "Signature";
              derive_fn = make_derive_ind fn })

let get_signature env sigma ty =
  try
    let sigma', (idx, _) = 
      new_type_evar env sigma Evd.univ_flexible
                    ~src:(dummy_loc, Evar_kinds.InternalHole) in
    let _idxev = fst (destEvar idx) in
    let sigma', cl = new_global sigma' (Lazy.force signature_ref) in
    let inst = mkApp (cl, [| ty; idx |]) in
    let sigma', tc = Typeclasses.resolve_one_typeclass env sigma' inst in
    let _, u = destInd (fst (destApp inst)) in
    let ssig = mkApp (mkConstG signature_sig u, [| ty; idx; tc |]) in
    let spack = mkApp (mkConstG signature_pack u, [| ty; idx; tc |]) in
      (sigma', nf_evar sigma' ssig, nf_evar sigma' spack)
  with Not_found ->
    let pind, args = Inductive.find_rectype env ty in
    let sigma, pred, pars, _, valsig, ctx, _, _ =
      build_sig_of_ind env sigma pind in
    Feedback.msg_warning (str "Automatically inlined signature for type " ++
    Printer.pr_pinductive env pind ++ str ". Use [Derive Signature for " ++
    Printer.pr_pinductive env pind ++ str ".] to avoid this.");
    let indsig = pred in
    let vbinder = of_tuple (Anonymous, None, ty) in
    let pack_fn = it_mkLambda_or_LetIn valsig (vbinder :: ctx) in
    let pack_fn = beta_applist (pack_fn, args) in
      (sigma, nf_evar sigma (mkApp (indsig, Array.of_list args)),
       nf_evar sigma pack_fn)

(* let generalize_sigma env sigma c packid = *)
(*   let ty = Retyping.get_type_of env sigma c in *)
(*   let value, typ = mk_pack env sigma ty in *)
(*   let valsig = value c in *)
(*   let setvar = letin_tac None (Name packid) valsig (Some typ) nowhere in *)
(*   let geneq = generalize [mkCast (mkRefl typ (mkVar packid),  *)
(* 					 DEFAULTcast, mkEq typ (mkVar packid) valsig)] in *)
(*   let clear = clear_body [packid] in *)
(*   let movetop = move_hyp true packid (Tacexpr.MoveToEnd false) in *)
(*     tclTHENLIST [setvar; geneq; clear; movetop] *)

let pattern_sigma ~assoc_right c hyp env sigma =
  let evd = ref sigma in
  let terms = constrs_of_coq_sigma env evd c (mkVar hyp) in
  let terms =
    if assoc_right then terms
    else match terms with
         | (x, t, p, rest) :: term :: _ -> 
	    constrs_of_coq_sigma env evd t p @ terms
         | _ -> terms
  in
  let pat = Patternops.pattern_of_constr env !evd in
  let terms = 
    if assoc_right then terms
    else match terms with
         | (x, t, p, rest) :: _ :: _ -> terms @ constrs_of_coq_sigma env evd t p 
         | _ -> terms
  in
  let projs = map (fun (x, t, p, rest) -> (pat t, make_change_arg p)) terms in
  let projabs =
    tclTHENLIST ((if assoc_right then rev_map
                  else map) (fun (t, p) -> to82 (change (Some t) p Locusops.onConcl))
                            projs) in
    Proofview.V82.tactic (tclTHEN (Refiner.tclEVARS !evd) projabs)
			 
let curry_left_hyp env sigma c t =
  let aux c t na u ty pred concl =
    let (n, idx, dom) = destLambda pred in
    let newctx = [of_tuple (na, None, dom); of_tuple (n, None, idx)] in
    let tuple = mkApp (mkConstructG coq_sigmaI u,
		       [| lift 2 ty; lift 2 pred; mkRel 2; mkRel 1 |])
    in
    let term = it_mkLambda_or_LetIn (mkApp (lift 2 c, [| tuple |])) newctx in
    let typ = it_mkProd_or_LetIn (subst1 tuple (liftn 2 2 concl)) newctx in
      (term, typ)
  in
  let rec curry_index c t =
    match kind_of_term t with
    | Prod (na, dom, concl) ->
       (match decompose_coq_sigma dom with
	| None -> (c, t)
	| Some (u, ty, pred) ->
	   let term, typ = aux c t na u ty pred concl in
	   match kind_of_term typ with
	   | Prod (na', dom', concl') ->
	      let body' = pi3 (destLambda term) in
	      let c, t = curry_index body' concl' in
	      mkLambda (na', dom', c), mkProd (na', dom', t)
	   | _ -> (term, typ))
    | _ -> (c, t)
  in
  let curry c t =
    match kind_of_term t with
    | Prod (na, dom, concl) ->
       (match decompose_coq_sigma dom with
	| None -> None
	| Some (inst, ty, pred) ->
	   let term, typ = aux c t na inst ty pred concl in
	   let c, t = curry_index term typ in
	     Some (c, t))
    | _ -> None
  in curry c t

let curry na c =
  let rec make_arg na t =
    match decompose_coq_sigma t with
    | None -> 
       if Globnames.is_global (Lazy.force coq_unit) t then
         let _, u = destInd t in
         [], Universes.constr_of_global_univ (Lazy.force coq_tt, u)
       else [of_tuple (na,None,t)], mkRel 1
    | Some (u, ty, pred) ->
       let na, _, codom =
         if isLambda pred then destLambda pred 
         else (Anonymous, ty, mkApp (pred, [|mkRel 1|])) in
       let ctx, rest = make_arg na codom in
       let len = List.length ctx in 
       let tuple = 
         mkApp (mkConstructG coq_sigmaI u,
		[| lift (len + 1) ty; lift (len + 1) pred; mkRel (len + 1); rest |])
       in
       ctx @ [of_tuple (na, None, ty)], tuple
  in
  make_arg na c

open Sigma

let uncurry_hyps name =
  let open Proofview in
  let open Proofview.Notations in
  Proofview.Goal.enter { enter = fun gl ->
    let hyps = Goal.hyps (Goal.assume gl) in
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let hyps, _ =
      List.split_when (fun d ->
         Globnames.is_global (Lazy.force coq_end_of_section_ref) (get_named_type d)
          || is_section_variable (get_id d)) hyps in
    let rec ondecl (sigma, acc, ty) d =
      let (dna, _, dty) = to_named_tuple d in
      let sigma, sigmaI = Evd.fresh_global env sigma (Lazy.force coq_sigmaI) in
      let _, u = destConstruct sigmaI in
      let types = [| dty; mkNamedLambda dna dty ty |] in
      let app = mkApp (sigmaI, Array.append types [| mkVar dna; acc |]) in
      (sigma, app, mkApp (mkIndG coq_sigma u, types))
    in
    let Sigma (unit, sigma, p) = Sigma.fresh_global env sigma (Lazy.force coq_tt) in
    let Sigma (unittype, sigma, q) =
      Sigma.fresh_global env sigma (Lazy.force coq_unit) in
    let sigma, term, ty = 
      fold_named_context_reverse 
        ondecl ~init:(Sigma.to_evar_map sigma, unit, unittype) hyps
    in
    let sigma, _ = Typing.type_of env sigma term in
    Proofview.Unsafe.tclEVARS sigma <*>
      Tactics.letin_tac None (Name name) term (Some ty) nowhere }

let uncurry_call env sigma c =
  let hd, args = decompose_app c in
  let ty = Retyping.get_type_of env sigma hd in
  let ctx, concl = decompose_prod_n_assum (List.length args) ty in
  let evdref = ref sigma in
  (* let ctx = (Anonymous, None, concl) :: ctx in *)
  let sigty, sigctx, constr = telescope evdref ctx in
  let app = substl (List.rev args) constr in
  !evdref, app, sigty

(* Produce parts of a case on a variable, while introducing cuts and
 * equalities when necessary.
 * This function requires a full rel_context, a rel to eliminate, and a goal.
 * It returns:
 *   - a context [ctx'];
 *   - a return type valid under [ctx'];
 *   - the type of the branches of the case;
 *   - a context_map for each branch;
 *   - a number of cuts;
 *   - a reverse substitution from [ctx] to [ctx'];
 *   - a list of terms in [ctx] to apply to the case once it is built;
 *   - a boolean about the need for simplification or not. *)
let smart_case (env : Environ.env) (evd : Evd.evar_map ref)
  (ctx : rel_context) (rel : int) (goal : Term.types) :
    rel_context * Term.types *
    (Term.types * int * Covering.context_map) array *
    int * Covering.context_map * Term.constr list * bool =
  let after, rel_decl, before = Covering.split_context (pred rel) ctx in
  let rel_ty = Context.Rel.Declaration.get_type rel_decl in
  let rel_ty = Vars.lift rel rel_ty in
  let rel_t = Constr.mkRel rel in
  (* Fetch some information about the type of the variable being eliminated. *)
  let pind, args = Inductive.find_inductive env rel_ty in
  let mib, oib = Global.lookup_pinductive pind in
  let params, indices = List.chop mib.mind_nparams args in
  (* The variable itself will be treated for all purpose as one of its indices. *)
  let indices = indices @ [rel_t] in
  let indfam = Inductiveops.make_ind_family (pind, params) in
  let arity_ctx = Inductiveops.make_arity_signature env true indfam in
  let rev_arity_ctx = List.rev arity_ctx in

  (* Firstly, we need to analyze each index to decide if we should introduce
   * an equality for it or not. *)
  (* For each index of the type, we _omit_ it if and only if
   *   1) It is a variable.
   *   2) It did not appear before.
   *   3) Its type does not depend on something that was not omitted before.
  *)

  (* ===== FORWARD PASS ===== *)
  let rec compute_omitted prev_indices indices prev_ctx ctx omitted candidate nb =
    match indices, ctx with
    | [], [] -> omitted, nb, prev_indices, candidate
    | idx :: indices, decl :: ctx ->
        let omit, cand =
          (* Variable. *)
          if not (Term.isRel idx) then None, None
          (* Linearity. *)
          else if List.exists (Termops.dependent idx) params then None, None
          else if List.exists (Termops.dependent idx) prev_indices then None, None
          (* Dependency. *)
          else
            let rel = Term.destRel idx in
            let decl_ty = Context.Rel.Declaration.get_type decl in
            let deps = Termops.free_rels decl_ty in
            let omit =
              Int.Set.fold (fun x b ->
                b && try Option.has_some (List.nth omitted (x-1))
                with Failure _ | Invalid_argument _ -> true) deps true
            in (if omit then Some rel else None), Some rel
        in
        compute_omitted (idx :: prev_indices) indices
                        (decl :: prev_ctx) ctx
                        (omit :: omitted)
                        (cand :: candidate)
                        (if Option.has_some omit then nb else succ nb)
    | _, _ -> assert false
  in
  (* [rev_indices] also include the variable being eliminated at its head. *)
  let omitted, nb, rev_indices, candidate =
    compute_omitted [] indices [] rev_arity_ctx [] [] 0 in

  (* Now we do a pass backwards to check if we can omit more things. *)
  (* More precisely, for any variable in rev_indices, we can omit it if
   * nothing in the remaining context that was not omitted depends on it. *)
  (* TODO The algorithm is very inefficient for now. *)

  (* ===== BACKWARD PASS ===== *)
  let rec compute_omitted_bis rev_omitted omitted candidate rev_indices nb =
    match omitted, candidate, rev_indices with
    | [], [], [] -> rev_omitted, nb
    | Some rel :: omitted, _ :: candidate, idx :: rev_indices ->
        compute_omitted_bis (Some rel :: rev_omitted) omitted candidate
          rev_indices nb
    | _ :: omitted, None :: candidate, idx :: rev_indices ->
        compute_omitted_bis (None :: rev_omitted) omitted candidate
          rev_indices nb
    | None :: omitted, Some rel :: candidate, idx :: rev_indices ->
        (* We know that [idx] is [Rel rel] and a candidate for omission. *)
        (* TODO Very inefficient... *)
        let new_decl = Context.Rel.Declaration.LocalAssum (Anonymous, goal) in
        let after = new_decl :: CList.firstn (pred rel) ctx in
        let omit = CList.for_all_i (fun i decl ->
          let decl_ty = Context.Rel.Declaration.get_type decl in
          (* No dependency. *)
          not (Termops.dependent (Constr.mkRel (rel - i)) decl_ty) ||
          (* Already omitted. *)
          List.mem (Some i) rev_omitted) 0 after in
        if omit then
          compute_omitted_bis (Some rel :: rev_omitted) omitted candidate
            rev_indices (pred nb)
        else
          compute_omitted_bis (None :: rev_omitted) omitted candidate
            rev_indices nb
    | _, _, _ -> assert false
  in
  let rev_omitted, nb = compute_omitted_bis [] omitted candidate rev_indices nb in
  let omitted = List.rev rev_omitted in

  (* At this point, we have [omitted] which is a list of either [Some rel] when
   * the corresponding index is omitted, [None] otherwise, and [nb] is the number
   * of [None] in this list. *)
  (* Now we consider the context [arity_ctx @ ctx], which is the context of
   * the return type. We will build a context substitution from this context
   * to a new one with shape [cuts @ arity_ctx @ ctx'] where [ctx'] is some
   * sub-context of [ctx], [cuts] is a number of declarations for which we
   * need to introduce cutx, and [arity_ctx] has been left untouched. *)

  (* ===== STRENGTHENING ===== *)
  let subst = Covering.id_subst (arity_ctx @ ctx) in
  let rev_subst = Covering.id_subst (arity_ctx @ ctx) in
  let subst, rev_subst = List.fold_left (
    fun ((ctx, _, _) as subst, rev_subst) -> function
    | None -> subst, rev_subst
    | Some rel ->
        let fresh_rel = Covering.mapping_constr subst (Constr.mkRel 1) in
        let target_rel = Constr.mkRel (rel + oib.mind_nrealargs + 1) in
        let target_rel = Covering.mapping_constr subst target_rel in
        let target_rel = Term.destRel target_rel in
        let lsubst, lrev_subst = Covering.new_strengthen env !evd ctx target_rel fresh_rel in
        let res1 = Covering.compose_subst env ~sigma:!evd lsubst subst in
        let res2 = Covering.compose_subst env ~sigma:!evd rev_subst lrev_subst in
          res1, res2
  ) (subst, rev_subst) omitted in
  let nb_cuts_omit = pred (Term.destRel
   (Covering.mapping_constr subst (Constr.mkRel 1))) in
  (* [ctx'] is the context under which we will build the case in a first step. *)
  (* This is [ctx] where everything omitted and cut is removed. *)
  let ctx' = List.skipn (nb_cuts_omit + oib.mind_nrealargs + 1) (pi3 rev_subst) in
  let rev_subst' = List.skipn (nb_cuts_omit + oib.mind_nrealargs + 1) (pi2 rev_subst) in
  let rev_subst' = Covering.lift_pats (-(oib.mind_nrealargs+1)) rev_subst' in
  let rev_subst_without_cuts = Covering.mk_ctx_map env !evd ctx rev_subst' ctx' in
  (* Now we will work under a context with [ctx'] as a prefix, so we will be
   * able to go back to [ctx] easily. *)

  (* ===== SUBSTITUTION ===== *)
  let subst = CList.fold_right_i (
    fun i omit ((ctx, pats, _) as subst)->
    match omit with
    | None -> subst
    | Some rel ->
        let orig = oib.mind_nrealargs + 1 - i in
        let fresh_rel = Covering.specialize pats (Covering.PRel orig) in
        let target_rel = Constr.mkRel (rel + oib.mind_nrealargs + 1) in
        let target_rel = Covering.mapping_constr subst target_rel in
        let target_rel = Term.destRel target_rel in
        (* We know that this call will fall in the simple case
         * of [single_subst], because we already strengthened everything. *)
        (* TODO Related to [compute_omitted_bis], we cannot actually substitute
         * the terms that were omitted simply due to the fact that nothing
         * depends on them, as it would be an ill-typed substitution. *)
        let lsubst = Covering.single_subst ~unsafe:true env !evd target_rel fresh_rel ctx in
          Covering.compose_subst ~unsafe:true env ~sigma:!evd lsubst subst
  ) 0 omitted subst in
  let nb_cuts = pred (Term.destRel
   (Covering.mapping_constr subst (Constr.mkRel 1))) in
  (* Also useful: a substitution from [ctx] to the context with cuts. *)
  let subst_to_cuts =
    let lift_subst = Covering.mk_ctx_map env !evd (arity_ctx @ ctx)
    (Covering.lift_pats (oib.mind_nrealargs + 1) (pi2 (Covering.id_subst ctx)))
    ctx in
      Covering.compose_subst ~unsafe:true env ~sigma:!evd subst lift_subst
  in

  (* Finally, we can work on producing a return type. *)
  let goal = Covering.mapping_constr subst_to_cuts goal in

  (* ===== CUTS ===== *)
  let cuts_ctx, remaining = List.chop nb_cuts (pi1 subst) in
  let fresh_ctx = List.firstn (oib.mind_nrealargs + 1) remaining in
  let revert_cut x =
    let rec revert_cut i = function
      | [] -> failwith "Could not revert a cut, please report."
      | Covering.PRel y :: _ when Int.equal x y -> Constr.mkRel i
      | _ :: l -> revert_cut (succ i) l
    in revert_cut (- oib.mind_nrealargs) (pi2 subst)
  in
  let rev_cut_vars = CList.map revert_cut (CList.init nb_cuts (fun i -> succ i)) in
  let cut_vars = List.rev rev_cut_vars in

  (* ===== EQUALITY OF TELESCOPES ===== *)
  let goal, to_apply, simpl =
    if Int.equal nb 0 then goal, [], false
    else
      let arity_ctx' = Covering.specialize_rel_context (pi2 subst_to_cuts) arity_ctx in
      let rev_indices' = List.map (Covering.mapping_constr subst_to_cuts) rev_indices in
      let _, rev_sigctx, tele_lhs, tele_rhs =
        CList.fold_left3 (
          fun (k, rev_sigctx, tele_lhs, tele_rhs) decl idx -> function
          | Some _ -> (* Don't add a binder, but substitute *)
              let fresh = Constr.mkRel (nb_cuts + oib.mind_nrealargs + 1) in
              let rev_sigctx = Equations_common.subst_telescope fresh rev_sigctx in
              succ k, rev_sigctx, tele_lhs, tele_rhs
          | None -> (* Add a binder to the telescope. *)
              let rhs = Constr.mkRel k in
              succ k, decl :: rev_sigctx, idx :: tele_lhs, rhs :: tele_rhs

        ) (succ nb_cuts, [], [], []) arity_ctx' rev_indices' omitted
      in
      let sigctx = List.rev rev_sigctx in
      let sigty, _, sigconstr = telescope evd sigctx in

      (* Build a goal with an equality of telescopes at the front. *)
      let left_sig = Vars.substl (List.rev tele_lhs) sigconstr in
      let right_sig = Vars.substl (List.rev tele_rhs) sigconstr in
      (* TODO Swap left_sig and right_sig... *)
      let eq = Equations_common.mkEq env evd sigty right_sig left_sig in
      let goal = Vars.lift 1 goal in
      let goal = Term.mkProd (Anonymous, eq, goal) in

      (* Build a reflexivity proof to apply to the case. *)
      let tr_out t =
        let t = Termops.it_mkLambda_or_LetIn t cuts_ctx in
        let t = Termops.it_mkLambda_or_LetIn t fresh_ctx in
        let t = Covering.mapping_constr rev_subst_without_cuts t in
          Reductionops.beta_applist (t, indices @ cut_vars)
      in
        goal, [Equations_common.mkRefl env evd (tr_out sigty) (tr_out left_sig)], true
  in

  (* ===== RESOURCES FOR EACH BRANCH ===== *)
  let params = List.map (Covering.mapping_constr subst_to_cuts) params in
  (* If something is wrong here, it means that one of the parameters was
   * omitted or cut, which should be wrong... *)
  let params = List.map (Vars.lift (-(nb_cuts + oib.mind_nrealargs + 1))) params in
  let goal = Termops.it_mkProd_or_LetIn goal cuts_ctx in
  let goal = Term.it_mkLambda_or_LetIn goal fresh_ctx in
  let branches_ty = Inductive.build_branches_type pind (mib, oib) params goal in
  (* Refresh the inductive family. *)
  let indfam = Inductiveops.make_ind_family (pind, params) in
  let branches_info = Inductiveops.get_constructors env indfam in
  let full_subst =
    let (ctx', pats, ctx) = Covering.id_subst ctx in
    let pats = Covering.lift_pats (oib.mind_nrealargs + 1) pats in
    let ctx' = arity_ctx @ ctx' in
      Covering.mk_ctx_map env !evd ctx' pats ctx
  in
  let full_subst = Covering.compose_subst ~unsafe:true env ~sigma:!evd subst full_subst in
  let pats_ctx' = pi2 (Covering.id_subst ctx') in
  let pats_cuts = pi2 (Covering.id_subst cuts_ctx) in
  let branches_subst = Array.map (fun summary ->
    (* This summary is under context [ctx']. *)
    let indices = summary.Inductiveops.cs_concl_realargs in
    let params = Array.of_list summary.Inductiveops.cs_params in
    let term = Constr.mkConstructU summary.Inductiveops.cs_cstr in
    let term = Constr.mkApp (term, params) in
    let term = Vars.lift (summary.Inductiveops.cs_nargs) term in
    let term = Constr.mkApp (term, Termops.rel_vect 0 summary.Inductiveops.cs_nargs) in
    (* Indices are typed under [args @ ctx'] *)
    let indices = (Array.to_list indices) @ [term] in
    let args = summary.Inductiveops.cs_args in
    (* Substitute the indices in [cuts_ctx]. *)
    let rev_indices = List.rev indices in
    let pats_indices = List.map Covering.pat_of_constr rev_indices in
    let pats_ctx' = Covering.lift_pats summary.Inductiveops.cs_nargs pats_ctx' in
    let pats = pats_indices @ pats_ctx' in
    let cuts_ctx = Covering.specialize_rel_context pats cuts_ctx in
    let pats = Covering.lift_pats nb_cuts pats in
    let pats = pats_cuts @ pats in
    let csubst = Covering.mk_ctx_map env !evd (cuts_ctx @ args @ ctx') pats (pi1 subst) in
      Covering.compose_subst ~unsafe:true env ~sigma:!evd csubst full_subst
  ) branches_info in
  let branches_nb = Array.map (fun summary ->
    summary.Inductiveops.cs_nargs) branches_info in
  let branches_res = Array.map3 (fun x y z -> (x, y, z))
    branches_ty branches_nb branches_subst in

  (* ===== RESULT ===== *)
  let to_apply = cut_vars @ to_apply in
   (* We have everything we need:
   *  - a context [ctx'];
   *  - a return type [goal] valid under [ctx'];
   *  - the type of the branches of the case;
   *  - the number of arguments of each constructor;
   *  - a context_map for each branch;
   *  - a number of cuts [nb_cuts];
   *  - a reverse substitution [rev_subst_without_cuts] from [ctx] to [ctx'];
   *  - some terms in [ctx] to apply to the case once it is built. *)
      (ctx', goal, branches_res, nb_cuts, rev_subst_without_cuts, to_apply, simpl)
