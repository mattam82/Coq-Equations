(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
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
open Errors
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
              aux (push_rel (n, None, b) env) p2 args.(3) t
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
  | [(n, None, t)] -> t, [n, Some (mkRel 1), lift 1 t], mkRel 1
  | (n, None, t) :: tl ->
      let len = succ (List.length tl) in
      let ty, tys =
	List.fold_left
	  (fun (ty, tys) (n, b, t) ->
	    let pred = mkLambda (n, t, ty) in
	    let sigty = mkAppG evd (Lazy.force coq_sigma) [|t; pred|] in
	      (sigty, pred :: tys))
	  (t, []) tl
      in
      let constr, _ = 
	List.fold_right (fun pred (intro, k) ->
	  let pred = Vars.lift k pred in
	  let (n, dom, codom) = destLambda pred in
	  let intro = mkAppG evd (Lazy.force coq_sigmaI) [| dom; pred; mkRel k; intro|] in
	    (intro, succ k))
	  tys (mkRel 1, 2)
      in
      let (last, _, subst) = List.fold_right2
	(fun pred (n, b, t) (prev, k, subst) ->
	  let proj1 = mkProj (Lazy.force coq_pr1, prev) in
	  let proj2 = mkProj (Lazy.force coq_pr2, prev) in
	    (lift 1 proj2, succ k, (n, Some proj1, liftn 1 k t) :: subst))
	(List.rev tys) tl (mkRel 1, 1, [])
      in ty, ((n, Some last, liftn 1 len t) :: subst), constr

  | _ -> raise (Invalid_argument "telescope")

let sigmaize ?(liftty=0) env0 evd pars f =
  let env = push_rel_context pars env0 in
  let ty = Retyping.get_type_of env !evd f in
  let ctx, concl = decompose_prod_assum ty in
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
     (Equations_common.proper_tails (map (fun (_, b, _) -> Option.get b) letbinders)))
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
  let evd, c = Evarutil.new_global evd (Lazy.force signature_ref) in
    evd, fst (snd (Option.get (Typeclasses.class_of_constr c)))

let build_sig_of_ind env sigma (ind,u as indu) =
  let (mib, oib as _mind) = Global.lookup_inductive ind in
  let ctx = inductive_alldecls indu in
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

let declare_sig_of_ind env ind =
  let sigma = Evd.from_env env in
  let sigma, (ind, u) = Evd.fresh_inductive_instance env sigma ind in
  let sigma, pred, pars, fullapp, valsig, ctx, lenargs, idx =
    build_sig_of_ind env sigma (ind, u) in
  let indid = ind_name ind in
  let simpl = Tacred.simpl env sigma in
  let poly = Flags.is_universe_polymorphism () in
  let indsig = 
    let indsigid = add_suffix indid "_sig" in
      declare_constant indsigid pred
	None poly sigma (IsDefinition Definition)
  in
  (* let sigma = if not poly then Evd.from_env (Global.env ()) else sigma in *)
  let pack_fn = 
    let vbinder = (Name (add_suffix indid "_var"), None, fullapp) in
    let term = it_mkLambda_or_LetIn valsig (vbinder :: ctx) 
    in
    let packid = add_suffix indid "_sig_pack" in
    (* let rettype = mkApp (mkConst indsig, extended_rel_vect (succ lenargs) pars) in *)
      declare_constant packid (simpl term)
	None (* (Some (it_mkProd_or_LetIn rettype (vbinder :: ctx))) *)
	poly sigma
	(IsDefinition Definition)
  in
  let sigma = if not poly then Evd.from_env (Global.env ()) else sigma in
  let sigma, c = signature_class sigma in
  let env = Global.env () in
  let sigma, indsig = Evd.fresh_global env sigma (ConstRef indsig) in
  let sigma, pack_fn = Evd.fresh_global env sigma (ConstRef pack_fn) in
  let inst = 
    declare_instance (add_suffix indid "_Signature")
      poly sigma ctx c
      [fullapp; lift lenargs idx;
       mkApp (indsig, extended_rel_vect lenargs pars);
       mkApp (pack_fn, extended_rel_vect 0 ctx)]
  in inst

let get_signature env sigma ty =
  try
    let sigma', (idx, _) = 
      new_type_evar env sigma Evd.univ_flexible ~src:(dummy_loc, Evar_kinds.InternalHole) in
    let _idxev = fst (destEvar idx) in
    let sigma', cl = Evarutil.new_global sigma' (Lazy.force signature_ref) in
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
    msg_warning (str "Automatically inlined signature for type " ++
    Printer.pr_pinductive env pind ++ str ". Use [Derive Signature for " ++
    Printer.pr_pinductive env pind ++ str ".] to avoid this.");
    let indsig = pred in
    let vbinder = (Anonymous, None, ty) in
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

let pattern_sigma c hyp env sigma =
  let evd = ref sigma in
  let terms = constrs_of_coq_sigma env evd c (mkVar hyp) in
  let terms = 
    match terms with
    | (x, t, p, rest) :: term :: _ -> 
	constrs_of_coq_sigma env evd t p @ terms
    | _ -> terms
  in
  let pat = Patternops.pattern_of_constr env !evd in
  let terms = 
    match terms with
    | (x, t, p, rest) :: _ :: _ -> terms @ constrs_of_coq_sigma env evd t p 
    | _ -> terms
  in
  let projs = map (fun (x, t, p, rest) -> (pat t, make_change_arg p)) terms in
  let projabs = tclTHENLIST (map (fun (t, p) -> change (Some t) p Locusops.onConcl) projs) in
    Proofview.V82.tactic (tclTHEN (Refiner.tclEVARS !evd) projabs)
			 
let curry_hyp env sigma c t =
  let aux c t na u ty pred concl =
    let (n, idx, dom) = destLambda pred in
    let newctx = [(na, None, dom); (n, None, idx)] in
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
	   let term = nf_beta sigma c in
	     Some (term, t))
    | _ -> None
  in curry c t
