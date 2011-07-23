(* -*- compile-command: "make -k -C .. src/equations_plugin.cma src/equations_plugin.cmxs" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $Id: equations.ml4 11996 2009-03-20 01:22:58Z letouzey $ *)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Sign
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

open Tactics
open Refiner
open Tacticals
open Tacmach

open Equations_common

let coq_sigma = Lazy.lazy_from_fun Coqlib.build_sigma_type

let mkSig (n, c, t) =
  mkApp ((Lazy.force coq_sigma).Coqlib.typ, [| c; mkLambda (n, c, t) |])

let constrs_of_coq_sigma env sigma t alias = 
  let s = Lazy.force coq_sigma in
  let rec aux proj c ty =
    match kind_of_term c with
    | App (f, args) when eq_constr f s.Coqlib.intro && 
	Array.length args = 4 -> 
	(match kind_of_term args.(1) with
	| Lambda (n, b, t) ->
	    let projargs = [| args.(0); args.(1); proj |] in
	    let p1 = mkApp (s.Coqlib.proj1, projargs) in
	    let p2 = mkApp (s.Coqlib.proj2, projargs) in
	      (n, args.(2), p1, args.(0)) :: aux p2 args.(3) t
	| _ -> raise (Invalid_argument "constrs_of_coq_sigma"))
    | _ -> [(Anonymous, c, proj, ty)]
  in aux alias t (Typing.type_of env sigma t)

let decompose_coq_sigma t = 
  let s = Lazy.force coq_sigma in
    match kind_of_term t with
    | App (f, args) when eq_constr f s.Coqlib.typ && 
	Array.length args = 2 -> Some (args.(0), args.(1))
    | _ -> None

let decompose_indapp f args =
  match kind_of_term f with
  | Construct (ind,_) 
  | Ind ind ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = array_chop first args in
	mkApp (f, pars), args
  | _ -> f, args


let sigT = Lazy.lazy_from_fun build_sigma_type
let sigT_info = lazy
  { ci_ind         = destInd (Lazy.force sigT).typ;
    ci_npar        = 2;
    ci_cstr_ndecls = [|2|];
    ci_pp_info     =  { ind_nargs = 0; style = LetStyle }
  }

let telescope = function
  | [] -> assert false
  | [(n, None, t)] -> t, [n, Some (mkRel 1), t], mkRel 1
  | (n, None, t) :: tl ->
      let len = succ (List.length tl) in
      let ty, tys =
	List.fold_left
	  (fun (ty, tys) (n, b, t) ->
	    let pred = mkLambda (n, t, ty) in
	    let sigty = mkApp ((Lazy.force sigT).typ, [|t; pred|]) in
	      (sigty, pred :: tys))
	  (t, []) tl
      in
      let constr, _ = 
	List.fold_right (fun pred (intro, k) ->
	  let pred = lift k pred in
	  let (n, dom, codom) = destLambda pred in
	  let intro = mkApp ((Lazy.force sigT).intro, [| dom; pred; mkRel k; intro|]) in
	    (intro, succ k))
	  tys (mkRel 1, 2)
      in
      let (last, _, subst) = List.fold_right2
	(fun pred (n, b, t) (prev, k, subst) ->
	  let proj1 = applistc (Lazy.force sigT).proj1 [liftn 1 k t; liftn 1 k pred; prev] in
	  let proj2 = applistc (Lazy.force sigT).proj2 [liftn 1 k t; liftn 1 k pred; prev] in
	    (lift 1 proj2, succ k, (n, Some proj1, liftn 1 k t) :: subst))
	(List.rev tys) tl (mkRel 1, 1, [])
      in ty, ((n, Some last, liftn 1 len t) :: subst), constr

  | _ -> raise (Invalid_argument "telescope")

let sigmaize ?(liftty=0) env sigma f =
  let ty = Retyping.get_type_of env sigma f in
  let ctx, concl = decompose_prod_assum ty in
  let argtyp, letbinders, make = telescope ctx in
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
  let tysig = mkApp ((Lazy.force coq_sigma).typ, tyargs) in
  let indexproj = mkApp ((Lazy.force coq_sigma).proj1, tyargs) in
  let valproj = mkApp ((Lazy.force coq_sigma).proj2, tyargs) in
  let indices = 
    list_map_i (fun i (_, b, _) -> lift (-i) (Option.get b)) 0 (List.rev letbinders)
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
      mkApp ((Lazy.force coq_sigma).intro,
	    [|argtyp; pred; lift 1 make; mkRel 1|])
  in argtyp, pred, indices, indexproj, valproj, valsig, tysig

let ind_name ind = Nametab.basename_of_global (IndRef ind)

open Decl_kinds

let signature_ref = lazy (init_constant ["Equations";"Signature"] "Signature")
let signature_sig = lazy (init_constant ["Equations";"Signature"] "signature")
let signature_pack = lazy (init_constant ["Equations";"Signature"] "signature_pack")

let signature_class () =
  fst (snd (Option.get (Typeclasses.class_of_constr (Lazy.force signature_ref))))

let declare_sig_of_ind env ind =
  let sigma = Evd.empty in
  let (mib, oib as _mind) = Global.lookup_inductive ind in
  let ctx = oib.Declarations.mind_arity_ctxt in
  let lenpars = mib.mind_nparams_rec in
  let lenargs = List.length ctx - lenpars in
  if lenargs = 0 then
    user_err_loc (dummy_loc, "Derive Signature", 
		 str"No signature to derive for non-dependent inductive types");
  let args, pars = list_chop lenargs ctx in
  let parapp = mkApp (mkInd ind, extended_rel_vect 0 pars) in
  let fullapp = mkApp (mkInd ind, extended_rel_vect 0 ctx) in
  let idx, pred, _, _, _, valsig, _ = 
    sigmaize (push_rel_context pars env) sigma parapp 
  in
  let indid = ind_name ind in
  let simpl = Tacred.simpl env sigma in
  let indsig = 
    let indsigid = add_suffix indid "_sig" in
      declare_constant indsigid (it_mkLambda_or_LetIn pred pars)
	None (IsDefinition Definition)
  in
  let pack_fn = 
    let vbinder = (Name (add_suffix indid "_var"), None, fullapp) in
    let term = it_mkLambda_or_LetIn valsig (vbinder :: ctx) 
    in
    let packid = add_suffix indid "_sig_pack" in
    (* let rettype = mkApp (mkConst indsig, extended_rel_vect (succ lenargs) pars) in *)
      declare_constant packid (simpl term)
	None (* (Some (it_mkProd_or_LetIn rettype (vbinder :: ctx))) *)
	(IsDefinition Definition)
  in
  let inst = 
    declare_instance (add_suffix indid "_Signature")
      ctx (signature_class ()) 
      [fullapp; lift lenargs idx; mkApp (mkConst indsig, extended_rel_vect lenargs pars);
       mkApp (mkConst pack_fn, extended_rel_vect 0 ctx)]
  in inst

VERNAC COMMAND EXTEND Derive_Signature
| [ "Derive" "Signature" "for" constr(c) ] -> [ 
  let c' = Constrintern.interp_constr Evd.empty (Global.env ()) c in
    match kind_of_term c' with
    | Ind i -> ignore(declare_sig_of_ind (Global.env ()) i)
    | _ -> error "Expected an inductive type"
  ]
END

let get_signature env sigma ty =
  let sigma', idx = new_evar sigma env ~src:(dummy_loc, Evd.InternalHole) (new_Type ()) in
  let _idxev = fst (destEvar idx) in
  let inst = mkApp (Lazy.force signature_ref, [| ty; idx |]) in
  let sigma', tc =
    try Typeclasses.resolve_one_typeclass env sigma' inst 
    with Not_found ->
      let _ = declare_sig_of_ind env (fst (Inductive.find_rectype env ty)) in
	Typeclasses.resolve_one_typeclass env sigma' inst
  in
    (nf_evar sigma' (mkApp (Lazy.force signature_sig, [| ty; idx; tc |])),
    nf_evar sigma' (mkApp (Lazy.force signature_pack, [| ty; idx; tc |])))
      
TACTIC EXTEND get_signature_pack
[ "get_signature_pack" hyp(id) ident(id') ] -> [ fun gl ->
  let sigsig, sigpack = get_signature (pf_env gl) (project gl) (pf_get_hyp_typ gl id) in
    letin_tac None (Name id') (mkApp (sigpack, [| mkVar id |])) None nowhere gl ]
END

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

let pattern_sigma c hyp gl =
  let terms = constrs_of_coq_sigma (pf_env gl) (project gl) c (mkVar hyp) in
  let terms = 
    match terms with
    | (x, t, p, rest) :: term :: _ -> 
	constrs_of_coq_sigma (pf_env gl) (project gl) t p @ terms
    | _ -> terms
  in
  let pat = Pattern.pattern_of_constr (project gl) in
  let terms = 
    match terms with
    | (x, t, p, rest) :: _ :: _ -> terms @ constrs_of_coq_sigma (pf_env gl) (project gl) t p 
    | _ -> terms
  in
  let projs = map (fun (x, t, p, rest) -> (snd (pat t), p)) terms in
  let projabs = tclTHENLIST (map (fun (t, p) -> change (Some t) p onConcl) projs) in
    projabs gl
      
TACTIC EXTEND pattern_sigma
[ "pattern" "sigma" hyp(id) ] -> [ fun gl ->
  let term = Option.get (pi2 (pf_get_hyp gl id)) in
    pattern_sigma term id gl ]
END

let curry_hyp c t =
  let na, dom, concl = destProd t in
    match decompose_coq_sigma dom with
    | None -> None
    | Some (ty, pred) ->
	let (n, idx, dom) = destLambda pred in
	let newctx = [(na, None, dom); (n, None, idx)] in
	let tuple = mkApp ((Lazy.force coq_sigma).intro,
			  [| lift 2 ty; lift 2 pred; mkRel 2; mkRel 1 |])
	in
	let term = it_mkLambda_or_LetIn (mkApp (c, [| tuple |])) newctx in
	let typ = it_mkProd_or_LetIn (subst1 tuple concl) newctx in
	  Some (term, typ)
	    
TACTIC EXTEND curry
[ "curry" hyp(id) ] -> [ fun gl ->
  match curry_hyp (mkVar id) (pf_get_hyp_typ gl id) with
  | Some (prf, typ) -> 
      cut_replacing id typ (Tacmach.refine_no_check prf) gl
  | None -> tclFAIL 0 (str"No currying to do in" ++ pr_id id) gl ]
END

(* TACTIC EXTEND pattern_tele *)
(* [ "pattern_tele" constr(c) ident(hyp) ] -> [ fun gl -> *)
(*   let settac = letin_tac None (Name hyp) c None onConcl in *)
(*     tclTHENLIST [settac; pattern_sigma c hyp] gl ] *)
(* END *)
