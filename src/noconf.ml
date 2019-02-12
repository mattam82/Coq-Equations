(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Util
open Names
open Nameops
open Constr
open Declarations
open Inductiveops
open Globnames
open Reductionops
open Entries
open Vars
open Decl_kinds

open Equations_common
open EConstr
open Vars

let mkcase env sigma c ty constrs =
  let cty = Retyping.get_type_of env sigma c in
  let indf, origargs = find_rectype env sigma cty in
  let mind, ind, origparams = match dest_ind_family indf with
    | (((mu, n),_ as i), pars) -> mu, i, pars
  in
  let mindb, oneind = Global.lookup_inductive (fst ind) in
  let inds = List.rev (Array.to_list (Array.mapi
                                      (fun i oib ->
                                      mkIndU ((mind, i),snd ind)) mindb.mind_packets)) in
  let ctx = oneind.mind_arity_ctxt in
  let _len = List.length ctx in
  let params = mindb.mind_nparams in
  let ci = make_case_info env (fst ind) RegularStyle in
  let brs = 
    Array.map2_i (fun i id cty ->
      let (args, arity) = decompose_prod_assum sigma (substl inds (of_constr cty)) in
      let realargs, pars = List.chop (List.length args - params) args in
      let args = substl (List.rev origparams) (it_mkProd_or_LetIn arity realargs) in
      let args, arity = decompose_prod_assum sigma args in
      let res = constrs ind i id params args arity in
      it_mkLambda_or_LetIn res args)
      oneind.mind_consnames oneind.mind_nf_lc
  in
    make_case_or_project env sigma indf ci ty c brs

let mk_eq env evd args args' =
  let _, _, make = Sigma_types.telescope evd args in
  let _, _, make' = Sigma_types.telescope evd args' in
  let make = lift (List.length args + 1) make in
  let ty = Retyping.get_type_of env !evd make in
  mkEq env evd ty make make'

let derive_no_confusion env evd ~polymorphic (ind,u as indu) =
  let evd = ref evd in
  let mindb, oneind = Global.lookup_inductive ind in
  let ctx = subst_instance_context (EInstance.kind !evd u) oneind.mind_arity_ctxt in
  let ctx = List.map of_rel_decl ctx in
  let ctx = smash_rel_context !evd ctx in
  let len = List.length ctx in
  let params = mindb.mind_nparams in
  let args = oneind.mind_nrealargs in
  let argsvect = rel_vect 0 len in
  let paramsvect, rest = Array.chop params argsvect in
  let argty, x, ctx, argsctx =
    if Array.length rest = 0 then
      mkApp (mkIndU indu, argsvect), mkRel 1, ctx, []
    else
      let evm, pred, pars, indty, valsig, ctx, lenargs, idx =
        Sigma_types.build_sig_of_ind env !evd indu
      in
      let () = evd := evm in
      let evm, sigma = Evarutil.new_global !evd (Lazy.force coq_sigma) in
      let () = evd := evm in
      let _, pred' = Term.decompose_lam_n (List.length pars) (EConstr.to_constr !evd pred) in
      let indty = mkApp (sigma, [|idx; of_constr pred'|]) in
      nf_betaiotazeta env !evd indty, mkProj (Lazy.force coq_pr2, mkRel 1), pars, (List.firstn lenargs ctx)
  in
  let tru = get_efresh logic_top evd in
  let fls = get_efresh logic_bot evd in
  let xid = Id.of_string "x" and yid = Id.of_string "y" in
  let xdecl = of_tuple (Name xid, None, argty) in
  let binders = xdecl :: ctx in
  let ydecl = of_tuple (Name yid, None, lift 1 argty) in
  let fullbinders = ydecl :: binders in
  let s = Equations_common.evd_comb1 Evd.fresh_sort_in_family evd (Lazy.force logic_sort) in
  let s = mkSort s in
  let arity = it_mkProd_or_LetIn s fullbinders in
  let env = push_rel_context binders env in
  let paramsvect = Context.Rel.to_extended_vect mkRel 0 ctx in
  let pack_ind_with_parlift n = lift n argty in
  let ind_with_parlift n = 
    mkApp (mkIndU indu, Array.append (Array.map (lift n) paramsvect) rest) 
  in
  let lenindices = List.length argsctx in
  let pred =
    let elim =
      (* In pars ; x |- fun args (x : ind pars args) => forall y, Prop *)
      let app = pack_ind_with_parlift (args + 2) in
	it_mkLambda_or_LetIn 
	  (mkProd_or_LetIn (of_tuple (Anonymous, None, app)) s)
	  (of_tuple (Name xid, None, ind_with_parlift (lenindices + 1)) ::
             lift_rel_context 1 argsctx)
    in
      mkcase env !evd x elim (fun ind i id nparams args arity ->
	let ydecl = (Name yid, None, pack_ind_with_parlift (List.length args + 1)) in
        let env' = push_rel_context (of_tuple ydecl :: args) env in
        let argsctx = lift_rel_context (List.length args + 2) argsctx in
	let elimdecl = (Name yid, None, ind_with_parlift (List.length args + lenindices + 2)) in
	  mkLambda_or_LetIn (of_tuple ydecl)
            (mkcase env' !evd x
	        (it_mkLambda_or_LetIn s (of_tuple elimdecl :: argsctx))
	        (fun _ i' id' nparams args' arity' ->
	          if i = i' then
	            if List.length args = 0 then tru
	            else mk_eq (push_rel_context args' env') evd args args'
	          else fls)))
  in
  let app = it_mkLambda_or_LetIn pred binders in
  let _, ce = make_definition ~poly:polymorphic !evd ~types:arity app in
  let indid = Nametab.basename_of_global (IndRef ind) in
  let id = add_prefix "NoConfusion_" indid
  and noid = add_prefix "noConfusion_" indid
  and packid = add_prefix "NoConfusionPackage_" indid in
  let cstNoConf = Declare.declare_constant id (DefinitionEntry ce, IsDefinition Definition) in
  let env = Global.env () in
  let evd = ref (Evd.from_env env) in
  let tc = Typeclasses.class_info (Lazy.force coq_noconfusion_class) in
  let noconf = e_new_global evd (ConstRef cstNoConf) in
  let noconfcl = e_new_global evd tc.Typeclasses.cl_impl in
  let inst, u = destInd !evd noconfcl in
  let noconfterm = mkApp (noconf, paramsvect) in
  let ctx, argty =
    let ty = Retyping.get_type_of env !evd noconf in
    let ctx, ty = EConstr.decompose_prod_n_assum !evd params ty in
    match kind !evd ty with
    | Prod (_, b, _) -> ctx, b
    | _ -> assert false
  in
  let b, ty = 
    Equations_common.instance_constructor !evd (tc,u) [argty; noconfterm]
  in
  let env = push_rel_context ctx (Global.env ()) in
  let rec term c ty =
    match kind !evd ty with
    | Prod (na, t, ty) ->
       let arg = Equations_common.evd_comb1 (Evarutil.new_evar env) evd t in
       term (mkApp (c, [|arg|])) (subst1 arg ty)
    | _ -> c, ty
  in
  let cty = Retyping.get_type_of env !evd (Option.get b) in
  let term, ty = term (Option.get b) cty in
  let term = it_mkLambda_or_LetIn term ctx in
  let ty = it_mkProd_or_LetIn ty ctx in
  let _ = Equations_common.evd_comb1 (Typing.type_of env) evd term in
  let hook _ectx _evars vis gr =
    Typeclasses.add_instance
      (Typeclasses.new_instance tc empty_hint_info true gr)
  in
  let kind = (Global, polymorphic, Definition) in
  let oblinfo, _, term, ty = Obligations.eterm_obligations env noid !evd 0
      (to_constr ~abort_on_undefined_evars:false !evd term)
      (to_constr !evd ty) in
    ignore(Obligations.add_definition ~hook:(Lemmas.mk_hook hook) packid
             ~kind ~term ty ~tactic:(noconf_tac ())
	      (Evd.evar_universe_context !evd) oblinfo)

let () =
  Ederive.(register_derive
            { derive_name = "NoConfusion";
              derive_fn = make_derive_ind derive_no_confusion })
