(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Cases
open Util
open Errors
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
open Errors
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
open Decl_kinds

open Equations_common
open Depelim


let mkcase env c ty constrs =
  let cty = Retyping.get_type_of env Evd.empty c in
  let ind, origargs = decompose_app cty in
  let mind, ind = match kind_of_term ind with
    | Ind ((mu, n),_ as i) -> mu, i
    | _ -> assert false
  in
  let mindb, oneind = Global.lookup_inductive (fst ind) in
  let inds = List.rev (Array.to_list (Array.mapi (fun i oib -> mkIndU ((mind, i),snd ind)) mindb.mind_packets)) in
  let ctx = oneind.mind_arity_ctxt in
  let _len = List.length ctx in
  let params = mindb.mind_nparams in
  let origparams, _ = List.chop params origargs in
  let ci = make_case_info env (fst ind) RegularStyle in
  let brs = 
    Array.map2_i (fun i id cty ->
      let (args, arity) = decompose_prod_assum (substl inds cty) in
      let realargs, pars = List.chop (List.length args - params) args in
      let args = substl (List.rev origparams) (it_mkProd_or_LetIn arity realargs) in
      let args, arity = decompose_prod_assum args in
      let res = constrs ind i id params args arity in
	it_mkLambda_or_LetIn res args)
      oneind.mind_consnames oneind.mind_nf_lc
  in
    mkCase (ci, ty, c, brs)

let mk_eq env evd args args' indty = 
  let _, _, make = Sigma.telescope evd args in
  let _, _, make' = Sigma.telescope evd args' in
  let make = lift (List.length args + 1) make in
  let ty = Retyping.get_type_of env !evd make in
  mkEq evd ty make make'

let derive_no_confusion env evd (ind,u) =
  let evd = ref evd in
  let poly = Flags.is_universe_polymorphism () in
  let mindb, oneind = Global.lookup_inductive ind in
  let ctx = subst_instance_context u oneind.mind_arity_ctxt in
  let len = List.length ctx in
  let params = mindb.mind_nparams in
  let args = oneind.mind_nrealargs in
  let argsvect = rel_vect 0 len in
  let paramsvect, rest = Array.chop params argsvect in
  let indty = mkApp (mkInd ind, argsvect) in
  let tru = Universes.constr_of_global (Lazy.force (get_one ())) in
  let fls = Universes.constr_of_global (Lazy.force (get_zero ())) in
  let xid = id_of_string "x" and yid = id_of_string "y" in
  let xdecl = (Name xid, None, indty) in
  let binders = xdecl :: ctx in
  let ydecl = (Name yid, None, lift 1 indty) in
  let fullbinders = ydecl :: binders in
  let s = Evarutil.evd_comb1 (Evd.fresh_sort_in_family env) evd (get_sort ()) in
  let s = mkSort s in
  let arity = it_mkProd_or_LetIn s fullbinders in
  let env = push_rel_context binders env in
  let ind_with_parlift n =
    mkApp (mkInd ind, Array.append (Array.map (lift n) paramsvect) rest) 
  in
  let lenargs = List.length ctx - params in
  let pred =
    let elim =
      let app = ind_with_parlift (args + 1) in
	it_mkLambda_or_LetIn 
	  (mkProd_or_LetIn (Anonymous, None, lift 1 app) s)
	  ((Name xid, None, ind_with_parlift (1 + lenargs)) :: List.firstn lenargs ctx)
    in
      mkcase env (mkRel 1) elim (fun ind i id nparams args arity ->
	let ydecl = (Name yid, None, arity) in
	let env' = push_rel_context (ydecl :: args) env in
	let decl = (Name yid, None, ind_with_parlift (lenargs + List.length args + 2)) in
	  mkLambda_or_LetIn ydecl
	    (mkcase env' (mkRel 1) 
		(it_mkLambda_or_LetIn s (decl :: List.firstn lenargs ctx))
		(fun _ i' id' nparams args' arity' ->
		  if i = i' then 
		    if List.length args = 0 then tru
		    else mk_eq (push_rel_context args' env') evd args args' indty
		  else fls)))
  in
  let app = it_mkLambda_or_LetIn pred binders in
  let ce = make_definition ~poly evd ~types:arity app in
  let indid = Nametab.basename_of_global (IndRef ind) in
  let id = add_prefix "NoConfusion_" indid
  and noid = add_prefix "noConfusion_" indid
  and packid = add_prefix "NoConfusionPackage_" indid in
  let cstNoConf = Declare.declare_constant id (DefinitionEntry ce, IsDefinition Definition) in
  let evd = ref (Evd.from_env (Global.env ())) in
  let tc = Typeclasses.class_info (Lazy.force coq_noconfusion_class) in
  let noconf = Evarutil.e_new_global evd (ConstRef cstNoConf) in
  let noconfcl = Evarutil.e_new_global evd tc.Typeclasses.cl_impl in
  let inst, u = destInd noconfcl in
  let noconfterm = mkApp (noconf, argsvect) in
  let b, ty = 
    Typeclasses.instance_constructor (tc,u) [indty; noconfterm]
  in
  let env = push_rel_context ctx (Global.env ()) in
  let rec term c ty =
    match kind_of_term ty with
    | Prod (na, t, ty) ->
       let arg = Evarutil.e_new_evar env evd t in
       term (mkApp (c, [|arg|])) (subst1 arg ty)
    | _ -> c, ty
  in
  let cty = Retyping.get_type_of env !evd (Option.get b) in
  let term, ty = term (Option.get b) cty in
  let term = it_mkLambda_or_LetIn term ctx in
  let ty = it_mkProd_or_LetIn ty ctx in
  let _ = Typing.e_type_of env evd term in
  let hook vis gr _ectx = 
    Typeclasses.add_instance
      (Typeclasses.new_instance tc None true poly gr)
  in
  let oblinfo, _, term, ty = Obligations.eterm_obligations env noid !evd 0 term ty in
    ignore(Obligations.add_definition ~hook:(Lemmas.mk_hook hook) packid 
	      ~term ty ~tactic:(noconf_tac ()) 
	      (Evd.evar_universe_context !evd) oblinfo)
