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

let mk_eqs env evd args args' pv = 
  let prf =
    List.fold_right2 (fun x y c -> 
      let tyx = Retyping.get_type_of env Evd.empty x 
      and tyy = Retyping.get_type_of env Evd.empty y in
      let hyp, prf = mk_term_eq env evd tyx x tyy y in
	mkProd (Anonymous, hyp, lift 1 c))
      args args' pv
  in mkProd (Anonymous, prf, pv)
	
let derive_no_confusion env evd (ind,u) =
  let evd = ref evd in
  let poly = Flags.is_universe_polymorphism () in
  let mindb, oneind = Global.lookup_inductive ind in
  let ctx = (* map_rel_context refresh_universes *) oneind.mind_arity_ctxt in
  let len = List.length ctx in
  let params = mindb.mind_nparams in
  let args = oneind.mind_nrealargs in
  let argsvect = rel_vect 0 len in
  let paramsvect, rest = Array.chop params argsvect in
  let indty = mkApp (mkInd ind, argsvect) in
  let pid = (id_of_string "P") in
  let pvar = mkVar pid in
  let xid = id_of_string "x" and yid = id_of_string "y" in
  let xdecl = (Name xid, None, lift 1 indty) in
  let pty = e_new_Type env evd in
  let binders = xdecl :: (Name pid, None, pty) :: ctx in
  let ydecl = (Name yid, None, lift 2 indty) in
  let fullbinders = ydecl :: binders in
  let arity = it_mkProd_or_LetIn pty fullbinders in
  let env = push_rel_context binders env in
  let ind_with_parlift n =
    mkApp (mkInd ind, Array.append (Array.map (lift n) paramsvect) rest) 
  in
  let lenargs = List.length ctx - params in
  let pred =
    let elim =
      let app = ind_with_parlift (args + 2) in
	it_mkLambda_or_LetIn 
	  (mkProd_or_LetIn (Anonymous, None, lift 1 app) pty)
	  ((Name xid, None, ind_with_parlift (2 + lenargs)) :: List.firstn lenargs ctx)
    in
      mkcase env (mkRel 1) elim (fun ind i id nparams args arity ->
	let ydecl = (Name yid, None, arity) in
	let env' = push_rel_context (ydecl :: args) env in
	let decl = (Name yid, None, ind_with_parlift (lenargs + List.length args + 3)) in
	  mkLambda_or_LetIn ydecl
	    (mkcase env' (mkRel 1) 
		(it_mkLambda_or_LetIn pty (decl :: List.firstn lenargs ctx))
		(fun _ i' id' nparams args' arity' ->
		  if i = i' then 
		    mk_eqs (push_rel_context args' env') evd
		      (rel_list (List.length args' + 1) (List.length args))
		      (rel_list 0 (List.length args')) pvar
		  else pvar)))
  in
  let app = it_mkLambda_or_LetIn (replace_vars [(pid, mkRel 2)] pred) binders in
  let ce = make_definition ~poly evd ~types:arity app in
  let indid = Nametab.basename_of_global (IndRef ind) in
  let id = add_prefix "NoConfusion_" indid
  and noid = add_prefix "noConfusion_" indid
  and packid = add_prefix "NoConfusionPackage_" indid in
  let cstNoConf = Declare.declare_constant id (DefinitionEntry ce, IsDefinition Definition) in
  let stmt = it_mkProd_or_LetIn
    (mkApp (mkConst cstNoConf, rel_vect 1 (List.length fullbinders)))
    ((Anonymous, None, mkEq evd (lift 3 indty) (mkRel 2) (mkRel 1)) :: fullbinders)
  in
  let hook vis gr = 
    let evd = ref (Evd.from_env (Global.env ())) in
    let tc = Typeclasses.class_info (global_of_constr (Lazy.force coq_noconfusion_class)) in
    let b, ty = Typeclasses.instance_constructor (tc,Univ.Instance.empty)
      [indty; mkApp (mkConst cstNoConf, argsvect) ; 
       mkApp (Universes.constr_of_global gr, argsvect) ] in
    match b with
      | Some b ->
        let ce = make_definition ~poly evd ~types:(it_mkProd_or_LetIn ty ctx)
	  (it_mkLambda_or_LetIn b ctx)
        in
        let inst = Declare.declare_constant packid (DefinitionEntry ce, IsDefinition Instance) in
        Typeclasses.add_instance (Typeclasses.new_instance tc None true poly (ConstRef inst))
      | None -> error "Could not find constructor"
  in
    ignore(Obligations.add_definition ~hook:(Lemmas.mk_hook hook) noid 
	      stmt ~tactic:(noconf_tac ()) 
	      (Evd.empty_evar_universe_context) [||])
