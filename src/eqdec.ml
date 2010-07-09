(* -*- compile-command: "COQBIN=~/research/coq/trunk/bin/ make -k -C .. src/equations_plugin.cma src/equations_plugin.cmxs" -*- *)
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

(* 
   Statements: forall Δ, EqDec Δ -> EqDec (I Δ)
   Proofs:
   intros; intro x y; depind x; depelim y.
   { c ts = c us } + { c ts <> c us }.
   Takes ts, us and recurse:
   case (eq_dec t u) ; [ rec ts us | right; intro Heq; noconf Heq; apply Hneq; reflexivity ]

*)


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

open Rawterm
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Util
open Entries

open Equations_common
open Sigma

type one_inductive_info = {
  ind_name : identifier;
  ind_c : constr; (* Inductive type, applied to parameters (named variables) *)
  ind_args : rel_context; (* Arguments, as a rel_context typed in env with named variables *)
  ind_constr : (rel_context * types) array; (* Constructor types as a context and an arity,
					       with parameters instantiated by variables *)
  ind_case : constr -> types -> constr array -> constr; 
  (* Case construct closure taking the target, predicate and branches *)
}

type mutual_inductive_info = {
  mutind_params : named_context; (* Mutual parameters as a named context *)
  mutind_inds : one_inductive_info array; (* Each inductive. *)
}

let named_of_rel_context l =
  let acc, args, ctx =
    List.fold_right
      (fun (na, b, t) (subst, args, ctx) ->
	let id = match na with Anonymous -> id_of_string "param" | Name id -> id in
	let d = (id, Option.map (substl subst) b, substl subst t) in
	let args = if b = None then mkVar id :: args else args in
	  (mkVar id :: subst, args, d :: ctx))
      l ([], [], [])
  in acc, rev args, ctx

let subst_rel_context k cstrs ctx = 
  let (_, ctx') = fold_right 
    (fun (id, b, t) (k, ctx') ->
      (succ k, (id, Option.map (substnl cstrs k) b, substnl cstrs k t) :: ctx'))
    ctx (k, [])
  in ctx'
    
let inductive_info (mind, _ as ind) =
  let mindb, oneind = Global.lookup_inductive ind in
  let subst, paramargs, params = named_of_rel_context mindb.mind_params_ctxt in
  let nparams = List.length params in
  let env = List.fold_right push_named params (Global.env ()) in
  let info_of_ind i ind =
    let ctx = ind.mind_arity_ctxt in
    let args, _ = list_chop ind.mind_nrealargs_ctxt ctx in
    let args' = subst_rel_context 0 subst args in
    let induct = (mind, i) in
    let indname = Nametab.basename_of_global (IndRef induct) in
    let indapp = applist (mkInd induct, paramargs) in    
    let arities = arities_of_constructors env induct in
     let constrs =
      Array.map (fun ty -> 
	let _, rest = decompose_prod_n_assum nparams ty in
	let constrty = substl subst rest in
	  decompose_prod_assum constrty)
	arities
    in
    let case c pred brs =
      let ci = {
	ci_ind = induct;
	ci_npar = List.length paramargs;
	ci_cstr_ndecls = ind.mind_consnrealdecls;
	ci_pp_info = { ind_nargs = ind.mind_nrealargs; style = RegularStyle; } }
      in
	mkCase (ci, pred, c, brs)
    in
      { ind_name = indname;
	ind_c = indapp; ind_args = args';
	ind_constr = constrs;
	ind_case = case }
  in
  let inds = Array.mapi info_of_ind mindb.mind_packets in
    { mutind_params = params;
      mutind_inds = inds }
    
let eq_dec_class () =
  Option.get 
    (Typeclasses.class_of_constr
	(init_constant ["Equations";"EqDec"] "EqDec"))

let dec_eq () =
  init_constant ["Equations";"EqDec"] "dec_eq"

open Decl_kinds

let derive_eq_dec ind =
  let info = inductive_info ind in
  let ctx = info.mutind_params in
  let _cl = eq_dec_class () in
  let stmt_of ind =
    let indapp = mkApp (ind.ind_c, extended_rel_vect 0 ind.ind_args) in
    let app = 
      mkApp (dec_eq (), [| indapp |])
    in
    let app = 
      let xname = Name (id_of_string "x") in
      let yname = Name (id_of_string "y") in
	mkProd (xname, indapp,
	       mkProd (yname, lift 1 indapp,
  		      mkApp (lift 2 app, [| mkRel 2; mkRel 1 |])))
    in
    let typ = it_mkProd_or_LetIn app ind.ind_args in
    let full = it_mkNamedProd_or_LetIn typ ctx in
      full
  in
  let indsl = Array.to_list info.mutind_inds in
  let possible_guards =
    List.map 
      (fun ind -> 
	list_tabulate (fun i -> i) (List.length ind.ind_args + 2)) 
      indsl
  in
    Lemmas.start_proof_with_initialization
      (Global, Proof Lemma) 
      (Some (false, possible_guards, None))
      (List.map (fun ind -> add_suffix ind.ind_name "_eqdec", (stmt_of ind, ([], []))) indsl)
      None
      (fun l gr -> ())

  (*   let impl =  *)
  (*     let xname = Name (id_of_string "x") in *)
  (*     let firstpred =  *)
  (* 	mkLambda (xname, typ,  *)
  (* 		 mkProd (yname, lift 1 typ, *)
  (* 			mkEq (lift 2 typ) (mkRel 1) (mkRel 2))) *)
  (*     in *)
  (*     let inner i (ctx, ar) = *)
  (* 	let ar, args = decompose_app ar in *)
  (* 	let typ' = substl args typ in *)
  (* 	let body = *)
  (* 	  let brs = Array.mapi (fun j (ctx', ar') -> *)
  (* 	  ) ind.ind_c *)
  (* 	  in *)
  (* 	  let innerpred =  *)
  (* 	    mkLambda (yname, typ, mkEq (lift 1 typ *)

  (* 	in *)
  (* 	  it_mkLambda_or_LetIn  *)
  (* 	    (mkLambda (yname, typ', body)) *)
  (* 	    ctx *)
  (*     in *)
  (*     let eqdec =  *)
  (* 	mkLambda (xname, typ,  *)
  (* 		 mkLambda (yname, lift 1 typ, *)
  (* 			  ind.ind_case (mkRel 2) firstpred *)
  (* 			    (Array.mapi inner ind.ind_c))) *)
  (*     in *)
  (* 	it_mkLambda_or_LetIn eqdec ind.ind_args *)
  (*   in typ, impl) *)
  (*   info.mutind_inds  *)
  (* in *)
    

  (* let mindb, oneind = Global.lookup_inductive ind in *)
  (* let ctx = oneind.mind_arity_ctxt in *)
  (* let len = List.length ctx in *)
  (* let params = mindb.mind_nparams in *)
  (* let args = oneind.mind_nrealargs in *)
  (* let argsvect = rel_vect 0 len in *)
  (* let paramsvect, rest = array_chop params argsvect in *)
  (* let indty = mkApp (mkInd ind, argsvect) in *)
    


  (* let pid = (id_of_string "P") in *)
  (* let pvar = mkVar pid in *)
  (* let xid = id_of_string "x" and yid = id_of_string "y" in *)
  (* let xdecl = (Name xid, None, lift 1 indty) in *)
  (* let binders = xdecl :: (Name pid, None, new_Type ()) :: ctx in *)
  (* let ydecl = (Name yid, None, lift 2 indty) in *)
  (* let fullbinders = ydecl :: binders in *)
  (* let arity = it_mkProd_or_LetIn (new_Type ()) fullbinders in *)
  (* let env = push_rel_context binders (Global.env ()) in *)
  (* let ind_with_parlift n = *)
  (*   mkApp (mkInd ind, Array.append (Array.map (lift n) paramsvect) rest)  *)
  (* in *)
  (* let lenargs = List.length ctx - params in *)
  (* let pred = *)
  (*   let elim = *)
  (*     let app = ind_with_parlift (args + 2) in *)
  (* 	it_mkLambda_or_LetIn  *)
  (* 	  (mkProd_or_LetIn (Anonymous, None, lift 1 app) (new_Type ())) *)
  (* 	  ((Name xid, None, ind_with_parlift (2 + lenargs)) :: list_firstn lenargs ctx) *)
  (*   in *)
  (*     mkcase env (mkRel 1) elim (fun ind i id nparams args arity -> *)
  (* 	let ydecl = (Name yid, None, arity) in *)
  (* 	let env' = push_rel_context (ydecl :: args) env in *)
  (* 	let decl = (Name yid, None, ind_with_parlift (lenargs + List.length args + 3)) in *)
  (* 	  mkLambda_or_LetIn ydecl *)
  (* 	    (mkcase env' (mkRel 1)  *)
  (* 		(it_mkLambda_or_LetIn (new_Type ()) (decl :: list_firstn lenargs ctx)) *)
  (* 		(fun _ i' id' nparams args' arity' -> *)
  (* 		  if i = i' then  *)
  (* 		    mk_eqs (push_rel_context args' env') *)
  (* 		      (rel_list (List.length args' + 1) (List.length args)) *)
  (* 		      (rel_list 0 (List.length args')) pvar *)
  (* 		  else pvar))) *)
  (* in *)
  (* let app = it_mkLambda_or_LetIn (replace_vars [(pid, mkRel 2)] pred) binders in *)
  (* let ce = *)
  (*   { const_entry_body = app; *)
  (*     const_entry_type = Some arity; *)
  (*     const_entry_opaque = false; *)
  (*     const_entry_boxed = false}  *)
  (* in *)
  (* let indid = Nametab.basename_of_global (IndRef ind) in *)
  (* let id = add_prefix "NoConfusion_" indid *)
  (* and noid = add_prefix "noConfusion_" indid *)
  (* and packid = add_prefix "NoConfusionPackage_" indid in *)
  (* let cstNoConf = Declare.declare_constant id (DefinitionEntry ce, IsDefinition Definition) in *)
  (* let stmt = it_mkProd_or_LetIn *)
  (*   (mkApp (mkConst cstNoConf, rel_vect 1 (List.length fullbinders))) *)
  (*   ((Anonymous, None, mkEq (lift 3 indty) (mkRel 2) (mkRel 1)) :: fullbinders) *)
  (* in *)
  (* let hook _ gr =  *)
  (*   let tc = class_info (global_of_constr (Lazy.force coq_noconfusion_class)) in *)
  (*   let b, ty = instance_constructor tc [indty; mkApp (mkConst cstNoConf, argsvect) ;  *)
  (* 					 mkApp (constr_of_global gr, argsvect) ] in *)
  (*   let ce = { const_entry_body = it_mkLambda_or_LetIn b ctx; *)
  (* 	       const_entry_type = Some (it_mkProd_or_LetIn ty ctx);  *)
  (* 	       const_entry_opaque = false; const_entry_boxed = false } *)
  (*   in *)
  (*   let inst = Declare.declare_constant packid (DefinitionEntry ce, IsDefinition Instance) in *)
  (*     Typeclasses.add_instance (Typeclasses.new_instance tc None true (ConstRef inst)) *)
  (* in *)
  (*   ignore(Subtac_obligations.add_definition ~hook noid stmt ~tactic:(noconf_tac ()) [||]) *)
     

VERNAC COMMAND EXTEND Derive_EqDec
| [ "Derive" "Equality" "for" constr_list(c) ] -> [ 
    List.iter (fun c ->
      let c' = Constrintern.interp_constr Evd.empty (Global.env ()) c in
	match kind_of_term c' with
	| Ind i -> derive_eq_dec i
	| _ -> error "Expected an inductive type")
      c
  ]
END
