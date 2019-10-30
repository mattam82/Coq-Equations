(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(* 
   Statements: forall Δ, EqDec Δ -> EqDec (I Δ)
   Proofs:
   intros; intro x y; depind x; depelim y.
   { c ts = c us } + { c ts <> c us }.
   Takes ts, us and recurse:
   case (eq_dec t u) ; [ rec ts us | right; intro Heq; noconf Heq; apply Hneq; reflexivity ]

*)

open Util
open Names
open Nameops
open Termops
open Declarations
open Inductiveops
open Vars

open EConstr   

open Equations_common

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

let erel_context = List.map of_rel_decl

let inductive_info sigma ((mind, _ as ind),u) =
  let mindb, oneind = Global.lookup_inductive ind in
  let params_ctxt = subst_instance_context (EInstance.kind sigma u) mindb.mind_params_ctxt in
  let subst, paramargs, params =
    named_of_rel_context (fun () -> Id.of_string "param") (erel_context params_ctxt) in
  let nparams = List.length params in
  let env = List.fold_right push_named params (Global.env ()) in
  let info_of_ind i ind =
    let ctx = ind.mind_arity_ctxt in
    let args, _ = List.chop ind.mind_nrealargs ctx in
    let args' = subst_rel_context 0 subst (erel_context args) in
    let induct = ((mind, i),u) in
    let indname = Nametab.basename_of_global (GlobRef.IndRef (mind,i)) in
    let indapp = applist (mkIndU induct, paramargs) in
    let arities = arities_of_constructors env (from_peuniverses sigma induct) in
     let constrs =
      Array.map (fun ty -> 
	let _, rest = decompose_prod_n_assum sigma nparams (EConstr.of_constr ty) in
	let constrty = Vars.substl subst rest in
	decompose_prod_assum sigma constrty)
	arities
    in
    let case c pred brs =
      let ci = make_case_info (Global.env ()) (mind,i) Sorts.Relevant Constr.RegularStyle in
      mkCase (ci, pred, c, brs)
      (* TODO relevance / case inversion *)
    in
      { ind_name = indname;
	ind_c = indapp; ind_args = args';
	ind_constr = constrs;
	ind_case = case }
  in
  let inds = Array.mapi info_of_ind mindb.mind_packets in
    { mutind_params = params;
      mutind_inds = inds }
    
let eq_dec_class evd =
  Option.get (Typeclasses.class_of_constr (Global.env()) !evd (get_efresh logic_eqdec_class evd))

let dec_eq evd = get_efresh logic_eqdec_dec_eq evd

let vars_of_pars pars = 
  Array.of_list (List.map (fun x -> mkVar (get_id x)) pars)

open EConstr.Vars  

let derive_eq_dec env sigma ~poly ind =
  let info = inductive_info sigma ind in
  let ctx = info.mutind_params in
  let evdref = ref sigma in
  let cl = fst (snd (eq_dec_class evdref)) in
  let info_of ind =
    let argsvect = extended_rel_vect 0 ind.ind_args in
    let indapp = mkApp (ind.ind_c, argsvect) in
    let app = 
      mkApp (dec_eq evdref, [| indapp |])
    in
    let app = 
      let xname = Context.nameR (Id.of_string "x") in
      let yname = Context.nameR (Id.of_string "y") in
	mkProd (xname, indapp,
	       mkProd (yname, lift 1 indapp,
  		      mkApp (lift 2 app, [| mkRel 2; mkRel 1 |])))
    in
    let typ = it_mkProd_or_LetIn app ind.ind_args in
    let full = it_mkNamedProd_or_LetIn typ ctx in
    let tc gr = 
      let b, ty = 
	Typeclasses.instance_constructor
          cl
          [indapp; mkapp (Global.env ()) evdref (Lazy.from_val gr)
             (Array.append (vars_of_pars ctx) argsvect) ] in
      let body = 
	it_mkNamedLambda_or_LetIn 
	  (it_mkLambda_or_LetIn (Option.get b) ind.ind_args) ctx
      in
      let univs = Evd.univ_entry ~poly !evdref in
      let types = to_constr !evdref (it_mkNamedProd_or_LetIn (it_mkProd_or_LetIn ty ind.ind_args) ctx) in
      let ce = Declare.definition_entry ~univs ~types (to_constr !evdref body) in
      ce
    in full, tc
  in
  let indsl = Array.to_list info.mutind_inds in
  let indsl = List.map (fun ind -> ind, info_of ind) indsl in
  let hook { DeclareDef.Hook.S.dref; _ } =
    List.iter (fun (ind, (stmt, tc)) ->
	let ce = tc dref in
        let kind = Decls.(IsDefinition Instance) in
        let entry = Declare.DefinitionEntry ce in
	let inst = Declare.declare_constant ~name:(add_suffix ind.ind_name "_EqDec") ~kind entry in
        let inst =
          Classes.mk_instance (fst cl) Hints.empty_hint_info true (GlobRef.ConstRef inst)
	in Classes.add_instance inst)
    indsl
  in
  let hook = DeclareDef.Hook.make hook in
  List.iter
    (fun (ind, (stmt, tc)) ->
     let id = add_suffix ind.ind_name "_eqdec" in
     ignore(Obligations.add_definition ~name:id (to_constr !evdref stmt) ~poly
              (Evd.evar_universe_context !evdref)
              ~tactic:(eqdec_tac ()) ~hook [||]))
    indsl

let () =
  Ederive.(register_derive
            { derive_name = "EqDec";
              derive_fn = make_derive_ind derive_eq_dec })
