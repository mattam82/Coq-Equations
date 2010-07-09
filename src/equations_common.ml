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
open Entries
open Tacmach
open Tacexpr
open Tactics
open Tacticals
open Decl_kinds

open Coqlib

let list_map_filter_i f l = 
  let rec aux i = function
    | hd :: tl -> 
	(match f i hd with
	| Some x -> x :: aux (succ i) tl
	| None -> aux (succ i) tl)
    | [] -> []
  in aux 0 l

let find_constant contrib dir s =
  constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "Equations"
let init_constant dir s = find_constant contrib_name dir s
let init_reference dir s = Coqlib.find_reference contrib_name dir s


let declare_constant id body ty kind =
  let ce =
    { const_entry_body = body;
      const_entry_type = ty;
      const_entry_opaque = false;
      const_entry_boxed = false}
  in 
  let cst = Declare.declare_constant id (DefinitionEntry ce, kind) in
    Flags.if_verbose message ((string_of_id id) ^ " is defined");
    cst
    
let declare_instance id ctx cl args =
  let c, t = Typeclasses.instance_constructor cl args in
  let cst = declare_constant id (it_mkLambda_or_LetIn c ctx)
    (Some (it_mkProd_or_LetIn t ctx)) (IsDefinition Instance)
  in 
  let inst = Typeclasses.new_instance cl None true (ConstRef cst) in
    Typeclasses.add_instance inst; mkConst cst

let coq_unit = lazy (init_constant ["Coq";"Init";"Datatypes"] "unit")
let coq_tt = lazy (init_constant ["Coq";"Init";"Datatypes"] "tt")

let coq_prod = lazy (init_constant ["Coq";"Init";"Datatypes"] "prod")
let coq_pair = lazy (init_constant ["Coq";"Init";"Datatypes"] "pair")

let fresh_id_in_env avoid id env =
  Namegen.next_ident_away_in_goal id (avoid@ids_of_named_context (named_context env))

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (pf_env gl)

let coq_eq = Lazy.lazy_from_fun Coqlib.build_coq_eq
let coq_eq_refl = lazy ((Coqlib.build_coq_eq_data ()).Coqlib.refl)

let coq_heq = lazy (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq")
let coq_heq_refl = lazy (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq_refl")

let mkEq t x y = 
  mkApp (Lazy.force coq_eq, [| refresh_universes_strict t; x; y |])
    
let mkRefl t x = 
  mkApp (Lazy.force coq_eq_refl, [| refresh_universes_strict t; x |])

let mkHEq t x u y =
  mkApp (Lazy.force coq_heq,
	[| refresh_universes_strict t; x; refresh_universes_strict u; y |])
    
let mkHRefl t x =
  mkApp (Lazy.force coq_heq_refl,
	[| refresh_universes_strict t; x |])

let tac_of_string str args =
  Tacinterp.interp (TacArg(TacCall(dummy_loc, Qualid (dummy_loc, qualid_of_string str), args)))

let equations_path = ["Equations";"Equations"]
let coq_dynamic_ind = lazy (init_constant equations_path "dynamic")
let coq_dynamic_constr = lazy (init_constant equations_path "Build_dynamic")
let coq_dynamic_type = lazy (init_constant equations_path "dynamic_type")
let coq_dynamic_obj = lazy (init_constant equations_path "dynamic_obj")

let functional_induction_class () =
  Option.get 
    (Typeclasses.class_of_constr
	(init_constant ["Equations";"FunctionalInduction"] "FunctionalInduction"))

let functional_elimination_class () =
  Option.get 
    (Typeclasses.class_of_constr
	(init_constant ["Equations";"FunctionalInduction"] "FunctionalElimination"))

let dependent_elimination_class () =
  Option.get 
    (Typeclasses.class_of_constr
	(init_constant ["Equations";"DepElim"] "DependentEliminationPackage"))

let below_path = ["Equations";"Below"]
let coq_have_class = lazy (init_constant below_path "Have")
let coq_have_meth = lazy (init_constant below_path "have")

let coq_wellfounded_class = lazy (init_constant ["Equations";"Subterm"] "WellFounded")
let coq_wellfounded = lazy (init_constant ["Coq";"Init";"Wf"] "well_founded")
let coq_relation = lazy (init_constant ["Coq";"Relations";"Relation_Definitions"] "relation")
let coq_clos_trans = lazy (init_constant ["Coq";"Relations";"Relation_Operators"] "clos_trans")
let coq_id = lazy (init_constant ["Coq";"Init";"Datatypes"] "id")

let list_path = ["Lists";"List"]
let coq_list_ind = lazy (init_constant list_path "list")
let coq_list_nil = lazy (init_constant list_path "nil")
let coq_list_cons = lazy (init_constant list_path "cons")

let coq_noconfusion_class = lazy (init_constant ["Equations";"DepElim"] "NoConfusionPackage")
  
let coq_inacc = lazy (init_constant ["Equations";"DepElim"] "inaccessible_pattern")
let coq_hide = lazy (init_constant ["Equations";"DepElim"] "hide_pattern")
let coq_add_pattern = lazy (init_constant ["Equations";"DepElim"] "add_pattern")
let coq_end_of_section_constr = lazy (init_constant ["Equations";"DepElim"] "the_end_of_the_section")
let coq_end_of_section = lazy (init_constant ["Equations";"DepElim"] "end_of_section")

let coq_notT = lazy (init_constant ["Coq";"Init";"Logic_Type"] "notT")
let coq_ImpossibleCall = lazy (init_constant ["Equations";"DepElim"] "ImpossibleCall")

let unfold_add_pattern = lazy
  (Tactics.unfold_in_concl [((false, []), EvalConstRef (destConst (Lazy.force coq_add_pattern)))])

let coq_dynamic_list = lazy (mkApp (Lazy.force coq_list_ind, [| Lazy.force coq_dynamic_ind |]))

let rec constrs_of_coq_dynamic_list c = 
  match kind_of_term c with
  | App (f, args) when f = Lazy.force coq_list_nil -> []
  | App (f, args) when f = Lazy.force coq_list_cons && 
      eq_constr args.(0) (Lazy.force coq_dynamic_ind) && 
      Array.length args = 3 -> 
      (match kind_of_term args.(1) with
      | App (f, args') when f = Lazy.force coq_dynamic_constr &&
	  Array.length args' = 2 ->
	  (args'.(0), args'.(1)) :: constrs_of_coq_dynamic_list args.(2)
      | _ -> raise (Invalid_argument "constrs_of_coq_dynamic_list"))
  | _ -> raise (Invalid_argument "constrs_of_coq_dynamic_list")


let subterm_relation_base = "subterm_relation"

(* Misc tactics *)


let rec head_of_constr t =
  let t = strip_outer_cast(collapse_appl t) in
    match kind_of_term t with
    | Prod (_,_,c2)  -> head_of_constr c2 
    | LetIn (_,_,_,c2) -> head_of_constr c2
    | App (f,args)  -> head_of_constr f
    | _      -> t
      
TACTIC EXTEND decompose_app
[ "decompose_app" ident(h) ident(h') constr(c) ] -> [ fun gl ->
    let f, args = decompose_app c in
    let fty = pf_type_of gl f in
    let flam = mkLambda (Name (id_of_string "f"), fty, mkApp (mkRel 1, Array.of_list args)) in
      tclTHEN (letin_tac None (Name h) f None allHyps)
	(letin_tac None (Name h') flam None allHyps) gl
  ]
END

(* open Pfedit *)
(* open Proof_trees *)

(* let check_guard gl = *)
(*   let pts = get_pftreestate () in *)
(*   let pf = proof_of_pftreestate pts in *)
(*   let (pfterm,_) = extract_open_pftreestate pts in *)
(*     try *)
(*       Inductiveops.control_only_guard (Evd.evar_env (goal_of_proof pf)) *)
(* 	pfterm; tclIDTAC gl *)
(*     with UserError(_,s) -> *)
(*       tclFAIL 0 (str ("Condition violated: ") ++s) gl *)
	
(* TACTIC EXTEND guarded *)
(* [ "guarded"  ] -> [ check_guard ] *)
(* END *)

TACTIC EXTEND abstract_match
[ "abstract_match" ident(hyp) constr(c) ] -> [
  match kind_of_term c with
  | Case (_, _, c, _) -> letin_tac None (Name hyp) c None allHypsAndConcl
  | _ -> tclFAIL 0 (str"Not a case expression")
]
END


open Tacexpr

let nowhere = { onhyps = Some []; concl_occs = no_occurrences_expr }

(* Lifting a [rel_context] by [n]. *)

let lift_rel_contextn k n sign =
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,Option.map (liftn n k) c,liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (rel_context_length sign + k) sign

let lift_context n sign = lift_rel_contextn 0 n sign

(* let compute_params cst =  *)
(*   let body = constant_value (Global.env ()) cst in *)
(*   let init, n, c =  *)
(*     let ctx, body =  *)
(*       match kind_of_term body with *)
(*       | Lambda _ -> decompose_lam_assum c  *)
(*       | _ -> [], c *)
(*     in *)
(*       (interval 0 (List.length ctx),  *)
(*       List.length ctx, body) *)
(*   in *)
(*   let params_of_args pars n args = *)
(*     Array.fold_left *)
(*       (fun (pars, acc) x -> *)
(* 	match pars with *)
(* 	| [] -> (pars, acc) *)
(* 	| par :: pars -> *)
(* 	    if isRel x then *)
(* 	      if n + par = destRel x then *)
(* 		(pars, par :: acc) *)
(* 	      else (pars, acc) *)
(* 	    else (pars, acc)) *)
(*       (pars, []) args *)
(*   in *)
(*   let rec aux pars n c = *)
(*     match kind_of_term c with *)
(*     | App (f, args) -> *)
(* 	if f = mkConst cst then *)
(* 	  let _, pars' = params_of_args pars n args in *)
(* 	    pars' *)
(* 	else pars *)
(*     | _ -> pars *)
(*   in aux init n c *)



let unfold_head env (ids, csts) c = 
  let rec aux c = 
    match kind_of_term c with
    | Var id when Idset.mem id ids ->
	(match Environ.named_body id env with
	| Some b -> true, b
	| None -> false, c)
    | Const cst when Cset.mem cst csts ->
	true, Environ.constant_value env cst
    | App (f, args) ->
	(match aux f with
	| true, f' -> true, Reductionops.whd_betaiota Evd.empty (mkApp (f', args))
	| false, _ -> 
	    let done_, args' = 
	      array_fold_left_i (fun i (done_, acc) arg -> 
		if done_ then done_, arg :: acc 
		else match aux arg with
		| true, arg' -> true, arg' :: acc
		| false, arg' -> false, arg :: acc)
		(false, []) args
	    in 
	      if done_ then true, mkApp (f, Array.of_list (List.rev args'))
	      else false, c)
    | _ -> 
	let done_ = ref false in
	let c' = map_constr (fun c -> 
	  if !done_ then c else 
	    let x, c' = aux c in
	      done_ := x; c') c
	in !done_, c'
  in aux c

open Auto

let autounfold_first db cl gl =
  let st =
    List.fold_left (fun (i,c) dbname -> 
      let db = try searchtable_map dbname 
	with Not_found -> errorlabstrm "autounfold" (str "Unknown database " ++ str dbname)
      in
      let (ids, csts) = Hint_db.unfolds db in
	(Idset.union ids i, Cset.union csts c)) (Idset.empty, Cset.empty) db
  in
  let did, c' = unfold_head (pf_env gl) st
    (match cl with Some (id, _) -> pf_get_hyp_typ gl id | None -> pf_concl gl) 
  in
    if did then
      match cl with
      | Some hyp -> change_in_hyp None c' hyp gl
      | None -> convert_concl_no_check c' DEFAULTcast gl
    else tclFAIL 0 (str "Nothing to unfold") gl

(* 	  Cset.fold (fun cst -> cons (all_occurrences, EvalConstRef cst)) csts *)
(* 	    (Idset.fold (fun id -> cons (all_occurrences, EvalVarRef id)) ids [])) db) *)
(*       in unfold_option unfolds cl *)

(*       let db = try searchtable_map dbname  *)
(* 	with Not_found -> errorlabstrm "autounfold" (str "Unknown database " ++ str dbname) *)
(*       in *)
(*       let (ids, csts) = Hint_db.unfolds db in *)
(* 	Cset.fold (fun cst -> tclORELSE (unfold_option [(occ, EvalVarRef id)] cst)) csts *)
(* 	  (Idset.fold (fun id -> tclORELSE (unfold_option [(occ, EvalVarRef id)] cl) ids acc))) *)
(*       (tclFAIL 0 (mt())) db *)
      
open Extraargs
open Eauto

TACTIC EXTEND autounfold_first
| [ "autounfold_first" hintbases(db) "in" hyp(id) ] ->
    [ autounfold_first (match db with None -> ["core"] | Some x -> x) (Some (id, InHyp)) ]
| [ "autounfold_first" hintbases(db) ] ->
    [ autounfold_first (match db with None -> ["core"] | Some x -> x) None ]
END
