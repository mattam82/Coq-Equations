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
open Vars
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type

open Locus
open Context

open Glob_term
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

let ($) f g = fun x -> f (g x)
let (&&&) f g (x, y) = (f x, g y)
let id x = x

(* Debugging infrastructure. *)

let debug = true

let check_term env evd c t =
  Typing.check env (ref evd) c t

let check_type env evd t =
  ignore(Typing.sort_of env (ref evd) t)
      
let typecheck_rel_context evd ctx =
  let _ =
    List.fold_right
      (fun (na, b, t as rel) env ->
	 check_type env evd t;
	 Option.iter (fun c -> check_term env evd c t) b;
	 push_rel rel env)
      ctx (Global.env ())
  in ()


let new_untyped_evar () =
  let _, ev = new_pure_evar empty_named_context_val Evd.empty mkProp in
    ev

let to82 t = Proofview.V82.of_tactic t
let of82 t = Proofview.V82.tactic t

let proper_tails l = snd (List.fold_right (fun _ (t,ts) -> List.tl t, ts @ [t]) l (l, []))

let list_find_map_i f =
  let rec try_find_f n = function
    | [] -> None
    | h::t -> 
      match f n h with
      | Some _ as res -> res 
      | None -> try_find_f (n+1) t
  in
  try_find_f

let array_remove_last a =
  Array.sub a 0 (Array.length a - 1)

let array_chop_last a =
  Array.chop (Array.length a - 1) a

let rev_assoc eq k =
  let rec loop = function
    | [] -> raise Not_found | (v,k')::_ when eq k k' -> v | _ :: l -> loop l 
  in
  loop

let array_filter_map f a =
  let l' =
    Array.fold_right (fun c acc -> 
		      Option.cata (fun r -> r :: acc) acc (f c))
    a []
  in Array.of_list l'


let find_constant contrib dir s =
  Universes.constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "Equations"
let init_constant dir s = find_constant contrib_name dir s
let init_reference dir s = Coqlib.find_reference contrib_name dir s
let gen_constant dir s = Coqlib.gen_constant "equations" dir s

let make_definition ?opaque ?(poly=false) evd ?types b =
  let env = Global.env () in
  let evd, t = Typing.e_type_of env !evd b in
  let evd = match types with
    | None -> evd 
    | Some t -> fst (Typing.e_type_of env evd t)
  in
  let evd, nf = Evarutil.nf_evars_and_universes evd in
  let body = nf b and typ = Option.map nf types in
    Declare.definition_entry ~poly ~univs:(Evd.universe_context evd)
      ?types:typ body

let declare_constant id body ty poly evd kind =
  let ce = make_definition ~opaque:false ~poly (ref evd) ?types:ty body in
  let cst = Declare.declare_constant id (DefinitionEntry ce, kind) in
    Flags.if_verbose message ((string_of_id id) ^ " is defined");
    cst
    
let declare_instance id poly univs ctx cl args =
  let c, t = Typeclasses.instance_constructor cl args in
  let cst = declare_constant id (it_mkLambda_or_LetIn (Option.get c) ctx)
    (Some (it_mkProd_or_LetIn t ctx)) poly univs (IsDefinition Instance)
  in 
  let inst = Typeclasses.new_instance (fst cl) None true poly (Globnames.ConstRef cst) in
    Typeclasses.add_instance inst; mkConst cst

let coq_unit = lazy (init_constant ["Coq";"Init";"Datatypes"] "unit")
let coq_tt = lazy (init_constant ["Coq";"Init";"Datatypes"] "tt")

let coq_prod = lazy (init_constant ["Coq";"Init";"Datatypes"] "prod")
let coq_pair = lazy (init_constant ["Coq";"Init";"Datatypes"] "pair")

let coq_zero = lazy (gen_constant ["Init"; "Datatypes"] "O")
let coq_succ = lazy (gen_constant ["Init"; "Datatypes"] "S")
let coq_nat = lazy (gen_constant ["Init"; "Datatypes"] "nat")

let rec coq_nat_of_int = function
  | 0 -> Lazy.force coq_zero
  | n -> mkApp (Lazy.force coq_succ, [| coq_nat_of_int (pred n) |])

let rec int_of_coq_nat c = 
  match kind_of_term c with
  | App (f, [| arg |]) -> succ (int_of_coq_nat arg)
  | _ -> 0

let coq_fix_proto = lazy (init_constant ["Coq";"Program";"Tactics"] "fix_proto")

let fresh_id_in_env avoid id env =
  Namegen.next_ident_away_in_goal id (avoid@ids_of_named_context (named_context env))

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (pf_env gl)

let coq_eq = Lazy.from_fun Coqlib.build_coq_eq
let coq_eq_refl = lazy ((Coqlib.build_coq_eq_data ()).Coqlib.refl)

let coq_heq = lazy (Coqlib.coq_reference "mkHEq" ["Logic";"JMeq"] "JMeq")
let coq_heq_refl = lazy (Coqlib.coq_reference "mkHEq" ["Logic";"JMeq"] "JMeq_refl")

let coq_fix_proto = lazy (Coqlib.coq_reference "coq_fix_proto" ["Program";"Tactics"] "fix_proto")


let mkapp evdref t args =
  let evd, c = Evd.fresh_global (Global.env ()) !evdref (Lazy.force t) in
  let _ = evdref := evd in
    mkApp (c, args)

let refresh_universes_strict evd t = 
  let evd', t' = Evarsolve.refresh_universes (Some true) (Global.env()) !evd t in
    evd := evd'; t'

let mkEq evd t x y = 
  mkapp evd coq_eq [| refresh_universes_strict evd t; x; y |]
    
let mkRefl evd t x = 
  mkapp evd coq_eq_refl [| refresh_universes_strict evd t; x |]

let mkHEq evd t x u y =
  mkapp evd coq_heq [| refresh_universes_strict evd t; x; refresh_universes_strict evd u; y |]
    
let mkHRefl evd t x =
  mkapp evd coq_heq_refl
    [| refresh_universes_strict evd t; x |]

let dummy_loc = Loc.dummy_loc 
type 'a located = 'a Loc.located

let tac_of_string str args =
  Tacinterp.interp (TacArg(dummy_loc, 
			   TacCall(dummy_loc, Qualid (dummy_loc, qualid_of_string str), args)))

let equations_path = ["Equations";"Equations"]

let get_class c = 
  let x = Typeclasses.class_of_constr c in
    fst (snd (Option.get x))

let functional_induction_class () =
  get_class
    (init_constant ["Equations";"FunctionalInduction"] "FunctionalInduction")

let functional_elimination_class () =
  get_class
    (init_constant ["Equations";"FunctionalInduction"] "FunctionalElimination")

let dependent_elimination_class () =
  get_class 
    (init_constant ["Equations";"DepElim"] "DependentEliminationPackage")

let below_path = ["Equations";"Below"]

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
let coq_block = lazy (init_constant ["Equations";"DepElim"] "block")
let coq_hide = lazy (init_constant ["Equations";"DepElim"] "hide_pattern")
let coq_add_pattern = lazy (init_constant ["Equations";"DepElim"] "add_pattern")
let coq_end_of_section_constr = lazy (init_constant ["Equations";"DepElim"] "the_end_of_the_section")
let coq_end_of_section = lazy (init_constant ["Equations";"DepElim"] "end_of_section")

let coq_notT = lazy (init_constant ["Coq";"Init";"Logic_Type"] "notT")
let coq_ImpossibleCall = lazy (init_constant ["Equations";"DepElim"] "ImpossibleCall")

let unfold_add_pattern = lazy
  (Tactics.unfold_in_concl [(Locus.AllOccurrences, 
			     EvalConstRef (fst (destConst (Lazy.force coq_add_pattern))))])

let subterm_relation_base = "subterm_relation"

(* Misc tactics *)


let rec head_of_constr t =
  let t = strip_outer_cast(collapse_appl t) in
    match kind_of_term t with
    | Prod (_,_,c2)  -> head_of_constr c2 
    | LetIn (_,_,_,c2) -> head_of_constr c2
    | App (f,args)  -> head_of_constr f
    | _      -> t

let nowhere = { onhyps = Some []; concl_occs = NoOccurrences }

(* Lifting a [rel_context] by [n]. *)

let lift_rel_contextn k n sign =
  let rec liftrec k = function
    | (na,c,t)::sign ->
	(na,Option.map (liftn n k) c,liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (rel_context_length sign + k) sign

let lift_context n sign = lift_rel_contextn 0 n sign

let lift_list l = List.map (lift 1) l

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
    | Const (cst,_ as c) when Cset.mem cst csts ->
	true, Environ.constant_value_in env c
    | App (f, args) ->
	(match aux f with
	| true, f' -> true, Reductionops.whd_betaiota Evd.empty (mkApp (f', args))
	| false, _ -> 
	    let done_, args' = 
	      Array.fold_left_i (fun i (done_, acc) arg -> 
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
open Errors

let autounfold_first db cl gl =
  let st =
    List.fold_left (fun (i,c) dbname -> 
      let db = try Hints.searchtable_map dbname 
	with Not_found -> errorlabstrm "autounfold" (str "Unknown database " ++ str dbname)
      in
      let (ids, csts) = Hints.Hint_db.unfolds db in
	(Idset.union ids i, Cset.union csts c)) (Idset.empty, Cset.empty) db
  in
  let did, c' = unfold_head (pf_env gl) st
    (match cl with Some (id, _) -> pf_get_hyp_typ gl id | None -> pf_concl gl) 
  in
    if did then
      match cl with
      | Some hyp -> Proofview.V82.of_tactic (change_in_hyp None (make_change_arg c') hyp) gl
      | None -> Proofview.V82.of_tactic (convert_concl_no_check c' DEFAULTcast) gl
    else tclFAIL 0 (str "Nothing to unfold") gl

type hintdb_name = string

let rec db_of_constr c = match kind_of_term c with
  | Const (c,_) -> string_of_label (con_label c)
  | App (c,al) -> db_of_constr c
  | _ -> assert false

let dbs_of_constrs = map db_of_constr

(** Bindings to Coq *)

let below_tactics_path =
  make_dirpath (List.map id_of_string ["Below";"Equations"])

let below_tac s =
  make_kn (MPfile below_tactics_path) (make_dirpath []) (mk_label s)

let tacident_arg h =
  Reference (Ident (dummy_loc,h))

let tacvar_arg h =
  let ipat = Genarg.in_gen (Genarg.rawwit Constrarg.wit_intro_pattern) 
    (dummy_loc, Misctypes.IntroNaming (Misctypes.IntroIdentifier h)) in
    TacGeneric ipat

let rec_tac h h' = 
  TacArg(dummy_loc, TacCall(dummy_loc, 
			    Qualid (dummy_loc, qualid_of_string "Equations.Below.rec"),
		[tacident_arg h;
		 tacvar_arg h']))

let rec_wf_tac h h' rel = 
  TacArg(dummy_loc, TacCall(dummy_loc, 
    Qualid (dummy_loc, qualid_of_string "Equations.Subterm.rec_wf_eqns_rel"),
			    [tacident_arg h;tacvar_arg h';			     
			     ConstrMayEval (Genredexpr.ConstrTerm rel)]))

let unfold_recursor_tac () = tac_of_string "Equations.Subterm.unfold_recursor" []

let equations_tac_expr () = 
  (TacArg(dummy_loc, TacCall(dummy_loc, 
   Qualid (dummy_loc, qualid_of_string "Equations.DepElim.equations"), [])))

let equations_tac () = tac_of_string "Equations.DepElim.equations" []

let set_eos_tac () = tac_of_string "Equations.DepElim.set_eos" []
    
let solve_rec_tac () = tac_of_string "Equations.Below.solve_rec" []

let find_empty_tac () = tac_of_string "Equations.DepElim.find_empty" []

let pi_tac () = tac_of_string "Equations.Subterm.pi" []

let noconf_tac () = tac_of_string "Equations.NoConfusion.solve_noconf" []

let simpl_equations_tac () = tac_of_string "Equations.DepElim.simpl_equations" []

let reference_of_global c =
  Qualid (dummy_loc, Nametab.shortest_qualid_of_global Idset.empty c)

let solve_equation_tac c = tac_of_string "Equations.DepElim.solve_equation"

let impossible_call_tac c = Tacintern.glob_tactic
  (TacArg(dummy_loc,TacCall(dummy_loc,
  Qualid (dummy_loc, qualid_of_string "Equations.DepElim.impossible_call"),
  [ConstrMayEval (Genredexpr.ConstrTerm (Constrexpr.CRef (reference_of_global c, None)))])))

let depelim_tac h = tac_of_string "Equations.DepElim.depelim"
  [tacident_arg h]

let do_empty_tac h = tac_of_string "Equations.DepElim.do_empty"
  [tacident_arg h]

let depelim_nosimpl_tac h = tac_of_string "Equations.DepElim.depelim_nosimpl"
  [tacident_arg h]

let simpl_dep_elim_tac () = tac_of_string "Equations.DepElim.simpl_dep_elim" []

let depind_tac h = tac_of_string "Equations.DepElim.depind"
  [tacident_arg h]

(* let mkEq t x y =  *)
(*   mkApp (Coqlib.build_coq_eq (), [| t; x; y |]) *)

let mkNot t =
  mkApp (Coqlib.build_coq_not (), [| t |])

let mkNot t =
  mkApp (Coqlib.build_coq_not (), [| t |])
      
let mkProd_or_subst (na,body,t) c =
  match body with
    | None -> mkProd (na, t, c)
    | Some b -> subst1 b c

let mkProd_or_clear decl c =
  if not (dependent (mkRel 1) c) then
    subst1 mkProp c
  else mkProd_or_LetIn decl c

let it_mkProd_or_clear ty ctx = 
  fold_left (fun c d -> mkProd_or_clear d c) ty ctx
      
let mkLambda_or_subst (na,body,t) c =
  match body with
    | None -> mkLambda (na, t, c)
    | Some b -> subst1 b c

let mkLambda_or_subst_or_clear (na,body,t) c =
  match body with
  | None when dependent (mkRel 1) c -> mkLambda (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let mkProd_or_subst_or_clear (na,body,t) c =
  match body with
  | None when dependent (mkRel 1) c -> mkProd (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let it_mkProd_or_subst ty ctx = 
  nf_beta Evd.empty (List.fold_left 
		       (fun c d -> whd_betalet Evd.empty (mkProd_or_LetIn d c)) ty ctx)

let it_mkProd_or_clean ty ctx = 
  nf_beta Evd.empty (List.fold_left 
		       (fun c (na,_,_ as d) -> whd_betalet Evd.empty 
			 (if na == Anonymous then subst1 mkProp c
			  else (mkProd_or_LetIn d c))) ty ctx)

let it_mkLambda_or_subst ty ctx = 
  whd_betalet Evd.empty
    (List.fold_left (fun c d -> mkLambda_or_LetIn d c) ty ctx)

let it_mkLambda_or_subst_or_clear ty ctx = 
  (List.fold_left (fun c d -> mkLambda_or_subst_or_clear d c) ty ctx)

let it_mkProd_or_subst_or_clear ty ctx = 
  (List.fold_left (fun c d -> mkProd_or_subst_or_clear d c) ty ctx)


let lift_constrs n cs = map (lift n) cs

let ids_of_constr ?(all=false) vars c =
  let rec aux vars c =
    match kind_of_term c with
    | Var id -> Idset.add id vars
    | App (f, args) -> 
	(match kind_of_term f with
	| Construct ((ind,_),_)
	| Ind (ind, _) ->
            let (mib,mip) = Global.lookup_inductive ind in
	      Array.fold_left_from
		(if all then 0 else mib.Declarations.mind_nparams)
		aux vars args
	| _ -> fold_constr aux vars c)
    | _ -> fold_constr aux vars c
  in aux vars c
    
let decompose_indapp f args =
  match kind_of_term f with
  | Construct ((ind,_),_) 
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
	mkApp (f, pars), args
  | _ -> f, args

let e_conv env evdref t t' =
  try evdref := Evd.conversion env !evdref Reduction.CONV t t'; true
  with Reduction.NotConvertible -> false

      
let deps_of_var id env =
  Environ.fold_named_context
    (fun _ (n,b,t) (acc : Idset.t) -> 
      if Option.cata (occur_var env id) false b || occur_var env id t then
	Idset.add n acc
      else acc)
    env ~init:Idset.empty
    
let idset_of_list =
  List.fold_left (fun s x -> Idset.add x s) Idset.empty

let pr_smart_global = Pptactic.pr_or_by_notation pr_reference
let string_of_smart_global = function
  | Misctypes.AN ref -> string_of_reference ref
  | Misctypes.ByNotation (loc, s, _) -> s

let ident_of_smart_global x = 
  id_of_string (string_of_smart_global x)
