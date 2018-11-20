(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Util
open Names
open Constr
open Termops
open Environ
open Reductionops
open Pp
open Locus
open Context

open Evarutil
open List
open Libnames
open Entries
open Tacmach
open Tactics
open Tacticals
open Decl_kinds

open Ltac_plugin
open Tacexpr

let ($) f g = fun x -> f (g x)
let (&&&) f g (x, y) = (f x, g y)
let id x = x

let to_peuniverses (x, u) = (x, EConstr.EInstance.make u)
let from_peuniverses sigma (x, u) = (x, EConstr.EInstance.kind sigma u)

(* Options. *)
let ocaml_splitting = ref true
let simplify_withK = ref false
let simplify_withK_dec = ref false
let equations_transparent = ref false

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optname  = "splitting variables in OCaml";
  Goptions.optkey   = ["Equations"; "OCaml"; "Splitting"];
  Goptions.optread  = (fun () -> !ocaml_splitting);
  Goptions.optwrite = (fun b -> ocaml_splitting := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optname  = "using axiomatic K during simplification";
  Goptions.optkey   = ["Equations"; "WithK"];
  Goptions.optread  = (fun () -> !simplify_withK);
  Goptions.optwrite = (fun b -> simplify_withK := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optname  = "using propositional K during simplification";
  Goptions.optkey   = ["Equations"; "WithKDec"];
  Goptions.optread  = (fun () -> !simplify_withK_dec);
  Goptions.optwrite = (fun b -> simplify_withK_dec := b)
}

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optname  = "leave definitions transparent";
  Goptions.optkey   = ["Equations"; "Transparent"];
  Goptions.optread  = (fun () -> !equations_transparent);
  Goptions.optwrite = (fun b -> equations_transparent := b)
}

(* Debugging infrastructure. *)

let debug = ref false

let _ = Goptions.declare_bool_option {
  Goptions.optdepr  = false;
  Goptions.optname  = "Equations debug output";
  Goptions.optkey   = ["Equations"; "Debug"];
  Goptions.optread  = (fun () -> !debug);
  Goptions.optwrite = (fun b -> debug := b)
}

type flags = {
  polymorphic : bool;
  with_eqns : bool;
  with_ind : bool }  

let check_term env evd c t =
  ignore(Typing.check env evd c t)

let check_type env evd t =
  ignore(Typing.sort_of env evd t)
      
let typecheck_rel_context env evd ctx =
  let open Context.Rel.Declaration in
  try
  let _ =
    List.fold_right
      (fun rel env ->
	 check_type env evd (get_type rel);
	 Option.iter (fun c -> check_term env evd c (get_type rel)) (get_value rel);
	 EConstr.push_rel rel env)
      ctx env
  in ()
  with e ->
    Printf.eprintf "Exception while typechecking context %s : %s\n"
                   (Pp.string_of_ppcmds (Internal.print_rel_context (EConstr.push_rel_context ctx env)))
                   (Printexc.to_string e);
    raise e

let new_untyped_evar () =
  let (sigma, ev) = new_pure_evar empty_named_context_val Evd.empty (EConstr.of_constr mkProp) in
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

let new_global sigma gr =
  Evarutil.new_global sigma gr

let e_new_global evdref gr =
  let sigma, gr = new_global !evdref gr in
  evdref := sigma; gr

type lazy_ref = Names.GlobRef.t Lazy.t

let equations_lib_ref s = Coqlib.lib_ref ("equations." ^ s)

let find_global s = lazy (equations_lib_ref s)

let find_constant s evd = e_new_global evd (equations_lib_ref s)

let global_reference id =
  Smartlocate.global_of_extended_global (Nametab.locate_extended (qualid_of_ident id))

let constr_of_global = UnivGen.constr_of_monomorphic_global

let constr_of_ident id =
  EConstr.of_constr (constr_of_global (Nametab.locate (qualid_of_ident id)))

let e_type_of env evd t =
  let evm, t = Typing.type_of ~refresh:false env !evd t in
  evd := evm; t

let make_definition ?opaque ?(poly=false) evm ?types b =
  let env = Global.env () in
  let evm = match types with
    | None -> fst (Typing.type_of env evm b)
    | Some t ->
      let evm = fst (Typing.type_of env evm t) in
      Typing.check env evm b t
  in
  let evm = Evd.minimize_universes evm in
  let evm0 = evm in
  let body = EConstr.to_constr evm b and typ = Option.map (EConstr.to_constr evm) types in
  let used = Vars.universes_of_constr body in
  let used' = Option.cata Vars.universes_of_constr Univ.LSet.empty typ in
  let used = Univ.LSet.union used used' in
  let evm = Evd.restrict_universe_context evm used in
  let univs = Evd.const_univ_entry ~poly evm in
  evm0, evm, Declare.definition_entry ~univs ?types:typ body

let declare_constant id body ty poly evd kind =
  let evm0, evm, ce = make_definition ~opaque:false ~poly evd ?types:ty body in
  let cst = Declare.declare_constant id (DefinitionEntry ce, kind) in
  Flags.if_verbose Feedback.msg_info (str((Id.to_string id) ^ " is defined"));
  if poly then
    let cstr = EConstr.(mkConstU (cst, EInstance.make (Univ.UContext.instance (Evd.to_universe_context evm)))) in
    cst, (evm0, cstr)
  else cst, (evm0, EConstr.mkConst cst)

let make_definition ?opaque ?(poly=false) evm ?types b =
  let evm', _, t = make_definition ?opaque ~poly evm ?types b in
  evm', t

let declare_instance id poly evm ctx cl args =
  let open Typeclasses in
  let open EConstr in
  let c, t = instance_constructor cl args in
  let term = it_mkLambda_or_LetIn (Option.get c) ctx in
  let typ = EConstr.it_mkProd_or_LetIn t ctx in
  let cst, ecst = declare_constant id term (Some typ) poly evm (IsDefinition Instance) in
  let inst = new_instance (fst cl) Hints.empty_hint_info true (Globnames.ConstRef cst) in
    add_instance inst; cst, ecst

let coq_zero = (find_global "nat.zero")
let coq_succ = (find_global "nat.succ")
let coq_nat = (find_global "nat.type")

let rec coq_nat_of_int = function
  | 0 -> constr_of_global (Lazy.force coq_zero)
  | n -> mkApp (constr_of_global (Lazy.force coq_succ), [| coq_nat_of_int (pred n) |])

let rec int_of_coq_nat c = 
  match Constr.kind c with
  | App (f, [| arg |]) -> succ (int_of_coq_nat arg)
  | _ -> 0

let fresh_id_in_env avoid id env =
  Namegen.next_ident_away_in_goal id (Id.Set.union avoid (Id.Set.of_list (ids_of_named_context (named_context env))))

let fresh_id avoid id gl =
  fresh_id_in_env avoid id (pf_env gl)


let coq_heq = (find_global "JMeq.type")
let coq_heq_refl = (find_global "JMeq.refl")

let coq_fix_proto = (find_global "fixproto")

let compute_sort_family l =
  let env = Global.env () in
  let evd = Evd.from_env env in
  let evd, c = Evarutil.new_global evd (Lazy.force l) in
  let _, s = EConstr.destArity evd (Retyping.get_type_of env evd c) in
  Sorts.family (EConstr.ESorts.kind evd s)

let logic_eq_type = (find_global "equality.type")
let logic_eq_refl = (find_global "equality.refl")
let logic_eq_case = (find_global "equality.case")
let logic_eq_elim = (find_global "equality.elim")
let logic_sort = lazy (compute_sort_family logic_eq_type)
let logic_bot = (find_global "bottom.type")
let logic_bot_case = (find_global "bottom.case")
let logic_bot_elim = (find_global "bottom.elim")
let logic_top = (find_global "top.type")
let logic_top_intro = (find_global "top.intro")
let logic_top_elim = (find_global "top.elim")
let logic_conj = (find_global "conj.type")
let logic_conj_intro = (find_global "conj.intro")
let logic_unit = (find_global "unit.type")
let logic_unit_intro = (find_global "unit.intro")
let logic_product = (find_global "product.type")
let logic_pair = (find_global "product.intro")
let logic_wellfounded_class = (find_global "wellfounded.class")
let logic_wellfounded = (find_global "wellfounded.type")
let logic_relation = (find_global "relation.type")
let logic_transitive_closure = (find_global "relation.transitive_closure")

let logic_eqdec_class = (find_global "eqdec.class")
let logic_eqdec_dec_eq = (find_global "eqdec.dec_eq")

let logic_signature_class = find_global "signature.class"
let logic_signature_sig = find_global "signature.signature"
let logic_signature_pack = find_global "signature.pack"

let get_fresh sigma r = new_global sigma (Lazy.force r)

let get_efresh r evd = e_new_global evd (Lazy.force r)

let is_lglobal gr c = Globnames.is_global (Lazy.force gr) c

open EConstr

let fresh_logic_sort evd =
  let evars, sort = Evd.fresh_sort_in_family !evd (Lazy.force logic_sort) in
  evd := evars; mkSort sort

let mkapp env evdref t args =
  let evd, c = fresh_global env !evdref (Lazy.force t) in
  let _ = evdref := evd in
    mkApp (c, args)

let refresh_universes_strict env evd t = 
  let evd', t' = Evarsolve.refresh_universes (Some true) env !evd t in
    evd := evd'; t'
    
let mkEq env evd t x y = 
  mkapp env evd logic_eq_type [| refresh_universes_strict env evd t; x; y |]
    
let mkRefl env evd t x = 
  mkapp env evd logic_eq_refl [| refresh_universes_strict env evd t; x |]

let mkHEq env evd t x u y =
  mkapp env evd coq_heq [| refresh_universes_strict env evd t; x;
                           refresh_universes_strict env evd u; y |]
    
let mkHRefl env evd t x =
  mkapp env evd coq_heq_refl [| refresh_universes_strict env evd t; x |]

let dummy_loc = None
type 'a located = 'a Loc.located

let tac_of_string str args =
  Tacinterp.interp (TacArg(CAst.(make @@ TacCall(make (Libnames.qualid_of_string str, args)))))

let get_class sigma c =
  let x = Typeclasses.class_of_constr sigma c in
    fst (snd (Option.get x))

type esigma = Evd.evar_map ref

type 'a peuniverses = 'a * EConstr.EInstance.t

let functional_induction_class evd =
  let evdref = ref evd in
  let cl = find_constant "funind.class" evdref in
  !evdref, get_class !evdref cl

let functional_elimination_class evd =
  let evdref = ref evd in
  let cl = find_constant "funelim.class" evdref in
  !evdref, get_class !evdref cl

let dependent_elimination_class evd =
  get_class !evd (find_constant "depelim.class" evd)

let coq_noconfusion_class = (find_global "noconfusion.class")

let coq_inacc = (find_global "internal.inaccessible_pattern")
let coq_block = (find_global "internal.block")
let coq_hide = (find_global "internal.hide_pattern")
let coq_hidebody = (find_global "internal.hidebody")
let coq_add_pattern = (find_global "internal.add_pattern")
let coq_end_of_section_id = Id.of_string "eos"
let coq_the_end_of_the_section = (find_global "internal.the_end_of_the_section")
let coq_end_of_section = (find_global "internal.end_of_section")

let coq_ImpossibleCall evd = find_constant "impossiblecall.class" evd

let unfold_add_pattern =
  lazy (Tactics.unfold_in_concl [(Locus.AllOccurrences,
			     EvalConstRef (Globnames.destConstRef (Lazy.force coq_add_pattern)))])

let subterm_relation_base = "subterm_relation"

let coq_sigma = (find_global "sigma.type")
let coq_sigmaI = (find_global "sigma.intro")

let init_projection gr =
  let cst = Globnames.destConstRef gr in
  let p = Option.get @@ Recordops.find_primitive_projection cst in
  Projection.make p false
			
let coq_pr1 = lazy (init_projection (Lazy.force (find_global "sigma.pr1")))
let coq_pr2 = lazy (init_projection (Lazy.force (find_global "sigma.pr2")))
			    
(* Misc tactics *)


let rec head_of_constr sigma t =
  let t = strip_outer_cast sigma (collapse_appl sigma t) in
    match kind sigma t with
    | Prod (_,_,c2)  -> head_of_constr sigma c2 
    | LetIn (_,_,_,c2) -> head_of_constr sigma c2
    | App (f,args)  -> head_of_constr sigma f
    | _      -> t

let nowhere = { onhyps = Some []; concl_occs = NoOccurrences }

(* Lifting a [rel_context] by [n]. *)
let of_tuple (x, b, t) =
  match b with
  | Some def -> Context.Rel.Declaration.LocalDef (x,def,t)
  | None -> Context.Rel.Declaration.LocalAssum (x, t)

let lift_rel_contextn k n sign =
  let open Context.Rel in
  let open Declaration in
  let rec liftrec k = function
    | rel::sign -> let (na,c,t) = to_tuple rel in
      of_tuple (na,Option.map (Vars.liftn n k) c, Vars.liftn n k t)::(liftrec (k-1) sign)
    | [] -> []
  in
  liftrec (Context.Rel.length sign + k) sign

let lift_rel_context n sign = lift_rel_contextn 0 n sign

let lift_list l = List.map (Vars.lift 1) l

(* let compute_params cst =  *)
(*   let body = constant_value (Global.env ()) cst in *)
(*   let init, n, c =  *)
(*     let ctx, body =  *)
(*       match Constr.kind body with *)
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
(*     match Constr.kind c with *)
(*     | App (f, args) -> *)
(* 	if f = mkConst cst then *)
(* 	  let _, pars' = params_of_args pars n args in *)
(* 	    pars' *)
(* 	else pars *)
(*     | _ -> pars *)
(*   in aux init n c *)



let unfold_head env sigma (ids, csts) c = 
  let rec aux c = 
    match kind sigma c with
    | Var id when Id.Set.mem id ids ->
	(match Environ.named_body id env with
	| Some b -> true, of_constr b
	| None -> false, c)
    | Const (cst,u) when Cset.mem cst csts ->
	true, of_constr (Environ.constant_value_in env (cst, EInstance.kind sigma u))
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
	let c' = EConstr.map sigma (fun c -> 
	  if !done_ then c else 
	    let x, c' = aux c in
	      done_ := x; c') c
	in !done_, c'
  in aux c

open CErrors

let autounfold_first db cl gl =
  let st =
    List.fold_left (fun (i,c) dbname -> 
      let db = try Hints.searchtable_map dbname 
	with Not_found -> user_err ~hdr:"autounfold" (str "Unknown database " ++ str dbname)
      in
      let (ids, csts) = Hints.Hint_db.unfolds db in
        (Id.Set.union ids i, Cset.union csts c)) (Id.Set.empty, Cset.empty) db
  in
  let did, c' = unfold_head (pf_env gl) (project gl) st
    (match cl with Some (id, _) -> pf_get_hyp_typ gl id | None -> pf_concl gl) 
  in
    if did then
      match cl with
      | Some hyp -> Proofview.V82.of_tactic (change_in_hyp None (make_change_arg c') hyp) gl
      | None -> Proofview.V82.of_tactic (convert_concl_no_check c' DEFAULTcast) gl
    else tclFAIL 0 (str "Nothing to unfold") gl

type hintdb_name = string

let rec db_of_constr c = match Constr.kind c with
  | Const (c,_) -> Label.to_string (Constant.label c)
  | App (c,al) -> db_of_constr c
  | _ -> assert false

let dbs_of_constrs = List.map db_of_constr

(** Bindings to Coq *)

let below_tactics_path =
  DirPath.make (List.map Id.of_string ["Below";"Equations"])

let below_tac s =
  KerName.make (MPfile below_tactics_path) (Label.make s)

let tacvar_arg h =
  let ipat = Genarg.in_gen (Genarg.rawwit Tacarg.wit_intro_pattern) 
    (CAst.make @@ Tactypes.IntroNaming (Namegen.IntroIdentifier h)) in
    TacGeneric ipat

let rec_tac h h' = 
  TacArg(CAst.(make @@ TacCall(
      make
        (qualid_of_string "Equations.Below.rec",
         [tacvar_arg h'; ConstrMayEval (Genredexpr.ConstrTerm h)]))))

let rec_wf_tac h h' rel = 
  TacArg(CAst.(make @@ TacCall(make
    (qualid_of_string "Equations.Subterm.rec_wf_eqns_rel",
    [tacvar_arg h';
     ConstrMayEval (Genredexpr.ConstrTerm h);
     ConstrMayEval (Genredexpr.ConstrTerm rel)]))))

let unfold_recursor_tac () = tac_of_string "Equations.Subterm.unfold_recursor" []

let equations_tac () = tac_of_string "Equations.DepElim.equations" []

let set_eos_tac () = tac_of_string "Equations.DepElim.set_eos" []
    
let solve_rec_tac () = tac_of_string "Equations.Equations.solve_rec" []

let find_empty_tac () = tac_of_string "Equations.DepElim.find_empty" []

let pi_tac () = tac_of_string "Equations.Subterm.pi" []

let noconf_tac () = tac_of_string "Equations.NoConfusion.solve_noconf" []

let noconf_hom_tac () = tac_of_string "Equations.NoConfusion.solve_noconf_hom" []

let eqdec_tac () = tac_of_string "Equations.EqDecInstances.eqdec_proof" []

let simpl_equations_tac () = tac_of_string "Equations.DepElim.simpl_equations" []

let specialize_mutfix_tac () = tac_of_string "Equations.FunctionalInduction.specialize_mutfix" []
  
open Libnames

let reference_of_global c = Nametab.shortest_qualid_of_global Names.Id.Set.empty c

let tacident_arg h =
  Reference (qualid_of_ident h)

let call_tac_on_ref tac c =
  let var = Names.Id.of_string "x" in
  let tac = Locus.ArgArg (dummy_loc, tac) in
  let val_reference = Geninterp.val_tag (Genarg.topwit Stdarg.wit_constr) in
  (** This is a hack to avoid generating useless universes *)
  let c = Constr.mkRef (c, Univ.Instance.empty) in
  let c = Geninterp.Val.inject val_reference (EConstr.of_constr c) in
  let ist = Geninterp.{ lfun = Names.Id.Map.add var c Names.Id.Map.empty;
                            extra = Geninterp.TacStore.empty } in
  let var = Reference (Locus.ArgVar CAst.(make var)) in
  let tac = TacArg (CAst.(make @@ TacCall (make (tac, [var])))) in
  ist, tac

let mp = Names.MPfile (Names.DirPath.make (List.map Names.Id.of_string ["DepElim"; "Equations"]))
let solve_equation = Names.KerName.make mp (Names.Label.make "solve_equation")

let solve_equation_tac (c : Names.GlobRef.t) =
  let ist, tac = call_tac_on_ref solve_equation c in
  Tacinterp.eval_tactic_ist ist tac

let impossible_call_tac c =
  let tac = Tacintern.glob_tactic
  (TacArg(CAst.(make @@ TacCall(make
  (Libnames.qualid_of_string "Equations.DepElim.impossible_call",
   [Reference (reference_of_global c)]))))) in
  let val_tac = Genarg.glbwit Tacarg.wit_tactic in
  Genarg.in_gen val_tac tac
(* let impossible_call_tac c = *)
(*   let ist, tac = call_tac_on_ref impossible_call c in *)
(*   let val_tac = Genarg.glbwit Tacarg.wit_tactic in *)
(*   let c = Genarg.in_gen val_tac tac in *)
(*   c *)

let depelim_tac h = tac_of_string "Equations.DepElim.depelim"
  [tacident_arg h]

let do_empty_tac h = tac_of_string "Equations.DepElim.do_empty"
  [tacident_arg h]

let depelim_nosimpl_tac h = tac_of_string "Equations.DepElim.depelim_nosimpl"
  [tacident_arg h]

let simpl_dep_elim_tac () = tac_of_string "Equations.DepElim.simpl_dep_elim" []

let depind_tac h = tac_of_string "Equations.DepElim.depind"
  [tacident_arg h]

open EConstr.Vars
   
let mkProd_or_subst decl c =
  let open Context.Rel.Declaration in
  match get_value decl with
    | None -> mkProd (get_name decl, get_type decl, c)
    | Some b -> subst1 b c

let mkProd_or_clear sigma decl c =
  if not (dependent sigma (mkRel 1) c) then
    subst1 mkProp c
  else mkProd_or_LetIn decl c

let it_mkProd_or_clear sigma ty ctx = 
  fold_left (fun c d -> mkProd_or_clear sigma d c) ty ctx
      
let mkLambda_or_subst decl c =
  let open Context.Rel.Declaration in
  match get_value decl with
    | None -> mkLambda (get_name decl, get_type decl, c)
    | Some b -> subst1 b c

let mkLambda_or_subst_or_clear sigma decl c =
  let open Context.Rel.Declaration in
  let (na,body,t) = to_tuple decl in
  match body with
  | None when dependent sigma (mkRel 1) c -> mkLambda (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let mkProd_or_subst_or_clear sigma decl c =
  let open Context.Rel.Declaration in
  let (na,body,t) = to_tuple decl in
  match body with
  | None when dependent sigma (mkRel 1) c -> mkProd (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let it_mkProd_or_subst env sigma ty ctx =
  nf_beta env sigma (List.fold_left
                       (fun c d -> whd_betalet sigma (mkProd_or_LetIn d c)) ty ctx)

let it_mkProd_or_clean env sigma ty ctx =
  let open Context.Rel.Declaration in
  nf_beta env sigma (List.fold_left
                       (fun c d -> whd_betalet sigma
			 (if (get_name d) == Anonymous then subst1 mkProp c
                          else mkProd_or_LetIn d c)) ty ctx)

let it_mkLambda_or_subst ty ctx = 
  whd_betalet Evd.empty
    (List.fold_left (fun c d -> mkLambda_or_LetIn d c) ty ctx)

let it_mkLambda_or_subst_or_clear sigma ty ctx = 
  (List.fold_left (fun c d -> mkLambda_or_subst_or_clear sigma d c) ty ctx)

let it_mkProd_or_subst_or_clear sigma ty ctx = 
  (List.fold_left (fun c d -> mkProd_or_subst_or_clear sigma d c) ty ctx)


let lift_constrs n cs = List.map (lift n) cs

let ids_of_constr sigma ?(all=false) vars c =
  let rec aux vars c =
    match kind sigma c with
    | Var id -> Id.Set.add id vars
    | App (f, args) -> 
	(match kind sigma f with
	| Construct ((ind,_),_)
	| Ind (ind, _) ->
            let (mib,mip) = Global.lookup_inductive ind in
	      Array.fold_left_from
		(if all then 0 else mib.Declarations.mind_nparams)
		aux vars args
	| _ -> fold sigma aux vars c)
    | _ -> fold sigma aux vars c
  in aux vars c
    
let decompose_indapp sigma f args =
  match kind sigma f with
  | Construct ((ind,_),_) 
  | Ind (ind,_) ->
      let (mib,mip) = Global.lookup_inductive ind in
      let first = mib.Declarations.mind_nparams_rec in
      let pars, args = Array.chop first args in
	mkApp (f, pars), args
  | _ -> f, args

let e_conv env evdref t t' =
  match Reductionops.infer_conv env !evdref ~pb:Reduction.CONV t t' with
  | Some sigma -> (evdref := sigma; true)
  | None -> false
  | exception Reduction.NotConvertible -> false
      
let deps_of_var sigma id env =
  Environ.fold_named_context
    (fun _ decl (acc : Id.Set.t) ->
       let n, b, t = Context.Named.Declaration.to_tuple decl in
       if Option.cata (fun x -> occur_var env sigma id (of_constr x)) false b ||
            occur_var env sigma id (of_constr t) then
        Id.Set.add n acc
      else acc)
    env ~init:Id.Set.empty
    
let idset_of_list =
  List.fold_left (fun s x -> Id.Set.add x s) Id.Set.empty

let pr_smart_global f = Pptactic.pr_or_by_notation pr_qualid f
let string_of_smart_global = function
  | {CAst.v=Constrexpr.AN ref} -> string_of_qualid ref
  | {CAst.v=Constrexpr.ByNotation (s, _)} -> s

let ident_of_smart_global x = 
  Id.of_string (string_of_smart_global x)

let pf_get_type_of               = pf_reduce Retyping.get_type_of
  
let move_after_deps id c =
  let open Context.Named.Declaration in
  let enter gl =
    let sigma = Proofview.Goal.sigma gl in
    let hyps = Proofview.Goal.hyps gl in
    let deps = collect_vars sigma c in
    let iddeps = 
      collect_vars sigma (Tacmach.New.pf_get_hyp_typ id gl) in
    let deps = Id.Set.diff deps iddeps in
    let find decl = Id.Set.mem (get_id decl) deps in
    let first = 
      match snd (List.split_when find (List.rev hyps)) with
      | a :: _ -> get_id a
      | [] -> user_err ~hdr:"move_before_deps"
        Pp.(str"Found no hypothesis on which " ++ Id.print id ++ str" depends")
    in
    Tactics.move_hyp id (Logic.MoveAfter first)
  in Proofview.Goal.enter enter

let observe s tac = 
  let open Proofview.Notations in
  if not !debug then tac
  else
    fun gls ->
    Feedback.msg_debug (str"Applying " ++ str s ++ str " on " ++ Printer.pr_goal gls);
    to82
      (Proofview.tclORELSE
         (Proofview.tclTHEN
            (of82 tac)
            (Proofview.numgoals >>= fun gls ->
             if gls = 0 then (Feedback.msg_debug (str s ++ str "succeeded"); Proofview.tclUNIT ())
             else
               (of82
                  (fun gls -> Feedback.msg_debug (str "Subgoal: " ++ Printer.pr_goal gls);
                           Evd.{ it = [gls.it]; sigma = gls.sigma }))))
         (fun iexn -> Feedback.msg_debug
                        (str"Failed with: " ++
                           (match fst iexn with
                            | Refiner.FailError (n,expl) ->
                               (str" Fail error " ++ int n ++ str " for " ++ str s ++ spc () ++ Lazy.force expl ++
                                  str " on " ++ Printer.pr_goal gls)
                            | Pretype_errors.PretypeError (env, sigma, e) ->
                               (str " Pretype error: " ++ Himsg.explain_pretype_error env sigma e)
                            | _ -> CErrors.iprint iexn));
                   Proofview.tclUNIT ())) gls

(** Compat definitions *)

type rel_context = EConstr.rel_context
type rel_declaration = EConstr.rel_declaration
type named_declaration = EConstr.named_declaration
type named_context = EConstr.named_context

let extended_rel_vect n ctx =
  Context.Rel.to_extended_vect mkRel n ctx
let extended_rel_list n ctx =
  Context.Rel.to_extended_list mkRel n ctx
let to_tuple = Context.Rel.Declaration.to_tuple
let to_named_tuple = Context.Named.Declaration.to_tuple
let of_named_tuple = Context.Named.Declaration.of_tuple
let to_context c =
  List.map of_tuple c

let get_type = Context.Rel.Declaration.get_type
let get_value = Context.Rel.Declaration.get_value
let get_name = Context.Rel.Declaration.get_name
let get_named_type = Context.Named.Declaration.get_type
let get_named_value = Context.Named.Declaration.get_value
let make_assum n t = Context.Rel.Declaration.LocalAssum (n, t)
let make_def n b t = 
  match b with
  | None -> Context.Rel.Declaration.LocalAssum (n, t)
  | Some b -> Context.Rel.Declaration.LocalDef (n, b, t)

let make_named_def n b t = 
  match b with
  | None -> Context.Named.Declaration.LocalAssum (n, t)
  | Some b -> Context.Named.Declaration.LocalDef (n, b, t)

let lookup_rel = Context.Rel.lookup

let named_of_rel_context ?(keeplets = false) default l =
  let acc, args, _, ctx =
    List.fold_right
      (fun decl (subst, args, ids, ctx) ->
        let decl = Context.Rel.Declaration.map_constr (substl subst) decl in
	let id = match get_name decl with Anonymous -> default () | Name id -> id in
	let d = Named.Declaration.of_tuple (id, get_value decl, get_type decl) in
	let args = if keeplets ||Context.Rel.Declaration.is_local_assum decl then mkVar id :: args else args in
	  (mkVar id :: subst, args, id :: ids, d :: ctx))
      l ([], [], [], [])
  in acc, rev args, ctx

let rel_of_named_context ctx = 
  List.fold_right (fun decl (ctx',subst) ->
      let (n, b, t) = to_named_tuple decl in
      let decl = make_def (Name n) (Option.map (subst_vars subst) b) (subst_vars subst t) in 
      (decl :: ctx', n :: subst)) ctx ([],[])

let empty_hint_info = Hints.empty_hint_info

(* Substitute a list of constrs [cstrs] in rel_context [ctx] for variable [k] and above. *)

open Context.Rel.Declaration
  
let map_decl f x =
  match x with
  | LocalAssum (na,x) -> LocalAssum (na, f x)
  | LocalDef (na,b,t) -> LocalDef (na, f b, f t)

let subst_rel_context k cstrs ctx = 
  let (_, ctx') = fold_right 
    (fun decl (k, ctx') ->
      (succ k, map_decl (substnl cstrs k) decl :: ctx'))
    ctx (k, [])
  in ctx'

(* A telescope is a reversed rel_context *)

let subst_telescope cstr ctx = 
  let (_, ctx') = fold_left
    (fun (k, ctx') decl ->
      (succ k, (map_decl (substnl [cstr] k) decl) :: ctx'))
    (0, []) ctx
  in rev ctx'

(* Substitute rel [n] by [c] in [ctx]
   Precondition: [c] is typable in [ctx] using variables 
   above [n] *)
    
let subst_in_ctx (n : int) (c : constr) (ctx : EConstr.rel_context) : EConstr.rel_context =
  let rec aux k after = function
    | [] -> []
    | decl :: before ->
	if k == n then (subst_rel_context 0 [lift (-k) c] (List.rev after)) @ before
	else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

let set_in_ctx (n : int) (c : constr) (ctx : EConstr.rel_context) : EConstr.rel_context =
  let rec aux k after = function
    | [] -> []
    | decl :: before ->      
      if k == n then
        (rev after) @ LocalDef (get_name decl, lift (-k) c, get_type decl) :: before
      else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

let get_id decl = Context.Named.Declaration.get_id decl

let fold_named_context_reverse = Context.Named.fold_inside
let map_rel_context = Context.Rel.map
let map_rel_declaration = Context.Rel.Declaration.map_constr
let map_named_declaration = Context.Named.Declaration.map_constr
let map_named_context = Context.Named.map
let lookup_named = Context.Named.lookup

let subst_in_named_ctx (n : Id.t) (c : constr) (ctx : EConstr.named_context) : EConstr.named_context =
  let rec aux after = function
    | [] -> []
    | decl :: before ->
       let name = get_id decl in
       if Id.equal name n then (rev after) @ before
       else aux (map_named_declaration (replace_vars [n,c]) decl :: after)
                before
  in aux [] ctx

let pp cmds = Feedback.msg_info cmds

let user_err_loc (loc, s, pp) =
  CErrors.user_err ?loc ~hdr:s pp
let error s = CErrors.user_err (str s)
let errorlabstrm s msg = CErrors.user_err ~hdr:s msg
let is_anomaly = CErrors.is_anomaly
let print_error e = CErrors.print e

let nf_betadeltaiota = nf_all
let anomaly ?label pp = CErrors.anomaly ?label pp

let evar_declare sign ev ty ?src evm =
  let evi = Evd.make_evar sign ty in
  let evi = match src with Some src -> { evi with Evd.evar_source = src }
                         | None -> evi in
  Evd.add evm ev evi

let new_evar env evm ?src ty =
  Evarutil.new_evar env evm ?src ty

let new_type_evar env evm ?src rigid =
  Evarutil.new_type_evar env evm rigid ?src
                           
let to_evar_map x = x
let of_evar_map x = x
let evar_absorb_arguments = Evardefine.evar_absorb_arguments

let hintdb_set_transparency cst b db =
  Hints.add_hints ~local:false [db] 
    (Hints.HintsTransparencyEntry (Hints.HintsReferences [EvalConstRef cst], b))

let is_global sigma f ec = Globnames.is_global f (to_constr sigma ec)                                  

let constr_of_global_univ sigma u = of_constr (Constr.mkRef (from_peuniverses sigma u))

let smash_rel_context sigma ctx =
  List.map of_rel_decl (smash_rel_context (List.map (to_rel_decl sigma) ctx))
let rel_vect n m = Array.map of_constr (rel_vect n m)

let applistc c a = applist (c, a)

let instance_constructor sigma tc args =
  Typeclasses.instance_constructor tc args

let decompose_appvect sigma t =
  match kind sigma t with
  | App (f, v) -> (f, v)
  | _ -> (t, [||])

let dest_ind_family fam =
  let ind, fam = Inductiveops.dest_ind_family fam in
  to_peuniverses ind, List.map of_constr fam

(* XXX: EConstr-versions fo these functions really needed XXX *)
let to_constr = to_constr ~abort_on_undefined_evars:false
let prod_appvect sigma p args =
  of_constr (Term.prod_appvect (to_constr sigma p) (Array.map (to_constr sigma) args))
let beta_appvect sigma p args =
  of_constr (Reduction.beta_appvect (to_constr sigma p) (Array.map (to_constr sigma) args))
let find_rectype env sigma ty =
  let Inductiveops.IndType (ind, args) = Inductiveops.find_rectype env sigma ty in
  ind, args

type identifier = Names.Id.t

let evd_comb0 f evd =
  let evm, r = f !evd in
  evd := evm; r

let evd_comb1 f evd x =
  let evm, r = f !evd x in
  evd := evm; r
