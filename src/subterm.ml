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
open Util
open Entries
open Context
open Vars
open Globnames

open Equations_common
open Sigma

let (=) (x : int) (y : int) = x == y

let solve_subterm_tac () = tac_of_string "Equations.Subterm.solve_subterm" []

let refresh_universes t = t (* MS: FIXME *)

let derive_subterm ind =
  let global = true in
  let poly = Flags.is_universe_polymorphism () in
  let sigma = Evd.from_env (Global.env ()) in
  let (mind, oneind as ms) = Global.lookup_pinductive ind in
  let ctx = oneind.mind_arity_ctxt in
  let len = List.length ctx in
  let params = mind.mind_nparams in
  (* let ctx = map_rel_context refresh_universes ctx in FIXME *)
  let lenargs = len - params in
  let argbinders, parambinders = List.chop lenargs ctx in
  let indapp = mkApp (mkIndU ind, extended_rel_vect 0 parambinders) in
  let getargs t = snd (List.chop params (snd (decompose_app t))) in
  let inds = 
    let branches = Array.mapi (fun i ty ->
      let args, concl = decompose_prod_assum ty in
      let lenargs = List.length args in
      let lenargs' = lenargs - params in
      let args', params' = List.chop lenargs' args in
      let recargs = CList.map_filter_i (fun i (n, _, t) ->
	let ctx, ar = decompose_prod_assum t in
	  match kind_of_term (fst (decompose_app ar)) with
	  | Ind (ind',_) when eq_ind ind' (fst ind) -> 
	      Some (ctx, i, mkRel (succ i), getargs (lift (succ i) ar))
	  | _ -> None) args'
      in
      let constr = mkApp (mkConstructUi (ind, succ i), extended_rel_vect 0 args) in
      let constrargs = getargs concl in
      let branches = List.map_i
	(fun j (ctx, i', r, rargs) ->
	  let ctxlen = List.length ctx in
	  let subargs = 
	    Array.of_list ((extended_rel_list (lenargs' + ctxlen) 
			       parambinders) 
			    @ rargs @ (map (lift ctxlen) constrargs) @ 
			    [mkApp (lift ctxlen r, extended_rel_vect 0 ctx) ;
			     lift ctxlen constr])
	  in
	  let relapp = mkApp (mkRel (succ lenargs + ctxlen), subargs) in
	    (i, j, it_mkProd_or_LetIn (it_mkProd_or_LetIn relapp 
					  (lift_rel_context (succ i') ctx)) args'))
	1 recargs
      in branches) (Inductive.type_of_constructors ind ms)
    in branches
  in
  let branches = Array.fold_right (fun x acc -> x @ acc) inds [] in
  let _trans_branch = 
    let liftargbinders = lift_rel_context lenargs argbinders in
    let liftargbinders' = lift_rel_context lenargs liftargbinders in
    let indapp n = (mkApp (lift (3 * lenargs + n) indapp, extended_rel_vect (n + (2 - n) * lenargs) argbinders)) in
    let terms = [(Name (id_of_string "z"), None, indapp 2);
		 (Name (id_of_string "y"), None, indapp 1);
		 (Name (id_of_string "x"), None, indapp 0)]
    in
    let binders = terms @ liftargbinders' @ liftargbinders @ argbinders in
    let lenbinders = 3 * succ lenargs in
    let xy =
      (mkApp (mkRel (succ lenbinders + params),
	      Array.of_list
		(extended_rel_list lenbinders parambinders @
		   extended_rel_list (2 * lenargs + 3) argbinders @
		   extended_rel_list (lenargs + 3) argbinders @
		   [mkRel 3; mkRel 2])))
    and yz = 
      (mkApp (mkRel (succ lenbinders + params), 
	      Array.of_list
		(extended_rel_list lenbinders parambinders @
		   extended_rel_list (lenargs + 3) argbinders @
		   extended_rel_list 3 argbinders @
		   [mkRel 2; mkRel 1])))
    and xz =
      (mkApp (mkRel (succ lenbinders + params),
	      Array.of_list
		(extended_rel_list lenbinders parambinders @
		   extended_rel_list (2 * lenargs + 3) argbinders @
		   extended_rel_list 3 argbinders @
		   [mkRel 3; mkRel 1])))
    in
      (0, 0, 
       it_mkProd_or_LetIn (mkProd (Anonymous, xy, mkProd (Anonymous, lift 1 yz, lift 2 xz))) binders)
  in
  let branches = (* trans_branch ::  *)branches in
  let declare_one_ind i ind branches =
    let indid = Nametab.basename_of_global (Globnames.IndRef (fst ind)) in
    let subtermid = add_suffix indid "_direct_subterm" in
    let constructors = map (fun (i, j, constr) -> constr) branches in
    let consnames = map (fun (i, j, _) ->
      add_suffix subtermid ("_" ^ string_of_int i ^ "_" ^ string_of_int j))
      branches 
    in
    let lenargs = List.length argbinders in
    let liftedbinders = lift_rel_context lenargs argbinders in
    let binders = liftedbinders @ argbinders in
    let appparams = mkApp (mkIndU ind, extended_rel_vect (2 * lenargs) parambinders) in
    let arity = it_mkProd_or_LetIn
      (mkProd (Anonymous, mkApp (appparams, extended_rel_vect lenargs argbinders),
	      mkProd (Anonymous, lift 1 (mkApp (appparams, extended_rel_vect 0 argbinders)),
		     mkProp)))
      binders
    in
      { mind_entry_template = false;
	mind_entry_typename = subtermid;
	mind_entry_arity = arity;
	mind_entry_consnames = consnames;	      
	mind_entry_lc = constructors }
  in
  let pl, uctx = Evd.universe_context sigma in
  let declare_ind () =
    let inds = [declare_one_ind 0 ind branches] in
    let inductive =
      { mind_entry_record = None;
	mind_entry_finite = Decl_kinds.Finite;
	mind_entry_params = map (fun (n, b, t) -> 
	  match b with
	  | Some b -> (out_name n, LocalDef (refresh_universes b)) 
	  | None -> (out_name n, LocalAssum (refresh_universes t)))
	  parambinders;
	mind_entry_inds = inds;
	mind_entry_polymorphic = poly;
	mind_entry_private = None;
	mind_entry_universes = uctx }
    in
    let k = Command.declare_mutual_inductive_with_eliminations inductive pl [] in
    let subind = mkInd (k,0) in
    let constrhints = 
      List.map_i (fun i entry -> 
	List.map_i (fun j _ -> None, poly, true, Hints.PathAny, 
	  Hints.IsGlobRef (ConstructRef ((k,i),j))) 1 entry.mind_entry_lc)
	0 inds 
    in Hints.add_hints false [subterm_relation_base]
      (Hints.HintsResolveEntry (List.concat constrhints));
      (* Proof of Well-foundedness *)
      let relid = add_suffix (Nametab.basename_of_global (IndRef (fst ind))) "_subterm" in
      let id = add_prefix "well_founded_" relid in
      let evm = ref sigma in
      let env = Global.env () in
      let env' = push_rel_context parambinders env in
      let kl = get_class (Lazy.force coq_wellfounded_class) in
      let body, ty =
	let ty, rel = 
	  if List.is_empty argbinders then
	    (* Standard homogeneous well-founded relation *)
	    indapp, mkApp (subind, extended_rel_vect 0 parambinders)
	  else
	    (* Construct a family relation by packaging all indexes into 
	       a sigma type *)
	    let _, _, indices, indexproj, valproj, valsig, typesig = sigmaize env' evm indapp in
	    let subrel = 
	      let liftindices = map (liftn 2 2) indices in
	      let yindices = map (subst1 (mkProj (indexproj, mkRel 1))) liftindices in
	      let xindices = map (subst1 (mkProj (indexproj, mkRel 2))) liftindices in
	      let apprel = 
		applistc subind (extended_rel_list 2 parambinders @
				    (xindices @ yindices @
					[mkProj (valproj, mkRel 2); mkProj (valproj, mkRel 1)]))
	      in 
		mkLambda (Name (id_of_string "x"), typesig,
			 mkLambda (Name (id_of_string "y"), lift 1 typesig,
				  apprel))
	    in
	    let typesig = Tacred.simpl env' !evm typesig in
	    let subrel = Tacred.simpl env' !evm subrel in
	      typesig, subrel
	in
	let relation =
	  let def = it_mkLambda_or_LetIn 
	    (mkApp (Lazy.force coq_clos_trans, [| ty; rel |]))
	    parambinders 
	  in
	  let ty = Some (it_mkProd_or_LetIn
			    (mkApp (Lazy.force coq_relation, [| ty |]))
			    parambinders) 
	  in
	  let cst = declare_constant relid def ty poly !evm
	    (Decl_kinds.IsDefinition Decl_kinds.Definition) in
	    (* Impargs.declare_manual_implicits false (ConstRef cst) ~enriching:false *)
	    (* 	(list_map_i (fun i _ -> ExplByPos (i, None), (true, true, true)) 1 parambinders); *)
	    Hints.add_hints false [subterm_relation_base] 
	      (Hints.HintsUnfoldEntry [EvalConstRef cst]);
	    mkApp (mkConst cst, extended_rel_vect 0 parambinders)
	in
	let evar = 
	  let evt = (mkApp (Lazy.force coq_wellfounded, [| ty; relation |])) in
	    e_new_evar env' evm evt
	in Typeclasses.instance_constructor kl [ ty; relation; evar ]
      in
      let ty = it_mkProd_or_LetIn ty parambinders in
      let body = it_mkLambda_or_LetIn (Option.get body) parambinders in
      let hook vis gr _ =
	let cst = match gr with ConstRef kn -> kn | _ -> assert false in
	let inst = Typeclasses.new_instance (fst kl) None global poly (ConstRef cst) in
	  Typeclasses.add_instance inst
      in
      let _bodyty = Typing.e_type_of (Global.env ()) evm body in
      let _ty' = Typing.e_type_of (Global.env ()) evm ty in
      let obls, _, constr, typ = 
	Obligations.eterm_obligations env id !evm 0 body ty 
      in
      let ctx = Evd.evar_universe_context !evm in
	Obligations.add_definition id ~term:constr typ ctx
	  ~kind:(Decl_kinds.Global,poly,Decl_kinds.Instance) 
	  ~hook:(Lemmas.mk_hook hook) ~tactic:(solve_subterm_tac ()) obls
  in ignore(declare_ind ())
    
let derive_below ctx (ind,u) =
  let env = Global.env () in
  let evd = ref (Evd.from_ctx ctx) in
  let mind, oneind = Global.lookup_inductive ind in
  let ctx = oneind.mind_arity_ctxt in
  let len = List.length ctx in
  let params = mind.mind_nparams in
  let argsvect = rel_vect 0 len in
  let indty = mkApp (mkInd ind, argsvect) in
  let binders = (Name (id_of_string "c"), None, indty) :: ctx in
  let argbinders, parambinders = List.chop (succ len - params) binders in
  let u = Evarutil.e_new_Type ~rigid:Evd.univ_rigid env evd in
  let arity = it_mkProd_or_LetIn u argbinders in
  let aritylam = it_mkLambda_or_LetIn u argbinders in
  let paramsvect = Array.map (lift 1) (rel_vect (succ len - params) params) in
  let argsvect = rel_vect 0 (succ len - params) in
  let pid = id_of_string "P" in
  let pdecl = Name pid, None, arity in
  let stepid = id_of_string "step" in
  let recid = id_of_string "rec" in
  let belowid = id_of_string "below" in
  let paramspargs = Array.append (Array.append paramsvect [| mkVar pid |]) argsvect in
  let tyb = mkApp (mkVar belowid, paramspargs) in
  let arityb = it_mkProd_or_LetIn tyb argbinders in
  let aritylamb = it_mkLambda_or_LetIn tyb argbinders in
  let termB, termb = 
    let branches = Array.mapi (fun i ty ->
      let nargs = constructor_nrealargs (ind, succ i) in
      let recarg = mkVar recid in
      let args, _ = decompose_prod_assum (substl [mkInd ind] ty) in
      let args, _ = List.chop (List.length args - params) args in
      let ty' = substl [recarg] ty in
      let args', _ = decompose_prod_assum ty' in
      let arg_tys = fst (List.fold_left (fun (acc, n) (_,_,t) ->
	((mkRel n, lift n t) :: acc, succ n)) ([], 1) args')
      in
      let fold_unit f args =
	let res = 
	  List.fold_left (fun acc x ->
	    match acc with
	    | Some (c, ty) -> f (fun (c', ty') -> 
		mkApp (Lazy.force coq_pair, [| ty' ; ty ; c' ; c |]),
		mkApp (Lazy.force coq_prod, [| ty' ; ty |])) x
	    | None -> f (fun x -> x) x)
	    None args
	in Option.cata (fun x -> x) (Lazy.force coq_tt, Lazy.force coq_unit) res
      in
      let bodyB =
	let _, res =
	  fold_unit (fun g (c, t) -> 
	    let t, args = decompose_app t in
	    let args = Array.of_list (args @ [ c ]) in
	      if eq_constr t recarg then 
		Some (g (mkRel 0, 
			mkApp (Lazy.force coq_prod, 
			      [| mkApp (mkVar pid, args) ; 
				 mkApp (mkVar recid, args) |])))
	      else None) arg_tys
	in res
      and bodyb =
	fold_unit (fun g (c, t) -> 
	  let t, args = decompose_app t in
	  let args = Array.of_list (args @ [ c ]) in
	    if eq_constr t recarg then 
	      let reccall = mkApp (mkVar recid, args) in
	      let ty = mkApp (Lazy.force coq_prod, 
			     [| mkApp (mkVar pid, args) ; 
				mkApp (mkVar belowid, Array.append [| mkVar pid |] args) |])
	      in
		Some (g (mkApp (Lazy.force coq_pair, 
			       [| mkApp (mkVar pid, args) ; 
				  mkApp (mkVar belowid, Array.append [| mkVar pid |] args) ;
				  mkApp (mkApp (mkVar stepid, args), [| reccall |]);
				  reccall |]), ty))
	    else None) arg_tys
      in (nargs, it_mkLambda_or_LetIn bodyB args, it_mkLambda_or_LetIn (fst bodyb) args)) oneind.mind_nf_lc
    in
    let caseB =
      mkCase (make_case_info env ind RegularStyle, aritylam, mkRel 1, Array.map pi2 branches)
    and caseb =
      mkCase (make_case_info env ind RegularStyle, aritylamb, mkRel 1, Array.map pi3 branches)
    in 
      it_mkLambda_or_LetIn caseB binders, it_mkLambda_or_LetIn caseb binders
  in
  let fixB = mkFix (([| len |], 0), ([| Name recid |], [| arity |], 
				     [| subst_vars [recid; pid] termB |])) in
  let bodyB = it_mkLambda_or_LetIn fixB (pdecl :: parambinders) in
  let id = add_prefix "Below_" (Nametab.basename_of_global (IndRef ind)) in
  let poly = Flags.is_universe_polymorphism () in
  let below = declare_constant id bodyB None poly !evd
    (Decl_kinds.IsDefinition Decl_kinds.Definition) in
  let fixb = mkFix (([| len |], 0), ([| Name recid |], [| arityb |], 
				    [| subst_vars [recid; stepid] termb |])) in
  let stepdecl = 
    let stepty = mkProd (Anonymous, mkApp (mkConst below, paramspargs),
			mkApp (mkVar pid, Array.map (lift 1) argsvect))
    in Name stepid, None, it_mkProd_or_LetIn stepty argbinders
  in
  let bodyb = 
    it_mkLambda_or_LetIn
      (subst_vars [pid] (mkLambda_or_LetIn stepdecl fixb))
      (pdecl :: parambinders)
  in
  let bodyb = replace_vars [belowid, mkConst below] bodyb in
  let id = add_prefix "below_" (Nametab.basename_of_global (IndRef ind)) in
  let evd = if poly then !evd else Evd.from_env (Global.env ()) in
    ignore(declare_constant id bodyb None poly evd
	     (Decl_kinds.IsDefinition Decl_kinds.Definition))
    
