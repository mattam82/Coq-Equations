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

let solve_subterm_tac () = tac_of_string "Equations.Subterm.solve_subterm" []

let derive_subterm ind =
  let global = true in
  let sigma = Evd.empty in
  let (mind, oneind as ms) = Global.lookup_inductive ind in
  let ctx = oneind.mind_arity_ctxt in
  let len = List.length ctx in
  let params = mind.mind_nparams in
  let ctx = map_rel_context refresh_universes ctx in
  let lenargs = len - params in
  let argbinders, parambinders = list_chop lenargs ctx in
  let indapp = mkApp (mkInd ind, extended_rel_vect 0 parambinders) in
  let getargs t = snd (list_chop params (snd (decompose_app t))) in
  let inds = 
    let branches = Array.mapi (fun i ty ->
      let args, concl = decompose_prod_assum ty in
      let lenargs = List.length args in
      let lenargs' = lenargs - params in
      let args', params' = list_chop lenargs' args in
      let recargs = list_map_filter_i (fun i (n, _, t) ->
	let ctx, ar = decompose_prod_assum t in
	  match kind_of_term (fst (decompose_app ar)) with
	  | Ind ind' when ind' = ind -> 
	      Some (ctx, i, mkRel (succ i), getargs (lift (succ i) t))
	  | _ -> None) args'
      in
      let constr = mkApp (mkConstruct (ind, succ i), extended_rel_vect 0 args) in
      let constrargs = getargs concl in
      let branches = list_map_i
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
					  (lift_rel_context (succ i) ctx)) args'))
	1 recargs
      in branches) (Inductive.type_of_constructors ind ms)
    in branches
  in
  let branches = Array.fold_right (fun x acc -> x @ acc) inds [] in
  let trans_branch = 
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
  let branches = trans_branch :: branches in
  let declare_one_ind i ind branches =
    let indid = Nametab.basename_of_global (IndRef ind) in
    let subtermid = add_suffix indid "_direct_subterm" in
    let constructors = map (fun (i, j, constr) -> constr) branches in
    let consnames = map (fun (i, j, _) ->
      add_suffix subtermid ("_" ^ string_of_int i ^ "_" ^ string_of_int j))
      branches 
    in
    let lenargs = List.length argbinders in
    let liftedbinders = lift_rel_context lenargs argbinders in
    let binders = liftedbinders @ argbinders in
    let appparams = mkApp (mkInd ind, extended_rel_vect (2 * lenargs) parambinders) in
    let arity = it_mkProd_or_LetIn
      (mkProd (Anonymous, mkApp (appparams, extended_rel_vect lenargs argbinders),
	      mkProd (Anonymous, lift 1 (mkApp (appparams, extended_rel_vect 0 argbinders)),
		     mkProp)))
      binders
    in
      { mind_entry_typename = subtermid;
	mind_entry_arity = arity;
	mind_entry_consnames = consnames;	      
	mind_entry_lc = constructors }
  in
  let declare_ind () =
    let inds = [declare_one_ind 0 ind branches] in
    let inductive =
      { mind_entry_record = false;
	mind_entry_finite = true;
	mind_entry_params = map (fun (n, b, t) -> 
	  match b with
	  | Some b -> (out_name n, LocalDef (refresh_universes b)) 
	  | None -> (out_name n, LocalAssum (refresh_universes t)))
	  parambinders;
	mind_entry_inds = inds }
    in
    let k = Command.declare_mutual_inductive_with_eliminations Declare.KernelSilent inductive [] in
    let subind = mkInd (k,0) in
    let constrhints = 
      list_map_i (fun i entry -> 
	list_map_i (fun j _ -> None, true, mkConstruct ((k,i),j)) 1 entry.mind_entry_lc)
	0 inds 
    in Auto.add_hints false [subterm_relation_base]
      (Auto.HintsResolveEntry (List.concat constrhints));
      (* Proof of Well-foundedness *)
      let id = add_prefix "well_founded_" (List.hd inds).mind_entry_typename in
      let relid = add_suffix (Nametab.basename_of_global (IndRef ind)) "_subterm" in
      let evm = ref Evd.empty in
      let env = Global.env () in
      let env' = push_rel_context parambinders env in
      let kl = Option.get (Typeclasses.class_of_constr (Lazy.force coq_wellfounded_class)) in
      let Some body, ty =
	let ty, rel = 
	  if argbinders = [] then
	    (* Standard homogeneous well-founded relation *)
	    indapp, mkApp (subind, extended_rel_vect 0 parambinders)
	  else
	    (* Construct a family relation by packaging all indexes into 
	       a sigma type *)
	    let _, _, indices, indexproj, valproj, valsig, typesig = sigmaize env' sigma indapp in
	    let subrel = 
	      let valproj = lift 2 valproj in
	      let liftindices = map (liftn 2 2) indices in
	      let yindices = map (subst1 (mkApp (lift 2 indexproj, [| mkRel 1 |]))) liftindices in
	      let xindices = map (subst1 (mkApp (lift 2 indexproj, [| mkRel 2 |]))) liftindices in
	      let apprel = 
		applistc subind (extended_rel_list 2 parambinders @
				    (xindices @ yindices @
					[mkApp (valproj, [| mkRel 2 |]); mkApp (valproj, [| mkRel 1 |])]))
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
	  let def = it_mkLambda_or_LetIn rel
(* 	    (mkApp (Lazy.force coq_clos_trans, [| ty; rel |])) *)
	    parambinders 
	  in
	  let ty = Some (it_mkProd_or_LetIn
			    (mkApp (Lazy.force coq_relation, [| ty |]))
			    parambinders) 
	  in
	  let cst = declare_constant relid def ty (Decl_kinds.IsDefinition Decl_kinds.Definition) in
	    (* Impargs.declare_manual_implicits false (ConstRef cst) ~enriching:false *)
	    (* 	(list_map_i (fun i _ -> ExplByPos (i, None), (true, true, true)) 1 parambinders); *)
	    Auto.add_hints false [subterm_relation_base] 
	      (Auto.HintsUnfoldEntry [EvalConstRef cst]);
	    mkApp (mkConst cst, extended_rel_vect 0 parambinders)
	in
	let evar = e_new_evar evm env'
	  (mkApp (Lazy.force coq_wellfounded, [| ty; relation |]))
	in Typeclasses.instance_constructor kl [ ty; relation; evar ]
      in
      let ty = it_mkProd_or_LetIn ty parambinders in
      let body = it_mkLambda_or_LetIn body parambinders in
      let hook vis gr =
	let cst = match gr with ConstRef kn -> kn | _ -> assert false in
	let inst = Typeclasses.new_instance kl None global (ConstRef cst) in
	  Typeclasses.add_instance inst
      in
      let obls, _, constr, typ = Eterm.eterm_obligations env id !evm !evm 0 body ty in
	Subtac_obligations.add_definition id ~term:constr typ
	  ~kind:(Decl_kinds.Global,false,Decl_kinds.Instance) 
	  ~hook ~tactic:(solve_subterm_tac ()) obls
  in ignore(declare_ind ())
    
VERNAC COMMAND EXTEND Derive_Subterm
| [ "Derive" "Subterm" "for" constr(c) ] -> [ 
    let c' = Constrintern.interp_constr Evd.empty (Global.env ()) c in
      match kind_of_term c' with
      | Ind i -> derive_subterm i
      | _ -> error "Expected an inductive type"
  ]
END

let derive_below ind =
  let mind, oneind = Global.lookup_inductive ind in
  let ctx = oneind.mind_arity_ctxt in
  let len = List.length ctx in
  let params = mind.mind_nparams in
  let argsvect = rel_vect 0 len in
  let indty = mkApp (mkInd ind, argsvect) in
  let binders = (Name (id_of_string "c"), None, indty) :: ctx in
  let argbinders, parambinders = list_chop (succ len - params) binders in
  let arity = it_mkProd_or_LetIn (new_Type ()) argbinders in
  let aritylam = it_mkLambda_or_LetIn (new_Type ()) argbinders in
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
      let nargs = constructor_nrealargs (Global.env ()) (ind, succ i) in
      let recarg = mkVar recid in
      let args, _ = decompose_prod_assum (substl [mkInd ind] ty) in
      let args, _ = list_chop (List.length args - params) args in
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
	      if t = recarg then 
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
	    if t = recarg then 
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
      mkCase ({
	ci_ind = ind;
	ci_npar = params;
	ci_cstr_nargs = Array.map pi1 branches;
	ci_pp_info = { ind_nargs = oneind.mind_nrealargs; style = RegularStyle }
      }, aritylam, mkRel 1, Array.map pi2 branches)
    and caseb =
      mkCase ({
	ci_ind = ind;
	ci_npar = params;
	ci_cstr_nargs = Array.map pi1 branches;
	ci_pp_info = { ind_nargs = oneind.mind_nrealargs; style = RegularStyle }
      }, aritylamb, mkRel 1, Array.map pi3 branches)
    in 
      it_mkLambda_or_LetIn caseB binders, it_mkLambda_or_LetIn caseb binders
  in
  let fixB = mkFix (([| len |], 0), ([| Name recid |], [| arity |], [| subst_vars [recid; pid] termB |])) in
  let bodyB = it_mkLambda_or_LetIn fixB (pdecl :: parambinders) in
  let id = add_prefix "Below_" (Nametab.basename_of_global (IndRef ind)) in
  let below = declare_constant id bodyB None (Decl_kinds.IsDefinition Decl_kinds.Definition) in
  let fixb = mkFix (([| len |], 0), ([| Name recid |], [| arityb |], 
				    [| subst_vars [recid; stepid] termb |])) in
  let stepdecl = 
    let stepty = mkProd (Anonymous, mkApp (mkConst below, paramspargs),
			mkApp (mkVar pid, Array.map (lift 1) argsvect))
    in Name stepid, None, it_mkProd_or_LetIn stepty argbinders
  in
  let bodyb = 
    it_mkLambda_or_LetIn (subst_vars [pid] (mkLambda_or_LetIn stepdecl fixb)) (pdecl :: parambinders)
  in
  let bodyb = replace_vars [belowid, mkConst below] bodyb in
  let id = add_prefix "below_" (Nametab.basename_of_global (IndRef ind)) in
    ignore(declare_constant id bodyb None (Decl_kinds.IsDefinition Decl_kinds.Definition))
    

VERNAC COMMAND EXTEND Derive_Below
| [ "Derive" "Below" "for" constr(c) ] -> [ 
  let c' = Constrintern.interp_constr Evd.empty (Global.env ()) c in
    match kind_of_term c' with
    | Ind i -> derive_below i
    | _ -> error "Expected an inductive type"
  ]
END
