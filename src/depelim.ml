(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Context
open Vars
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type
open Decl_kinds
open Entries

open Globnames
open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Tacmach
open Namegen
open Tacticals
open Tactics
open Evd

open Equations_common
open Sigma

let lift_togethern n l =
  let l', _ =
    List.fold_right
      (fun x (acc, n) ->
	(lift n x :: acc, succ n))
      l ([], n)
  in l'

let lift_together l = lift_togethern 0 l

open Coqlib

let mk_term_eq env sigma ty t ty' t' =
  if e_conv env sigma ty ty' then
    mkEq env sigma ty t t', mkRefl env sigma ty' t'
  else
    mkHEq env sigma ty t ty' t', mkHRefl env sigma ty' t'

let make_abstract_generalize gl evd id concl dep ctx body c eqs args refls =
  let meta = Evarutil.new_meta() in
  let eqslen = List.length eqs in
  let term, typ = mkVar id, pf_get_hyp_typ gl id in
    (* Abstract by the "generalized" hypothesis equality proof if necessary. *)
  let abshypeq, abshypt =
    if dep then
      let eq, refl = mk_term_eq (push_rel_context ctx (pf_env gl)) evd (lift 1 c) (mkRel 1) typ term in
	mkProd (Anonymous, eq, lift 1 concl), [| refl |]
    else concl, [||]
  in
    (* Abstract by equalitites *)
  let eqs = lift_togethern 1 eqs in (* lift together and past genarg *)
  let abseqs = it_mkProd_or_LetIn (lift eqslen abshypeq) (List.map (fun x -> (Anonymous, None, x)) eqs) in
    (* Abstract by the "generalized" hypothesis. *)
  let genarg = mkProd_or_LetIn (Name id, body, c) abseqs in
    (* Abstract by the extension of the context *)
  let genctyp = it_mkProd_or_LetIn genarg ctx in
    (* The goal will become this product. *)
  let genc = mkCast (mkMeta meta, DEFAULTcast, genctyp) in
    (* Apply the old arguments giving the proper instantiation of the hyp *)
  let instc = mkApp (genc, Array.of_list args) in
    (* Then apply to the original instanciated hyp. *)
  let instc = Option.cata (fun _ -> instc) (mkApp (instc, [| mkVar id |])) body in
    (* Apply the reflexivity proofs on the indices. *)
  let appeqs = mkApp (instc, Array.of_list refls) in
    (* Finaly, apply the reflexivity proof for the original hyp, to get a term of type gl again. *)
    mkApp (appeqs, abshypt)

let hyps_of_vars env sign nogen hyps =
  if Idset.is_empty hyps then [] 
  else
    let (_,lh) =
      Context.fold_named_context_reverse
        (fun (hs,hl) (x,_,_ as d) ->
	  if Idset.mem x nogen then (hs,hl)
	  else if Idset.mem x hs then (hs,x::hl)
	  else
	    let xvars = global_vars_set_of_decl env d in
	      if not (Idset.equal (Idset.diff xvars hs) Idset.empty) then
		(Idset.add x hs, x :: hl)
	      else (hs, hl))
        ~init:(hyps,[])
        sign 
    in lh

exception Seen

let linear vars args = 
  let seen = ref vars in
    try 
      Array.iter (fun i -> 
	let rels = ids_of_constr ~all:true Idset.empty i in
	let seen' = 
	  Idset.fold (fun id acc ->
	    if Idset.mem id acc then raise Seen
	    else Idset.add id acc)
	    rels !seen
	in seen := seen')
	args;
      true
    with Seen -> false


let needs_generalization gl id =
  let f, args, def, id, oldid = 
    let oldid = pf_get_new_id id gl in
    let (_, b, t) = pf_get_hyp gl id in
      match b with
      | None -> let f, args = decompose_app t in
		  f, args, false, id, oldid
      | Some t -> 
	  let f, args = decompose_app t in
	    f, args, true, id, oldid
  in
    if args = [] then false
    else
      let args = Array.of_list args in
      let f', args' = decompose_indapp f args in
      let parvars = ids_of_constr ~all:true Idset.empty f' in
	if not (linear parvars args') then true
	else Array.exists (fun x -> not (isVar x)) args'
	  
	
let abstract_args gl generalize_vars dep id defined f args =
  let sigma = project gl in
  let evd = ref sigma in
  let env = pf_env gl in
  let concl = pf_concl gl in
  let dep = dep || dependent (mkVar id) concl in
  let avoid = ref [] in
  let get_id name =
    let id = fresh_id !avoid (match name with Name n -> n | Anonymous -> id_of_string "gen_x") gl in
      avoid := id :: !avoid; id
  in
    (* Build application generalized w.r.t. the argument plus the necessary eqs.
       From env |- c : forall G, T and args : G we build
       (T[G'], G' : ctx, env ; G' |- args' : G, eqs := G'_i = G_i, refls : G' = G, vars to generalize)
       
       eqs are not lifted w.r.t. each other yet. (* will be needed when going to dependent indexes *)
    *)
  let aux (prod, ctx, ctxenv, c, args, eqs, refls, nongenvars, vars, env) arg =
    let (name, _, ty), arity =
      let rel, c = Reductionops.splay_prod_n env sigma 1 prod in
	List.hd rel, c
    in
    let argty = pf_get_type_of gl arg in
    let argty = 
      Evarutil.evd_comb1
	(Evarsolve.refresh_universes (Some true) env) evd argty in
    let lenctx = List.length ctx in
    let liftargty = lift lenctx argty in
    let leq = constr_cmp Reduction.CUMUL liftargty ty in
      match kind_of_term arg with
      | Var id when leq && not (Idset.mem id nongenvars) ->
      	  (subst1 arg arity, ctx, ctxenv, mkApp (c, [|arg|]), args, eqs, refls,
      	  Idset.add id nongenvars, Idset.remove id vars, env)
      | _ ->
	  let name = get_id name in
	  let decl = (Name name, None, ty) in
	  let ctx = decl :: ctx in
	  let c' = mkApp (lift 1 c, [|mkRel 1|]) in
	  let args = arg :: args in
	  let liftarg = lift (List.length ctx) arg in
	  let eq, refl =
	    if leq then
	      mkEq env evd (lift 1 ty) (mkRel 1) liftarg,
              mkRefl env evd (lift (-lenctx) ty) arg
	    else
	      mkHEq env evd (lift 1 ty) (mkRel 1) liftargty liftarg,
              mkHRefl env evd argty arg
	  in
	  let eqs = eq :: lift_list eqs in
	  let refls = refl :: refls in
	  let argvars = ids_of_constr vars arg in
	    (arity, ctx, push_rel decl ctxenv, c', args, eqs, refls, 
	    nongenvars, Idset.union argvars vars, env)
  in 
  let f', args' = decompose_indapp f args in
  let dogen, f', args' =
    let parvars = ids_of_constr ~all:true Idset.empty f' in
      if not (linear parvars args') then true, f, args
      else
	match Array.findi (fun i x -> not (isVar x)) args' with
	| None -> false, f', args'
	| Some nonvar ->
	    let before, after = Array.chop nonvar args' in
	      true, mkApp (f', before), after
  in
    if dogen then
      let arity, ctx, ctxenv, c', args, eqs, refls, nogen, vars, env = 
	Array.fold_left aux (pf_get_type_of gl f',[],env,f',[],[],[],Idset.empty,Idset.empty,env) args'
      in
      let args, refls = List.rev args, List.rev refls in
      let vars = 
	if generalize_vars then
	  let nogen = Idset.add id nogen in
	    hyps_of_vars (pf_env gl) (pf_hyps gl) nogen vars
	else []
      in
      let body, c' = if defined then Some c', Retyping.get_type_of ctxenv Evd.empty c' else None, c' in
	Some (make_abstract_generalize gl evd id concl dep ctx body c' eqs args refls,
	     dep, succ (List.length ctx), vars)
    else None

let intro = 
  Proofview.V82.of_tactic intro
      
let abstract_generalize ?(generalize_vars=true) ?(force_dep=false) id gl =
  Coqlib.check_required_library ["Coq";"Logic";"JMeq"];
  let f, args, def, id, oldid = 
    let oldid = pf_get_new_id id gl in
    let (_, b, t) = pf_get_hyp gl id in
      match b with
      | None -> let f, args = decompose_app t in
		  f, args, false, id, oldid
      | Some t -> 
	  let f, args = decompose_app t in
	    f, args, true, id, oldid
  in
  if args = [] then tclIDTAC gl
  else 
    let args = Array.of_list args in
    let newc = abstract_args gl generalize_vars force_dep id def f args in
      match newc with
      | None -> tclIDTAC gl
      | Some (newc, dep, n, vars) -> 
	  let tac =
	    if dep then
	      tclTHENLIST [refine newc; Proofview.V82.of_tactic (rename_hyp [(id, oldid)]); 
			   tclDO n intro; 
			   generalize_dep ~with_let:true (mkVar oldid)]	      
	    else
	      tclTHENLIST [refine newc; clear [id]; tclDO n intro]
	  in 
	    if vars = [] then tac gl
	    else tclTHEN tac 
	      (fun gl -> tclFIRST [Proofview.V82.of_tactic (revert vars) ;
				   tclMAP (fun id -> 
				     tclTRY (generalize_dep ~with_let:true (mkVar id))) vars] gl) gl

let dependent_pattern ?(pattern_term=true) c gl =
  let cty = pf_hnf_type_of gl c in
  let deps =
    match kind_of_term cty with
    | App (f, args) -> 
	let f', args' = decompose_indapp f args in 
	  Array.to_list args'
    | _ -> []
  in
  let varname c = match kind_of_term c with
    | Var id -> id
    | _ -> pf_get_new_id (id_of_string (hdchar (pf_env gl) c)) gl
  in
  let env = pf_env gl in
  let mklambda (ty, evd) (c, id, cty) =
    let conclvar, evd' = 
      Find_subterm.subst_closed_term_occ env (project gl)
	(Locus.AtOccs Locus.AllOccurrences) c ty 
    in
      mkNamedLambda id cty conclvar, evd'
  in
  let subst = 
    let deps = List.rev_map (fun c -> (c, varname c, pf_get_type_of gl c)) deps in
      if pattern_term then (c, varname c, cty) :: deps
      else deps
  in
  let concllda, evd = List.fold_left mklambda (pf_concl gl, project gl) subst in
  let conclapp = applistc concllda (List.rev_map pi1 subst) in
    Proofview.V82.of_tactic (convert_concl_no_check conclapp DEFAULTcast) gl


let depcase (mind, i as ind) =
  let indid = Nametab.basename_of_global (IndRef ind) in
  let mindb, oneind = Global.lookup_inductive ind in
  let inds = List.rev (Array.to_list (Array.mapi (fun i oib -> mkInd (mind, i)) mindb.mind_packets)) in
  let ctx = oneind.mind_arity_ctxt in
  let nparams = mindb.mind_nparams in
  let args, params = List.chop (List.length ctx - nparams) ctx in
  let nargs = List.length args in
  let indapp = mkApp (mkInd ind, extended_rel_vect 0 ctx) in
  let evd = ref (Evd.from_env (Global.env())) in
  let pred = it_mkProd_or_LetIn (e_new_Type (Global.env ()) evd) 
    ((Anonymous, None, indapp) :: args)
  in
  let nconstrs = Array.length oneind.mind_nf_lc in
  let branches = 
    Array.map2_i (fun i id cty ->
      let substcty = substl inds cty in
      let (args, arity) = decompose_prod_assum substcty in
      let _, indices = decompose_app arity in
      let _, indices = List.chop nparams indices in
      let ncargs = List.length args - nparams in
      let realargs, pars = List.chop ncargs args in
      let realargs = lift_rel_context (i + 1) realargs in
      let arity = applistc (mkRel (ncargs + i + 1)) 
	(indices @ [mkApp (mkConstruct (ind, succ i), 
			  Array.append (extended_rel_vect (ncargs + i + 1) params)
			    (extended_rel_vect 0 realargs))])
      in
      let body = mkRel (1 + nconstrs - i) in
      let br = it_mkProd_or_LetIn arity realargs in
	(Name (id_of_string ("P" ^ string_of_int i)), None, br), body)
      oneind.mind_consnames oneind.mind_nf_lc
  in
  let ci = make_case_info (Global.env ()) ind RegularStyle in
  (*   ci_ind = ind; *)
  (*   ci_npar = nparams; *)
  (*   ci_cstr_nargs = oneind.mind_consnrealargs; *)
  (*   ci_cstr_ndecls = oneind.mind_consnrealdecls; *)
  (*   ci_pp_info = { ind_tags = []; cstr_tags = [||]; style = RegularStyle; } } *)
  (* in *)
  let obj i =
    mkApp (mkInd ind,
	  (Array.append (extended_rel_vect (nargs + nconstrs + i) params)
	      (extended_rel_vect 0 args)))
  in
  let ctxpred = (Anonymous, None, obj (2 + nargs)) :: args in
  let app = mkApp (mkRel (nargs + nconstrs + 3),
		  (extended_rel_vect 0 ctxpred))
  in
  let ty = it_mkLambda_or_LetIn app ctxpred in
  let case = mkCase (ci, ty, mkRel 1, Array.map snd branches) in
  let xty = obj 1 in
  let xid = Namegen.named_hd (Global.env ()) xty Anonymous in
  let body = 
    let len = 1 (* P *) + Array.length branches in
    it_mkLambda_or_LetIn case 
      ((xid, None, lift len indapp) 
	:: ((List.rev (Array.to_list (Array.map fst branches))) 
	    @ ((Name (id_of_string "P"), None, pred) :: ctx)))
  in
  let ce = Declare.definition_entry ~univs:(snd (Evd.universe_context !evd)) body in
  let kn = 
    let id = add_suffix indid "_dep_elim" in
      ConstRef (Declare.declare_constant id
		  (DefinitionEntry ce, IsDefinition Scheme))
  in Evd.from_env (Global.env ()), ctx, indapp, kn

let derive_dep_elimination env sigma (i,u) =
  let evd, ctx, ty, gref = depcase i in
  let indid = Nametab.basename_of_global (IndRef i) in
  let id = add_prefix "DependentElimination_" indid in
  let cl = dependent_elimination_class () in
  let casety = Global.type_of_global_unsafe gref in
  let poly = false in (*FIXME*)
  let args = extended_rel_vect 0 ctx in
    Equations_common.declare_instance id poly evd ctx cl [ty; prod_appvect casety args; 
				mkApp (Universes.constr_of_global gref, args)]     

let () =
  let fn env sigma c = ignore (derive_dep_elimination env sigma c) in
  Derive.(register_derive
            { derive_name = "DependentElimination";
              derive_fn = make_derive_ind fn })

let pattern_call ?(pattern_term=true) c gl =
  let env = pf_env gl in
  let cty = pf_get_type_of gl c in
  let ids = ids_of_named_context (pf_hyps gl) in
  let deps =
    match kind_of_term c with
    | App (f, args) -> Array.to_list args
    | _ -> []
  in
  let varname c = match kind_of_term c with
    | Var id -> id
    | _ -> Namegen.next_ident_away (id_of_string (Namegen.hdchar (pf_env gl) c))
	ids
  in
  let mklambda ty (c, id, cty) =
    let conclvar, _ = Find_subterm.subst_closed_term_occ env (project gl) 
      (Locus.AtOccs Locus.AllOccurrences) c ty in
      mkNamedLambda id cty conclvar
  in
  let subst = 
    let deps = List.rev_map (fun c -> (c, varname c, pf_get_type_of gl c)) deps in
      if pattern_term then (c, varname c, cty) :: deps
      else deps
  in
  let concllda = List.fold_left mklambda (pf_concl gl) subst in
  let conclapp = applistc concllda (List.rev_map pi1 subst) in
    Proofview.V82.of_tactic (convert_concl_no_check conclapp DEFAULTcast) gl

let destPolyRef c =
  match kind_of_term c with
  | Ind (ind, u) -> IndRef ind, u
  | Const (c, u) -> ConstRef c, u
  | Construct (cstr, u) -> ConstructRef cstr, u
  | _ -> raise (Invalid_argument "destPolyRef")
              
let rec compare_upto_variables t v =
  if (isVar v || isRel v) then true
  else compare_constr compare_upto_variables t v

let specialize_eqs id gl =
  let env = pf_env gl in
  let ty = pf_get_hyp_typ gl id in
  let evars = ref (project gl) in
  let unif env evars c1 c2 = Evarconv.e_conv env evars c1 c2 in
  let rec aux in_eqs ctx acc ty =
    match kind_of_term ty with
    | Prod (na, t, b) ->
	(match kind_of_term t with
	 | App (eq, [| eqty; x; y |]) when
                (Globnames.is_global (Lazy.force coq_eq) eq &&
                   (noccur_between 1 (List.length ctx) x ||
                      noccur_between 1 (List.length ctx) y)) ->
            let _, u = destPolyRef eq in
	    let c, o = if noccur_between 1 (List.length ctx) x then x, y
                       else y, x in
            let eqr = Universes.constr_of_global_univ (Lazy.force coq_eq_refl, u) in
	    let p = mkApp (eqr, [| eqty; c |]) in
	    if compare_upto_variables c o &&
                 unif (push_rel_context ctx env) evars o c then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	 | App (heq, [| eqty; x; eqty'; y |]) when
                Globnames.is_global (Lazy.force coq_heq) heq &&
                 (noccur_between 1 (List.length ctx) x ||
                    noccur_between 1 (List.length ctx) y) ->
            let _, u = destPolyRef heq in
	    let eqt, c, o =
              if noccur_between 1 (List.length ctx) x then eqty, x, y
              else eqty', y, x in
            let eqr = Universes.constr_of_global_univ (Lazy.force coq_heq_refl, u) in
	    let p = mkApp (eqr, [| eqt; c |]) in
            let env' = push_rel_context ctx env in
	    if compare_upto_variables c o && unif env' evars eqty eqty' &&
                 unif env' evars o c then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	| _ ->
	    if in_eqs then acc, in_eqs, ctx, ty
	    else
	      let e = e_new_evar (push_rel_context ctx env) evars t in
		aux false ((na, Some e, t) :: ctx) (mkApp (lift 1 acc, [| mkRel 1 |])) b)
    | t -> acc, in_eqs, ctx, ty
  in
  let acc, worked, ctx, ty = aux false [] (mkVar id) ty in
  let ctx' = nf_rel_context_evar !evars ctx in
  let ctx'' = List.map (fun (n,b,t as decl) ->
    match b with
    | Some k when isEvar k -> (n,None,t)
    | b -> decl) ctx'
  in
  let ty' = it_mkProd_or_LetIn ty ctx'' in
  let acc' = it_mkLambda_or_LetIn acc ctx'' in
  let ty' = Tacred.whd_simpl env !evars ty'
  and acc' = Tacred.whd_simpl env !evars acc' in
  let acc' = Evarutil.nf_evar !evars acc' in
  let ty' = Evarutil.nf_evar !evars ty' in
    if worked then
      tclTHENFIRST (Tacmach.internal_cut true id ty')
	(exact_no_check acc') gl
    else tclFAIL 0 (str "Nothing to do in hypothesis " ++ pr_id id) gl

let specialize_eqs id gl =
  if
    (try ignore(clear [id] gl); false
     with e when Errors.noncritical e -> true)
  then
    tclFAIL 0 (str "Specialization not allowed on dependent hypotheses") gl
  else specialize_eqs id gl
                            
