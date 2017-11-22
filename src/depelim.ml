(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Reductionops
open Pp
open Decl_kinds
open Entries

open Globnames
open Evarutil
open Tacmach
open Namegen
open Tacticals
open Tactics
open Evd

open Equations_common
open EConstr
open Vars

let lift_togethern n l =
  let l', _ =
    List.fold_right
      (fun x (acc, n) ->
	(lift n x :: acc, succ n))
      l ([], n)
  in l'

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
  let abseqs = it_mkProd_or_LetIn (lift eqslen abshypeq) (List.map (fun x -> make_assum Anonymous x) eqs) in
    (* Abstract by the "generalized" hypothesis. *)
  let genarg = mkProd_or_LetIn (make_def (Name id) body c) abseqs in
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

let hyps_of_vars env sigma sign nogen hyps =
  if Id.Set.is_empty hyps then []
  else
    let (_,lh) =
      fold_named_context_reverse
        (fun (hs,hl) decl ->
           let x = get_id decl in
          if Id.Set.mem x nogen then (hs,hl)
          else if Id.Set.mem x hs then (hs,x::hl)
	  else
            let xvars = global_vars_set_of_decl env sigma decl in
              if not (Id.Set.equal (Id.Set.diff xvars hs) Id.Set.empty) then
                (Id.Set.add x hs, x :: hl)
	      else (hs, hl))
        ~init:(hyps,[])
        sign 
    in lh

exception Seen

let linear sigma vars args =
  let seen = ref vars in
    try 
      Array.iter (fun i -> 
        let rels = ids_of_constr ~all:true sigma Id.Set.empty i in
	let seen' = 
          Id.Set.fold (fun id acc ->
            if Id.Set.mem id acc then raise Seen
            else Id.Set.add id acc)
	    rels !seen
	in seen := seen')
	args;
      true
    with Seen -> false


let needs_generalization gl id =
  let sigma = gl.sigma in
  let f, args, def, id, oldid = 
    let oldid = pf_get_new_id id gl in
    let (_, b, t) = to_named_tuple (pf_get_hyp gl id) in
      match b with
      | None -> let f, args = decompose_app sigma t in
		  f, args, false, id, oldid
      | Some t -> 
          let f, args = decompose_app sigma t in
	    f, args, true, id, oldid
  in
    if args = [] then false
    else
      let args = Array.of_list args in
      let f', args' = decompose_indapp sigma f args in
      let parvars = ids_of_constr ~all:true sigma Id.Set.empty f' in
        if not (linear sigma parvars args') then true
        else Array.exists (fun x -> not (isVar sigma x)) args'
	  
	
let abstract_args gl generalize_vars dep id defined f args =
  let sigma = project gl in
  let evd = ref sigma in
  let env = pf_env gl in
  let concl = pf_concl gl in
  let dep = dep || dependent sigma (mkVar id) concl in
  let avoid = ref Id.Set.empty in
  let get_id name =
    let id = fresh_id !avoid (match name with Name n -> n | Anonymous -> Id.of_string "gen_x") gl in
      avoid := Id.Set.add id !avoid; id
  in
    (* Build application generalized w.r.t. the argument plus the necessary eqs.
       From env |- c : forall G, T and args : G we build
       (T[G'], G' : ctx, env ; G' |- args' : G, eqs := G'_i = G_i, refls : G' = G, vars to generalize)
       
       eqs are not lifted w.r.t. each other yet. (* will be needed when going to dependent indexes *)
    *)
  let aux (prod, ctx, ctxenv, c, args, eqs, refls, nongenvars, vars, env) arg =
    let (name, _, ty), arity =
      let rel, c = Reductionops.splay_prod_n env sigma 1 prod in
	to_tuple (List.hd rel), c
    in
    let argty = pf_get_type_of gl arg in
    let argty = 
      Evarutil.evd_comb1
	(Evarsolve.refresh_universes (Some true) env) evd argty in
    let lenctx = List.length ctx in
    let liftargty = lift lenctx argty in
    let leq = constr_cmp sigma Reduction.CUMUL liftargty ty in
      match kind sigma arg with
      | Var id when leq && not (Id.Set.mem id nongenvars) ->
      	  (subst1 arg arity, ctx, ctxenv, mkApp (c, [|arg|]), args, eqs, refls,
          Id.Set.add id nongenvars, Id.Set.remove id vars, env)
      | _ ->
	  let name = get_id name in
	  let decl = make_assum (Name name) ty in
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
          let argvars = ids_of_constr sigma vars arg in
	    (arity, ctx, push_rel decl ctxenv, c', args, eqs, refls, 
            nongenvars, Id.Set.union argvars vars, env)
  in 
  let f', args' = decompose_indapp sigma f args in
  let dogen, f', args' =
    let parvars = ids_of_constr sigma ~all:true Id.Set.empty f' in
      if not (linear sigma parvars args') then true, f, args
      else
        match Array.findi (fun i x -> not (isVar sigma x)) args' with
	| None -> false, f', args'
	| Some nonvar ->
	    let before, after = Array.chop nonvar args' in
	      true, mkApp (f', before), after
  in
    if dogen then
      let arity, ctx, ctxenv, c', args, eqs, refls, nogen, vars, env = 
        Array.fold_left aux (pf_get_type_of gl f',[],env,f',[],[],[],Id.Set.empty,Id.Set.empty,env) args'
      in
      let args, refls = List.rev args, List.rev refls in
      let vars = 
	if generalize_vars then
          let nogen = Id.Set.add id nogen in
            hyps_of_vars (pf_env gl) (project gl) (pf_hyps gl) nogen vars
	else []
      in
      let body, c' = if defined then Some c', Retyping.get_type_of ctxenv Evd.empty c' else None, c' in
	Some (make_abstract_generalize gl evd id concl dep ctx body c' eqs args refls,
	     dep, succ (List.length ctx), vars)
    else None

let abstract_generalize ?(generalize_vars=true) ?(force_dep=false) id gl =
  Coqlib.check_required_library ["Coq";"Logic";"JMeq"];
  let sigma = gl.sigma in
  let f, args, def, id, oldid = 
    let oldid = pf_get_new_id id gl in
    let (_, b, t) = to_named_tuple (pf_get_hyp gl id) in
      match b with
      | None -> let f, args = decompose_app sigma t in
		  f, args, false, id, oldid
      | Some t -> 
          let f, args = decompose_app sigma t in
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
			   tclDO n (to82 intro); 
			   to82 (generalize_dep ~with_let:true (mkVar oldid))]
	    else
	      tclTHENLIST [refine newc; to82 (clear [id]); tclDO n (to82 intro)]
	  in 
	    if vars = [] then tac gl
	    else tclTHEN tac 
	      (fun gl -> tclFIRST [Proofview.V82.of_tactic (revert vars) ;
				   tclMAP (fun id -> 
				     tclTRY (to82 (generalize_dep ~with_let:true (mkVar id)))) vars] gl) gl

let dependent_pattern ?(pattern_term=true) c gl =
  let sigma = gl.sigma in
  let cty = pf_hnf_type_of gl c in
  let deps =
    match kind sigma cty with
    | App (f, args) -> 
        let f', args' = decompose_indapp sigma f args in
	  Array.to_list args'
    | _ -> []
  in
  let varname c = match kind sigma c with
    | Var id -> id
    | _ -> pf_get_new_id (Id.of_string (hdchar (pf_env gl) (project gl) c)) gl
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

let depcase poly (mind, i as ind) =
  let indid = Nametab.basename_of_global (IndRef ind) in
  let mindb, oneind = Global.lookup_inductive ind in
  let inds = List.rev (Array.to_list (Array.mapi (fun i oib -> mkInd (mind, i)) mindb.mind_packets)) in
  let ctx = oneind.mind_arity_ctxt in
  let nparams = mindb.mind_nparams in
  let ctx = List.map of_rel_decl ctx in
  let args, params = List.chop (List.length ctx - nparams) ctx in
  let nargs = List.length args in
  let indapp = mkApp (mkInd ind, extended_rel_vect 0 ctx) in
  let evd = ref (Evd.from_env (Global.env())) in
  let pred = it_mkProd_or_LetIn (e_new_Type (Global.env ()) evd) 
    (make_assum Anonymous indapp :: args)
  in
  let nconstrs = Array.length oneind.mind_nf_lc in
  let branches = 
    Array.map2_i (fun i id cty ->
      let substcty = substl inds (of_constr cty) in
      let (args, arity) = decompose_prod_assum !evd substcty in
      let _, indices = decompose_app !evd arity in
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
        (make_assum (Name (Id.of_string ("P" ^ string_of_int i))) br), body)
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
  let ctxpred = make_assum Anonymous (obj (2 + nargs)) :: args in
  let app = mkApp (mkRel (nargs + nconstrs + 3),
		  (extended_rel_vect 0 ctxpred))
  in
  let ty = it_mkLambda_or_LetIn app ctxpred in
  let case = mkCase (ci, ty, mkRel 1, Array.map snd branches) in
  let xty = obj 1 in
  let xid = Namegen.named_hd (Global.env ()) !evd xty Anonymous in
  let body = 
    let len = 1 (* P *) + Array.length branches in
    it_mkLambda_or_LetIn case 
      (make_assum xid (lift len indapp) 
	:: ((List.rev (Array.to_list (Array.map fst branches))) 
            @ (make_assum (Name (Id.of_string "P")) pred :: ctx)))
  in
  let univs = Evd.const_univ_entry ~poly !evd in
  let ce = Declare.definition_entry ~univs (EConstr.to_constr !evd body) in
  let kn = 
    let id = add_suffix indid "_dep_elim" in
      ConstRef (Declare.declare_constant id
		  (DefinitionEntry ce, IsDefinition Scheme))
  in
  let env = (Global.env ()) in (* Refresh after declare constant *)
  env, Evd.from_env env, ctx, indapp, kn

let derive_dep_elimination env sigma ~polymorphic (i,u) =
  let env, evd, ctx, ty, gref = depcase polymorphic i in
  let indid = Nametab.basename_of_global (IndRef i) in
  let id = add_prefix "DependentElimination_" indid in
  let evdref = ref evd in
  let cl = dependent_elimination_class evdref in
  let caseterm = e_new_global evdref gref in
  let casety = Retyping.get_type_of env !evdref caseterm in
  let args = extended_rel_vect 0 ctx in
    Equations_common.declare_instance id polymorphic !evdref ctx cl [ty; prod_appvect sigma casety args;
				mkApp (caseterm, args)]

let () =
  let fn env sigma ~polymorphic c = ignore (derive_dep_elimination env sigma ~polymorphic c) in
  Derive.(register_derive
            { derive_name = "DependentElimination";
              derive_fn = make_derive_ind fn })

let pattern_call ?(pattern_term=true) c gl =
  let env = pf_env gl in
  let sigma = project gl in
  let cty = pf_get_type_of gl c in
  let ids = Id.Set.of_list (ids_of_named_context (pf_hyps gl)) in
  let deps =
    match kind sigma c with
    | App (f, args) -> Array.to_list args
    | _ -> []
  in
  let varname c = match kind sigma c with
    | Var id -> id
    | _ -> Namegen.next_ident_away (Id.of_string (Namegen.hdchar env sigma c))
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

let destPolyRef sigma c =
  match kind sigma c with
  | Ind (ind, u) -> IndRef ind, u
  | Const (c, u) -> ConstRef c, u
  | Construct (cstr, u) -> ConstructRef cstr, u
  | _ -> raise (Invalid_argument "destPolyRef")
              
(** Compare up-to variables in v, skipping parameters of inductive constructors. *)
let rec compare_upto_variables sigma t v =
  if (isVar sigma v || isRel sigma v) then true
  else
    match kind sigma t, kind sigma v with
    | App (cnstr, args), App (cnstr', args') when eq_constr_nounivs sigma cnstr cnstr' &&
                                                  isConstruct sigma cnstr ->
       let cnstr, _u = destConstruct sigma cnstr in
       let real = constructor_nrealargs cnstr in
       if real <= Array.length args && real <= Array.length args' then
         let args = CArray.sub args (Array.length args - real) real in
         let args' = CArray.sub args' (Array.length args' - real) real in
         CArray.for_all2 (compare_upto_variables sigma) args args'
       else
         compare_constr sigma (compare_upto_variables sigma) t v
    | _, _ -> compare_constr sigma (compare_upto_variables sigma) t v

let specialize_eqs id gl =
  let env = pf_env gl in
  let ty = pf_get_hyp_typ gl id in
  let evars = ref (project gl) in
  let unif env ctx evars c1 c2 =
    Evarconv.e_conv env evars (it_mkLambda_or_subst c1 ctx) (it_mkLambda_or_subst c2 ctx) in
  let rec aux in_eqs ctx acc ty =
    match kind !evars ty with
    | Prod (na, t, b) ->
        (match kind !evars t with
	 | App (eq, [| eqty; x; y |]) when
                (is_global !evars (Lazy.force coq_eq) eq &&
                   (noccur_between !evars 1 (List.length ctx) x ||
                      noccur_between !evars 1 (List.length ctx) y)) ->
            let _, u = destPolyRef !evars eq in
            let c, o = if noccur_between !evars 1 (List.length ctx) x then x, y
                       else y, x in
            let eqr = constr_of_global_univ !evars (Lazy.force coq_eq_refl, u) in
	    let p = mkApp (eqr, [| eqty; c |]) in
            if compare_upto_variables !evars c o &&
                 unif env ctx evars o c then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	 | App (heq, [| eqty; x; eqty'; y |]) when
                is_global !evars (Lazy.force coq_heq) heq &&
                 (noccur_between !evars 1 (List.length ctx) x ||
                    noccur_between !evars 1 (List.length ctx) y) ->
            let _, u = destPolyRef !evars heq in
	    let eqt, c, o =
              if noccur_between !evars 1 (List.length ctx) x then eqty, x, y
              else eqty', y, x in
            let eqr = constr_of_global_univ !evars (Lazy.force coq_heq_refl, u) in
	    let p = mkApp (eqr, [| eqt; c |]) in
            if compare_upto_variables !evars c o && unif env ctx evars eqty eqty' &&
                 unif env ctx evars o c then
		aux true ctx (mkApp (acc, [| p |])) (subst1 p b)
	      else acc, in_eqs, ctx, ty
	| _ ->
	    if in_eqs then acc, in_eqs, ctx, ty
	    else
	      let e = e_new_evar env evars (it_mkLambda_or_subst t ctx) in
		aux false (make_def na (Some e) t :: ctx) (mkApp (lift 1 acc, [| mkRel 1 |])) b)
    | t -> acc, in_eqs, ctx, ty
  in
  let acc, worked, ctx, ty = aux false [] (mkVar id) ty in
  let ctx' = nf_rel_context_evar !evars ctx in
  let ctx'' = List.map (fun decl ->
    let (n,b,t) = to_tuple decl in
    match b with
    | Some k when isEvar !evars k -> make_assum n t
    | b -> decl) ctx'
  in
  let ty' = it_mkProd_or_LetIn ty ctx'' in
  let acc' = it_mkLambda_or_LetIn acc ctx'' in
  (* let ty' = Tacred.whd_simpl env !evars ty' *)
  (* and acc' = Tacred.whd_simpl env !evars acc' in *)
  let acc' = Evarutil.nf_evar !evars acc' in
  let ty' = Evarutil.nf_evar !evars ty' in
    if worked then
      tclTHENFIRST (to82 (Tactics.assert_before_replacing id ty'))
	(to82 (exact_no_check acc')) gl
    else tclFAIL 0 (str "Nothing to do in hypothesis " ++ pr_id id) gl

let specialize_eqs id gl =
  if
    (try ignore(to82 (clear [id]) gl); false
     with e when CErrors.noncritical e -> true)
  then
    tclFAIL 0 (str "Specialization not allowed on dependent hypotheses") gl
  else specialize_eqs id gl

(* Produce a list of default patterns to eliminate an inductive value in [ind]. *)
let default_patterns env sigma ?(avoid = ref Id.Set.empty) ind : (Syntax.user_pat Loc.located) list =
  let nparams = Inductiveops.inductive_nparams ind in
  let mib, oib = Inductive.lookup_mind_specif env ind in
  let make_pattern (i : int) : Syntax.user_pat Loc.located =
    let construct = Names.ith_constructor_of_inductive ind (succ i) in
    let args =
      let arity = oib.mind_nf_lc.(i) in
      let params, arity = EConstr.decompose_prod_n_assum sigma nparams (of_constr arity) in
      let ctx, _ = EConstr.decompose_prod_assum sigma arity in
      (* Make an identifier for each argument of the constructor. *)
      List.rev_map (fun decl ->
        let id =
          match Context.Rel.Declaration.get_name decl with
          | Names.Name id -> Namegen.next_ident_away id !avoid
          | Names.Anonymous ->
              let ty = Context.Rel.Declaration.get_type decl in
              let hd = Namegen.hdchar env sigma ty in
                Namegen.next_ident_away (Names.Id.of_string hd) !avoid
        in avoid := Id.Set.add id !avoid;
      None, Syntax.PUVar (id, true)) ctx
    in
      None, Syntax.PUCstr (construct, nparams, args)
  in List.init (Array.length oib.mind_consnames) make_pattern

(* Dependent elimination using Equations. *)
let dependent_elim_tac ?patterns id : unit Proofview.tactic =
  Proofview.Goal.nf_enter begin fun gl ->
    let env = Environ.reset_context (Proofview.Goal.env gl) in
    let hyps = Proofview.Goal.hyps gl in
    let default_loc, id = id in
    (* Keep aside the section variables. *)
    let loc_hyps, sec_hyps = CList.split_when
      (fun decl ->
        let id = Context.Named.Declaration.get_id decl in
        Termops.is_section_variable id) hyps in
    let env = push_named_context sec_hyps env in

    (* Check that [id] exists in the current context. *)
    begin try ignore (Context.Named.lookup id loc_hyps)
    with Not_found ->
      raise (Logic.(RefinerError (NoSuchHyp id)))
    end;

    (* We want to work in a [rel_context], not a [named_context]. *)
    let ctx, subst = Equations_common.rel_of_named_context loc_hyps in
    let _, rev_subst, _ =
      let err () = assert false in
      Equations_common.named_of_rel_context ~keeplets:true err ctx in
    let concl = Proofview.Goal.concl gl in
    let sigma = Proofview.Goal.sigma gl in
    (* We also need to convert the goal for it to be well-typed in
     * the [rel_context]. *)
    let ty = Vars.subst_vars subst concl in
    let patterns : (Syntax.user_pat Loc.located) list =
      match patterns with
      | None ->
          (* Produce directly a user_pat. *)
          let decl = Context.Named.lookup id loc_hyps in
          let ty = Context.Named.Declaration.get_type decl in
          let indf, _ = find_rectype env sigma ty in
          let ((ind,_), _) = dest_ind_family indf in
            default_patterns env sigma ind
      | Some p ->
          (* Interpret each pattern. *)
          let avoid = ref Id.Set.empty in
            List.map (Syntax.interp_pat env ~avoid) p
    in

    (* For each pattern, produce a clause. *)
    let make_clause : (Syntax.user_pat Loc.located) -> Syntax.clause =
      fun (loc, pat) ->
        let lhs =
          List.rev_map (fun decl ->
            let decl_id = Context.Named.Declaration.get_id decl in
            if Names.Id.equal decl_id id then loc, pat
            else None, Syntax.PUVar (decl_id, false)) loc_hyps
        in
        let rhs =
          let prog = Constrexpr.CHole (None, Misctypes.IntroAnonymous, None) in
            Syntax.Program (CAst.make prog, [])
        in
          (Option.default default_loc loc, lhs, rhs)
    in
    let clauses : Syntax.clause list = List.map make_clause patterns in
    if !debug then
    Feedback.msg_info (str "Generated clauses: " ++ fnl() ++ Syntax.pr_clauses env clauses);

    (* Produce dummy data for covering. *)
    (* FIXME Not very clean. *)
    let data = (Names.Id.of_string "dummy", false,
      Constrintern.empty_internalization_env) in

    (* Initial problem. *)
    let prob = Covering.id_subst ctx in
    let args = Context.Rel.to_extended_list mkRel 0 ctx in

    Refine.refine ~typecheck:true begin fun evars ->
      let evd = ref evars in
      (* Produce a splitting tree. *)
      let split : Covering.splitting =
        Covering.covering env evd data clauses [] prob ty
      in

      let helpers, oblevs, c, ty =
        Splitting.term_of_tree Evar_kinds.Expand evd env split
      in
      let c = beta_applist !evd (c, args) in
      let c = Vars.substl (List.rev rev_subst) c in
        (!evd, c)
    end
  end
