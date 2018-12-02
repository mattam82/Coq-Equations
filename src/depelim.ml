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
open Constr
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
        else Array.exists (fun x -> not (isVar sigma x) || is_section_variable (destVar sigma x)) args'


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
  let pred = it_mkProd_or_LetIn (evd_comb0 Evarutil.new_Type evd)
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
  Ederive.(register_derive
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

let specialize_eqs ~with_block id gl =
  let env = pf_env gl in
  let ty = pf_get_hyp_typ gl id in
  let evars = ref (project gl) in
  let unif env ctx evars c1 c2 =
    match Evarconv.conv env !evars (it_mkLambda_or_subst c1 ctx) (it_mkLambda_or_subst c2 ctx) with
    | None -> false
    | Some evm -> evars := evm; true
  in
  let rec aux in_block in_eqs ctx subst acc ty =
    match kind !evars ty with
    | LetIn (na, b, t, ty) ->
      if is_global !evars (Lazy.force coq_block) b then
        if not with_block then aux true in_eqs ctx subst acc (subst1 mkProp ty)
        else if in_block then acc, in_eqs, ctx, subst, (subst1 mkProp ty)
        else aux true in_eqs ctx subst acc (subst1 mkProp ty)
      else if not in_block then
        aux in_block in_eqs (make_def na (Some b) t :: ctx) subst acc ty
      else
        aux in_block in_eqs ctx (make_def na (Some b) t :: subst) acc ty
    | Prod (na, t, b) when not in_block ->
      aux false in_eqs (make_def na None t :: ctx) subst (mkApp (lift 1 acc, [| mkRel 1 |])) b
    | Prod (na, t, b) ->
      (match kind !evars t with
       | App (eq, [| eqty; x; y |]) when
           (is_global !evars (Lazy.force logic_eq_type) eq &&
            (noccur_between !evars 1 (List.length subst) x ||
             noccur_between !evars 1 (List.length subst) y)) ->
         let _, u = destPolyRef !evars eq in
         let c, o = if noccur_between !evars 1 (List.length subst) x then x, y
           else y, x in
         let eqr = constr_of_global_univ !evars (Lazy.force logic_eq_refl, u) in
         let p = mkApp (eqr, [| eqty; c |]) in
         if (with_block || compare_upto_variables !evars c o) &&
            unif (push_rel_context ctx env) subst evars o c then
           aux in_block true ctx subst (mkApp (acc, [| p |])) (subst1 p b)
         else acc, in_eqs, ctx, subst, ty
       | _ ->
         if in_eqs then
           (* aux in_block false ctx (make_def na None t :: subst) (mkApp (lift 1 acc, [| mkRel 1 |])) b *)
           acc, in_eqs, ctx, subst, ty
         else
           let e = evd_comb1 (Evarutil.new_evar (push_rel_context ctx env))
               evars (it_mkLambda_or_subst t subst) in
           aux in_block false ctx (make_def na (Some e) t :: subst) (mkApp (lift 1 acc, [| mkRel 1 |])) b)
    | t -> acc, in_eqs, ctx, subst, ty
  in
  let acc, worked, ctx, subst, ty = aux (if with_block then false else true) false [] [] (mkVar id) ty in
  let subst' = nf_rel_context_evar !evars subst in
  let subst'' = List.map (fun decl ->
    let (n,b,t) = to_tuple decl in
    match b with
    | Some k when isEvar !evars k -> make_assum n t
    | b -> decl) subst'
  in
  let ty = it_mkProd_or_LetIn ty subst'' in
  let acc = it_mkLambda_or_LetIn acc subst'' in
  let ty = it_mkProd_or_LetIn ty ctx in
  let acc = it_mkLambda_or_LetIn acc ctx in
  let ty = Evarutil.nf_evar !evars ty in
  let acc = Evarutil.nf_evar !evars acc in
    if worked then
      tclTHENFIRST (to82 (Tactics.assert_before_replacing id ty))
        (to82 (exact_no_check acc)) gl
    else tclFAIL 0 (str "Nothing to do in hypothesis " ++ Id.print id ++
                    Printer.pr_econstr_env env !evars ty
                   ) gl

let specialize_eqs ~with_block id gl =
  if
    (try ignore(to82 (clear [id]) gl); false
     with e when CErrors.noncritical e -> true)
  then
    tclFAIL 0 (str "Specialization not allowed on dependent hypotheses") gl
  else specialize_eqs ~with_block id gl

(* Dependent elimination using Equations. *)
let dependent_elim_tac ?patterns id : unit Proofview.tactic =
  let open Proofview.Notations in
  Proofview.Goal.enter begin fun gl ->
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
    begin try
      let rec lookup k = function
        | decl :: _ when Id.equal id (Context.Named.Declaration.get_id decl) -> k
        | _ :: sign -> lookup (succ k) sign
        | [] -> raise Not_found
      in Proofview.tclUNIT (lookup 1 loc_hyps)
    with Not_found ->
      Tacticals.New.tclZEROMSG (str "No such hypothesis: " ++ Id.print id)
    end >>= fun rel ->

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
    let rhs =
      let prog = Constrexpr.CHole (None, Namegen.IntroAnonymous, None) in
        Syntax.Program (Syntax.ConstrExpr (CAst.make prog), [])
    in
    begin match patterns with
    | None ->
        (* Produce default clauses from the variable to split. *)
        let evd = ref sigma in
        begin match Covering.split_var (env, evd) rel ctx with
        | None | Some (Covering.CannotSplit _) ->
            Tacticals.New.tclZEROMSG (str "Could not eliminate variable " ++ Id.print id)
        | Some (Covering.Splitted (_, newctx, brs)) ->
            let brs = Option.List.flatten (Array.to_list brs) in
            let clauses_lhs = List.map Covering.context_map_to_lhs brs in
            let clauses = List.map (fun lhs -> (Some default_loc, lhs, rhs)) clauses_lhs in
              Proofview.tclUNIT clauses
        end
    | Some p ->
        (* Interpret each pattern to then produce clauses. *)
        let patterns : (Syntax.user_pat_loc) list =
          let avoid = ref (Syntax.ids_of_pats None p) in
          List.map (fun x -> List.hd (Syntax.interp_pat env ~avoid None x)) p
        in
        (* For each pattern, produce a clause. *)
        let make_clause : (Syntax.user_pat_loc) -> Syntax.pre_clause =
          DAst.with_loc_val (fun ?loc pat ->
            let lhs =
              List.rev_map (fun decl ->
                let decl_id = Context.Named.Declaration.get_id decl in
                if Names.Id.equal decl_id id then DAst.make ?loc pat
                else DAst.make (Syntax.PUVar (decl_id, false))) loc_hyps
            in
              (loc, lhs, rhs))
        in Proofview.tclUNIT (List.map make_clause patterns)
    end >>= fun clauses ->
    if !debug then
    Feedback.msg_info (str "Generated clauses: " ++ fnl() ++ Syntax.pr_preclauses env clauses);

    (* Produce dummy data for covering. *)
    (* FIXME Not very clean. *)
    let data =
      Covering.{
        rec_info = None;
        fixdecls = [];
        intenv = Constrintern.empty_internalization_env;
        notations = []
      } in
    let p = Syntax.{program_loc = default_loc;
                    program_id = Names.Id.of_string "dummy";
                    program_impls = [];
                    program_rec = None;
                    program_sign = ctx;
                    program_arity = ty} in

    (* Initial problem. *)
    let prob = Covering.id_subst ctx in
    let args = Context.Rel.to_extended_list mkRel 0 ctx in

    Refine.refine ~typecheck:true begin fun evars ->
      let evd = ref evars in
      (* Produce a splitting tree. *)
      let split : Covering.splitting =
        Covering.covering env evd p data clauses [] prob [] ty
      in

      let helpers, oblevs, c, ty =
        Splitting.term_of_tree Evar_kinds.Expand evd env split
      in
      let c = beta_applist !evd (c, args) in
      let c = Vars.substl (List.rev rev_subst) c in
        (!evd, c)
    end
  end
