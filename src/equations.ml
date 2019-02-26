(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Util
open Names
open Nameops
open Constr
open Termops
open Environ
open Globnames
open Libnames
open Vars
open Tactics
open Tacticals
open Tacmach
open Evarutil
open Equations_common

open Syntax
open Covering
open Splitting
open Principles
open EConstr

open Extraction_plugin
                
let inline_helpers i = 
  let l = List.map (fun (cst, _) -> Nametab.shortest_qualid_of_global Id.Set.empty (ConstRef cst)) i.helpers_info in
  Table.extraction_inline true l

let declare_wf_obligations info =
  let make_resolve gr =
    (Hints.empty_hint_info, is_polymorphic info, true,
     Hints.PathAny, Hints.IsGlobRef gr)
  in let constrs =
    List.fold_right (fun obl acc ->
    make_resolve (ConstRef obl) :: acc) info.comp_obls [] in
  Hints.add_hints ~local:false [Principles_proofs.wf_obligations_base info] (Hints.HintsResolveEntry constrs)

let define_unfolding_eq env evd flags p unfp prog prog' ei hook =
  let info' = prog'.program_split_info in
  let info =
    { info' with base_id = prog.program_split_info.base_id;
                 helpers_info = prog.program_split_info.helpers_info @ info'.helpers_info;
                 user_obls = Id.Set.union prog.program_split_info.user_obls info'.user_obls } in
  let () = inline_helpers info in
  let funf_cst = match info'.term_id with ConstRef c -> c | _ -> assert false in
  let () = if flags.polymorphic then evd := Evd.from_ctx info'.term_ustate in
  let funfc = e_new_global evd info'.term_id in
  let unfold_split = unfp.program_splitting in
  (* let cmap' x = of_constr (cmap (EConstr.to_constr ~abort_on_undefined_evars:false !evd x)) in
   * let unfold_split = map_split cmap' unfold_split in *)
  let unfold_eq_id = add_suffix (program_id unfp) "_eq" in
  let hook_eqs _ _obls subst grunfold =
    Global.set_strategy (ConstKey funf_cst) Conv_oracle.transparent;
    let () = (* Declare the subproofs of unfolding for where as rewrite rules *)
      let decl _ (_, id, _) =
        let gr =
          try Nametab.locate_constant (qualid_of_ident id)
          with Not_found -> anomaly Pp.(str "Could not find where clause unfolding lemma "
                                        ++ Names.Id.print id)
        in
        let grc = UnivGen.fresh_global_instance (Global.env()) (ConstRef gr) in
        Autorewrite.add_rew_rules (info.base_id ^ "_where") [CAst.make (grc, true, None)];
        Autorewrite.add_rew_rules (info.base_id ^ "_where_rev") [CAst.make (grc, false, None)]
      in
      PathMap.iter decl ei.Principles_proofs.equations_where_map
    in
    let env = Global.env () in
    let () = if not flags.polymorphic then evd := (Evd.from_env env) in
    let prog' = { program_cst = funf_cst;
                  program_split_info = info }
    in
    let unfp =
      { unfp with program_info =
                    { unfp.program_info with program_id = program_id p } }
    in
    let eqninfo =
      Principles_proofs.{ equations_id = program_id p;
                          equations_where_map = ei.equations_where_map;
                          equations_f = funfc;
                          equations_prob = ei.equations_prob }
    in hook (p, Some unfp, prog', eqninfo) unfold_eq_id
  in
  let () = if not flags.polymorphic then (evd := Evd.from_env (Global.env ())) in
  let sign = program_sign unfp in
  let arity = program_arity unfp in
  let stmt = it_mkProd_or_LetIn
      (mkEq (Global.env ()) evd arity (mkApp (p.program_term, extended_rel_vect 0 sign))
         (mkApp (funfc, extended_rel_vect 0 sign))) sign
  in
  let evd, stmt = Typing.solve_evars (Global.env ()) !evd stmt in
  let tac =
    Principles_proofs.(prove_unfolding_lemma info ei.equations_where_map prog.program_cst funf_cst
      p.program_splitting unfold_split)
  in
  ignore(Obligations.add_definition
           ~kind:info.decl_kind
           ~hook:(Lemmas.mk_hook hook_eqs) ~reduce:(fun x -> x)
           ~implicits:(program_impls p) unfold_eq_id (to_constr evd stmt)
           ~tactic:(of82 tac)
           (Evd.evar_universe_context evd) [||])

let define_principles flags rec_type fixprots progs =
  let env = Global.env () in
  let evd = ref (Evd.from_env env) in
  let () =
    if flags.polymorphic then
      let ustate = (snd (List.hd progs)).program_split_info.term_ustate in
      let () = evd := Evd.merge_universe_context !evd ustate in ()
    else ()
  in
  let progs' = Principles.unfold_programs env evd flags rec_type progs in
  match progs' with
  | [p, Some (unfp, cpi'), cpi, eqi] ->
    let hook (p, unfp, cpi, eqi) unfold_eq_id =
      Principles.build_equations flags.with_ind env !evd
        ~alias:(make_alias (p.program_term, unfold_eq_id, p.program_splitting))
        rec_type [p, unfp, cpi, eqi]
    in
    define_unfolding_eq env evd flags p unfp cpi cpi' eqi hook
  | splits ->
    let splits = List.map (fun (p, unfp, cpi, eqi) ->
     let unfp' = match unfp with
       | Some (unfp, unfpi) -> Some unfp
       | None -> None
     in (p, unfp', cpi, eqi)) splits
    in
    build_equations flags.with_ind env !evd rec_type splits

let define_by_eqs ~poly ~program_mode ~open_proof opts eqs nt =
  let with_eqns, with_ind =
    let try_bool_opt opt =
      if List.mem opt opts then false
      else true 
    in
    let with_eqns = try_bool_opt (OEquations false) in
    if with_eqns then with_eqns, try_bool_opt (OInd false)
    else false, false
  in
  let env = Global.env () in
  let flags = { polymorphic = poly; with_eqns; with_ind; open_proof } in
  let evd = ref (Evd.from_env env) in
  let programs = List.map (fun (((loc,i),rec_annot,l,t,by),clauses as ieqs) ->
      let is_rec = is_recursive i (eqs, nt) in
      interp_arity env evd ~poly ~is_rec ~with_evars:open_proof nt ieqs) eqs in
  let rec_type = compute_rec_type [] programs in
  let () = print_recinfo programs in
  let env = Global.env () in (* To find the comp constant *)
  let data, fixdecls, fixprots = compute_fixdecls_data env evd programs in
  let fixdecls = nf_rel_context_evar !evd fixdecls in
  let intenv = { rec_type; flags; fixdecls; intenv = data; notations = nt; program_mode } in
  let programs = coverings env evd intenv programs (List.map snd eqs) in
  let env = Global.env () in (* coverings has the side effect of defining comp_proj constants for now *)
  let fix_proto_ref = destConstRef (Lazy.force coq_fix_proto) in
  let _kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
  let baseid =
    let p = List.hd programs in Id.to_string p.program_info.program_id in
  (* Necessary for the definition of [i] *)
  let () =
    let trs = { TransparentState.full with TransparentState.tr_cst = Cpred.complement (Cpred.singleton fix_proto_ref) } in
    Hints.create_hint_db false baseid trs true
  in
  let progs = Array.make (List.length eqs) None in
  let hook i p info =
    let () = inline_helpers info in
    let () = declare_wf_obligations info in
    let f_cst = match info.term_id with ConstRef c -> c | _ -> assert false in
    let () = evd := Evd.from_ctx info.term_ustate in
    let compiled_info = { program_cst = f_cst;
                          program_split_info = info } in
    progs.(i) <- Some (p, compiled_info);
    if CArray.for_all (fun x -> not (Option.is_empty x)) progs then
      (let fixprots = List.map (nf_evar !evd) fixprots in
       let progs = Array.map_to_list (fun x -> Option.get x) progs in
       let rec_info = compute_rec_type [] (List.map (fun (x, y) -> x.program_info) progs) in
       List.iter (Metasyntax.add_notation_interpretation (Global.env ())) nt;
       if flags.with_eqns || flags.with_ind then
         define_principles flags rec_info fixprots progs)
  in
  define_programs env evd rec_type fixdecls flags programs hook

let equations ~poly ~program_mode ~open_proof opts eqs nt =
  List.iter (fun (((loc, i), nested, l, t, by),eqs) -> Dumpglob.dump_definition CAst.(make ~loc i) false "def") eqs;
  define_by_eqs ~poly ~program_mode ~open_proof opts eqs nt

let solve_equations_goal destruct_tac tac gl =
  let concl = pf_concl gl in
  let intros, move, concl =
    let rec intros goal move = 
      match Constr.kind goal with
      | Prod (Name id, _, t) -> 
         let id = fresh_id_in_env Id.Set.empty id (pf_env gl) in
         let tac, move, goal = intros (subst1 (Constr.mkVar id) t) (Some id) in
         tclTHEN (to82 intro) tac, move, goal
      | LetIn (Name id, c, _, t) -> 
         if String.equal (Id.to_string id) "target" then 
           tclIDTAC, move, goal
         else 
           let id = fresh_id_in_env Id.Set.empty id (pf_env gl) in
           let tac, move, goal = intros (subst1 c t) (Some id) in
           tclTHEN (to82 intro) tac, move, goal
      | _ -> tclIDTAC, move, goal
    in 
    intros (to_constr (project gl) concl) None
  in
  let move_tac = 
    match move with
    | None -> fun _ -> tclIDTAC
    | Some id' -> fun id -> to82 (move_hyp id (Logic.MoveBefore id'))
  in
  let targetn, branchesn, targ, brs, b =
    match kind (project gl) (of_constr concl) with
    | LetIn (Name target, targ, _, b) ->
        (match kind (project gl) b with
	| LetIn (Name branches, brs, _, b) ->
           target, branches, int_of_coq_nat (to_constr (project gl) targ),
           int_of_coq_nat (to_constr (project gl) brs), b
	| _ -> error "Unnexpected goal")
    | _ -> error "Unnexpected goal"
  in
  let branches, b =
    let rec aux n c =
      if n == 0 then [], c
      else match kind (project gl) c with
      | LetIn (Name id, br, brt, b) ->
	  let rest, b = aux (pred n) b in
	    (id, br, brt) :: rest, b
      | _ -> error "Unnexpected goal"
    in aux brs b
  in
  let ids = targetn :: branchesn :: List.map pi1 branches in
  let cleantac = tclTHEN (to82 (intros_using ids)) (to82 (clear ids)) in
  let dotac = tclDO (succ targ) (to82 intro) in
  let letintac (id, br, brt) = 
    tclTHEN (to82 (letin_tac None (Name id) br (Some brt) nowhere))
            (tclTHEN (move_tac id) tac)
  in
  let subtacs =
    tclTHENS destruct_tac (List.map letintac branches)
  in tclTHENLIST [intros; cleantac ; dotac ; subtacs] gl

let dependencies env sigma c ctx =
  let init = global_vars_set env c in
  let deps =
    fold_named_context_reverse 
    (fun variables decl ->
      let n = get_id decl in
      let dvars = global_vars_set_of_decl env sigma decl in
        if Id.Set.mem n variables then Id.Set.union dvars variables
        else variables)
      ~init:init ctx
  in
    (init, Id.Set.diff deps init)
