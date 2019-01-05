(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
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

let program_fixdecls p fixdecls =
  match p.Syntax.program_rec with
  | Some (Structural NestedNonRec) -> (* Actually the definition is not self-recursive *)
     List.filter (fun decl ->
         let na = Context.Rel.Declaration.get_name decl in
         let id = Nameops.Name.get_id na in
         not (Id.equal id p.program_id)) fixdecls
  | _ -> fixdecls

let define_principles flags rec_info fixprots progs =
  let env = Global.env () in
  let evd = ref (Evd.from_env env) in
  let () =
    if flags.polymorphic then
      let ustate = (snd (List.hd progs)).program_split_info.term_ustate in
      let () = evd := Evd.merge_universe_context !evd ustate in ()
    else ()
  in
  let newsplits env fixdecls (p, prog) =
    let fixsubst = List.map (fun d -> let na, b, t = to_tuple d in
                                      (Nameops.Name.get_id na, (None, Option.get b))) fixdecls in
    let pi = p.program_info in
    let i = pi.program_id in
    let sign = pi.program_sign in
    let arity = pi.program_arity in
      match rec_info with
      | Some (Guarded _) ->
         let fixdecls = program_fixdecls pi fixdecls in
         let cutprob, norecprob =
           let (ctx, pats, ctx' as ids) = Context_map.id_subst sign in
	   (ctx @ fixdecls, pats, ctx'), ids
	 in
	 let split, where_map =
           update_split env evd p rec_info cutprob fixsubst p.program_splitting in
         let eqninfo =
           Principles_proofs.{ equations_id = i;
             equations_where_map = where_map;
             equations_f = p.program_term;
             equations_prob = norecprob;
             equations_split = split }
         in
         Some eqninfo
      | None ->
         let prob = Context_map.id_subst sign in
	 let split, where_map =
           update_split env evd p rec_info prob [] p.program_splitting in
         let eqninfo =
           Principles_proofs.{ equations_id = i;
             equations_where_map = where_map;
             equations_f = p.program_term;
             equations_prob = prob;
             equations_split = split }
         in
         Some eqninfo

      | Some (Logical r) ->
         let prob = Context_map.id_subst sign in
         (* let () = msg_debug (str"udpdate split" ++ spc () ++ pr_splitting env split) in *)
         let recarg = Some (-1) in
         let unfold_split, where_map =
           update_split env evd p rec_info prob [(i, (recarg, p.program_term))] p.program_splitting
         in
	 (* We first define the unfolding and show the fixpoint equation. *)
         let unfoldi = add_suffix i "_unfold" in
         let unfpi =
           { pi with program_id = unfoldi;
                     program_sign = sign;
                     program_arity = arity }
         in
         let unfoldp = make_single_program env evd flags [] unfpi prob unfold_split None in
         let hook_unfold idx unfp info' ectx =
           let info =
             { info' with base_id = prog.program_split_info.base_id;
                          helpers_info = prog.program_split_info.helpers_info @ info'.helpers_info;
                          user_obls = Id.Set.union prog.program_split_info.user_obls info'.user_obls } in
	   let () = inline_helpers info in
           let funf_cst = match info'.term_id with ConstRef c -> c | _ -> assert false in
           let () = if flags.polymorphic then evd := Evd.from_ctx ectx in
           let funfc = e_new_global evd info'.term_id in
           let unfold_split = unfp.program_splitting in
           (* let cmap' x = of_constr (cmap (EConstr.to_constr ~abort_on_undefined_evars:false !evd x)) in
            * let unfold_split = map_split cmap' unfold_split in *)
	   let unfold_eq_id = add_suffix unfoldi "_eq" in
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
               PathMap.iter decl where_map
             in
	     let env = Global.env () in
	     let () = if not flags.polymorphic then evd := (Evd.from_env env) in
             let prog' = { program_cst = funf_cst;
                          program_split_info = info }
             in
             let unfp =
               { unfp with program_info =
                             { unfp.program_info with program_id = i } }
             in
             let eqninfo =
               Principles_proofs.{ equations_id = i;
                 equations_where_map = where_map;
                 equations_f = funfc;
                 equations_prob = prob;
                 equations_split = unfold_split }
             in
             build_equations flags.with_ind env !evd
               ~alias:(make_alias (p.program_term, unfold_eq_id, p.program_splitting))
               rec_info [unfp, prog', eqninfo]
	   in
           let () = if not flags.polymorphic then (evd := Evd.from_env (Global.env ())) in
           let stmt = it_mkProd_or_LetIn
                        (mkEq (Global.env ()) evd arity (mkApp (p.program_term, extended_rel_vect 0 sign))
		              (mkApp (funfc, extended_rel_vect 0 sign))) sign 
	   in
           let evd, stmt = Typing.solve_evars (Global.env ()) !evd stmt in
           let tac =
             Principles_proofs.prove_unfolding_lemma info where_map r prog.program_cst funf_cst
                                                     p.program_splitting unfold_split
           in
	   ignore(Obligations.add_definition
                    ~kind:info.decl_kind
		    ~univ_hook:(Obligations.mk_univ_hook hook_eqs) ~reduce:(fun x -> x)
                    ~implicits:pi.program_impls unfold_eq_id (to_constr evd stmt)
                    ~tactic:(of82 tac)
                    (Evd.evar_universe_context evd) [||])
         in
         define_programs env evd None [] flags ~unfold:true [unfoldp] hook_unfold;
         None
  in
  let principles env newsplits =
    match newsplits with
    | [p, prog, Some eqninfo] ->
       let evm = !evd in
       (match rec_info with
        | Some (Guarded _) ->
           build_equations flags.with_ind env evm rec_info [p, prog, eqninfo]
        | Some (Logical _) -> ()
        | None ->
           build_equations flags.with_ind env evm rec_info [p, prog, eqninfo])
    | [_, _, None] -> ()
    | splits ->
       let splits = List.map (fun (p,prog,s) -> p, prog, Option.get s) splits in
       let evm = !evd in
       build_equations flags.with_ind env evm rec_info splits
  in
  let fixdecls =
    let fn fixprot (p, prog) =
      of_tuple (Name p.program_info.program_id, Some p.program_term, fixprot)
    in
    let fixdecls = List.map2 fn fixprots progs in
    List.rev fixdecls
  in
  let newsplits = List.map (fun (p, prog as x) -> p, prog, newsplits env fixdecls x) progs in
  principles env newsplits

let define_by_eqs ~poly ~open_proof opts eqs nt =
  let with_rec, with_eqns, with_ind =
    let try_bool_opt opt =
      if List.mem opt opts then false
      else true 
    in
    let irec = 
      try 
	List.find_map (function ORec i -> Some i | _ -> None) opts 
      with Not_found -> None
    in
      irec, try_bool_opt (OEquations false), try_bool_opt (OInd false)
  in
  let eqs =
    match eqs with
    | ((li,ra,l,t,by), eqns) :: tl ->
      (match with_rec with
      | Some lid -> ((li, Some Syntax.Mutual, l, t, Some (Syntax.Structural lid)), eqns) :: tl
      | _ -> eqs)
    | _ -> assert false
  in
  let env = Global.env () in
  let flags = { polymorphic = poly; with_eqns; with_ind; open_proof } in
  let evd = ref (Evd.from_env env) in
  let programs = List.map (fun (((loc,i),rec_annot,l,t,by),clauses as ieqs) ->
      let is_rec = is_recursive i eqs in
      interp_arity env evd ~poly ~is_rec ~with_evars:open_proof ieqs) eqs in
  let rec_info = compute_recinfo programs in
  let () = print_recinfo programs in
  let env = Global.env () in (* To find the comp constant *)
  let data, fixdecls, fixprots = compute_fixdecls_data env evd programs in
  let fixdecls = nf_rel_context_evar !evd fixdecls in
  let intenv = { rec_info; flags; fixdecls; intenv = data; notations = nt } in
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
  let hook i p info ectx =
    let () = inline_helpers info in
    let () = declare_wf_obligations info in
    let f_cst = match info.term_id with ConstRef c -> c | _ -> assert false in
    let () = evd := Evd.from_ctx ectx in
    let compiled_info = { program_cst = f_cst;
                          program_split_info = info } in
    progs.(i) <- Some (p, compiled_info);
    if CArray.for_all (fun x -> not (Option.is_empty x)) progs then
      (let fixprots = List.map (nf_evar !evd) fixprots in
       let progs = Array.map_to_list (fun x -> Option.get x) progs in
       let rec_info = compute_recinfo (List.map (fun (x, y) -> x.program_info) progs) in
       if flags.with_eqns || flags.with_ind then
         define_principles flags rec_info fixprots progs)
  in
  define_programs env evd rec_info fixdecls flags programs hook

let equations ~poly ~open_proof opts eqs nt =
  List.iter (fun (((loc, i), nested, l, t, by),eqs) -> Dumpglob.dump_definition CAst.(make ~loc i) false "def") eqs;
  define_by_eqs ~poly ~open_proof opts eqs nt

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
