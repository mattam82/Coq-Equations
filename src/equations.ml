(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
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
open Globnames
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type
open Glob_term
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Entries
open Constrexpr
open Vars
open Tacexpr
open Tactics
open Tacticals
open Tacmach
open Context
open Evd
open Evarutil
open Evar_kinds
open Equations_common
open Depelim
open Printer
open Ppconstr
open Decl_kinds
open Constrintern

open Syntax
open Covering
open Splitting
open Principles

open Extraction_plugin
                
let inline_helpers i = 
  let l = List.map (fun (_, _, id) -> Ident (dummy_loc, id)) i.helpers_info in
  Table.extraction_inline true l

let make_ref dir s = Coqlib.gen_reference "Program" dir s

let fix_proto_ref () = 
  match make_ref ["Program";"Tactics"] "fix_proto" with
  | ConstRef c -> c
  | _ -> assert false

let constr_of_global = Universes.constr_of_global

let is_recursive i eqs =
  let rec occur_eqn (_, _, rhs) =
    match rhs with
    | Program (c,w) -> if occur_var_constr_expr i c then Some false else None
    | Refine (c, eqs) -> 
       if occur_var_constr_expr i c then Some false
       else occur_eqns eqs
    | Rec _ -> Some true
    | _ -> None
  and occur_eqns eqs =
    let occurs = map occur_eqn eqs in
    if for_all Option.is_empty occurs then None
    else if exists (function Some true -> true | _ -> false) occurs then Some true
    else Some false
  in occur_eqns eqs

let declare_wf_obligations info =
  let make_resolve gr =
    (Hints.empty_hint_info, is_polymorphic info, true,
     Hints.PathAny, Hints.IsGlobRef gr)
  in let constrs =
    Id.Set.fold (fun wfobl acc ->
    let gr = Nametab.locate_constant (qualid_of_ident wfobl) in
    make_resolve (ConstRef gr) :: acc) info.comp_obls [] in
  Hints.add_hints false [Principles_proofs.wf_obligations_base info] (Hints.HintsResolveEntry constrs)

let define_by_eqs opts i l t nt eqs =
  let with_comp, with_rec, with_eqns, with_ind =
    let try_bool_opt opt =
      if List.mem opt opts then false
      else true 
    in
    let irec = 
      try 
	List.find_map (function ORec i -> Some i | _ -> None) opts 
      with Not_found -> None
    in
      try_bool_opt (OComp false), irec,
      try_bool_opt (OEquations false), try_bool_opt (OInd false)
  in
  (* TODO Uncomment this line. For now, it makes some tests fail. *)
  let with_comp = with_comp && not !Equations_common.ocaml_splitting in
  let env = Global.env () in
  let poly = Flags.is_universe_polymorphism () in
  let evd = ref (Evd.from_env env) in
  let ienv, ((env', sign), impls) = interp_context_evars env evd l in
  let arity = interp_type_evars env' evd t in
  let sign = nf_rel_context_evar ( !evd) sign in
  let oarity = nf_evar ( !evd) arity in
  let is_recursive = is_recursive i eqs in
  let (sign, oarity, arity, comp, is_recursive) = 
    let body = it_mkLambda_or_LetIn oarity sign in
    let comp, compapp, oarity =
      if with_comp then
        let _ = Pretyping.check_evars env Evd.empty !evd body in
	let compid = add_suffix i "_comp" in
	let ce = make_definition ~poly evd body in
	let comp =
	  Declare.declare_constant compid (DefinitionEntry ce, IsDefinition Definition)
	in (*Typeclasses.add_constant_class c;*)
        let oarity = nf_evar !evd oarity in
        let sign = nf_rel_context_evar !evd sign in
	evd := if poly then !evd else Evd.from_env (Global.env ());
	let compc = e_new_global evd (ConstRef comp) in
	let compapp = mkApp (compc, rel_vect 0 (length sign)) in
        hintdb_set_transparency comp false "Below";
        hintdb_set_transparency comp false "program";
        hintdb_set_transparency comp false "subterm_relation";
        Impargs.declare_manual_implicits true (ConstRef comp) [impls];
        Table.extraction_inline true [Ident (dummy_loc, compid)];
        Some (compid, comp), compapp, oarity
      else
        (* let compapp = mkApp (body, rel_vect 0 (length sign)) in *)
        None, oarity, oarity
    in
    match is_recursive with
    | None -> (sign, oarity, oarity, None, None)
    | Some b ->
       let projid = add_suffix i "_comp_proj" in
       let compproj = 
	 let body =
           it_mkLambda_or_LetIn (mkRel 1)
				(of_tuple (Name (id_of_string "comp"), None, compapp) :: sign)
	 in
	 let _ty = e_type_of (Global.env ()) evd body in
	 let nf, _ = Evarutil.e_nf_evars_and_universes evd in
	 let ce =
           Declare.definition_entry ~fix_exn:(Stm.get_fix_exn ())
				    ~poly ~univs:(snd (Evd.universe_context !evd))
				    (nf body)
	 in
	 Declare.declare_constant projid
				  (DefinitionEntry ce, IsDefinition Definition)
       in
       let impl =
         if with_comp then
           [ExplByPos (succ (List.length sign), None), (true, false, true)]
         else [] in
       Impargs.declare_manual_implicits true (ConstRef compproj) [impls @ impl];
       Table.extraction_inline true [Ident (dummy_loc, projid)];
       let compinfo = LogicalProj { comp = Option.map snd comp; comp_app = compapp;
			            comp_proj = compproj; comp_recarg = succ (length sign) } in
       let compapp, is_recursive =
	 if b then compapp, Some (Logical compinfo)
	 else compapp, Some (Structural with_rec)
       in
       (sign, oarity, compapp, Some compinfo, is_recursive)
  in
  let env = Global.env () in (* To find the comp constant *)
  let oty = it_mkProd_or_LetIn oarity sign in
  let ty = it_mkProd_or_LetIn arity sign in
  let data = Constrintern.compute_internalization_env
    env Constrintern.Recursive [i] [oty] [impls] 
  in
  let fixprot = mkLetIn (Anonymous,
                         Universes.constr_of_global (Lazy.force coq_fix_proto),
			 Universes.constr_of_global (Lazy.force coq_unit), ty) in
  let fixdecls = [of_tuple (Name i, None, fixprot)] in
  let implsinfo = Impargs.compute_implicits_with_manual env oty false impls in
  let equations = 
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation data) nt;
      map (interp_eqn i is_recursive env implsinfo) eqs)
      ()
  in
  let sign = nf_rel_context_evar !evd sign in
  let oarity = nf_evar !evd oarity in
  let arity = nf_evar !evd arity in
  let fixdecls = nf_rel_context_evar !evd fixdecls in
  (*   let ce = check_evars fixenv Evd.empty !evd in *)
  (*   List.iter (function (_, _, Program rhs) -> ce rhs | _ -> ()) equations; *)
  let prob = 
    if is_structural is_recursive then
      id_subst (sign @ fixdecls)
    else id_subst sign
  in
  let split = covering env evd (i,with_comp,data) equations [] prob arity in
  let status = Define false in
  let (ids, csts) = full_transparent_state in
  let fix_proto_ref = destConstRef (Lazy.force coq_fix_proto) in
  (** Necessary for the definition of [i] *)
  let () =
    let trs = (ids, Cpred.remove fix_proto_ref csts) in
    Hints.create_hint_db false (Id.to_string i) trs true
  in
  let hook split cmap info ectx =
    let () = inline_helpers info in
    let () = declare_wf_obligations info in
    let f_cst = match info.term_id with ConstRef c -> c | _ -> assert false in
    let env = Global.env () in
    let () = evd := Evd.from_ctx ectx in
    let split = map_evars_in_split !evd cmap split in
    let sign = nf_rel_context_evar !evd sign in
    let oarity = nf_evar !evd oarity in
    let arity = nf_evar !evd arity in
    let fixprot = nf_evar !evd fixprot in
    let f =
      let (f, uc) = Universes.unsafe_constr_of_global info.term_id in
        evd := Evd.from_env env;
	if poly then
  	  evd := Evd.merge_context_set Evd.univ_rigid !evd
	       (Univ.ContextSet.of_context (Univ.instantiate_univ_context uc));
	f
    in
      if with_eqns || with_ind then
	match is_recursive with
	| Some (Structural _) ->
	    let cutprob, norecprob = 
	      let (ctx, pats, ctx' as ids) = id_subst sign in
	      let fixdecls' = [of_tuple (Name i, Some f, fixprot)] in
		(ctx @ fixdecls', pats, ctx'), ids
	    in
	    let split, where_map = update_split env evd is_recursive
                                     cmap f cutprob i split in
	      build_equations with_ind env !evd i info sign is_recursive arity 
			      where_map f_cst f norecprob split
	| None ->
	   let prob = id_subst sign in
	   let split, where_map = update_split env evd is_recursive cmap
                                    f prob i split in
	   build_equations with_ind env !evd i info sign is_recursive arity 
			   where_map f_cst f prob split
	| Some (Logical r) ->
	   let prob = id_subst sign in
    (* let () = msg_debug (str"udpdate split" ++ spc () ++ pr_splitting env split) in *)
	   let unfold_split, where_map =
             update_split env evd is_recursive cmap f prob i split
           in
	   (* We first define the unfolding and show the fixpoint equation. *)
	   let unfoldi = add_suffix i "_unfold" in
	   let hook_unfold _ cmap info' ectx =
	     let info =
               { info' with base_id = info.base_id;
                            helpers_info = info.helpers_info @ info'.helpers_info } in
	     let () = inline_helpers info in
	     let funf_cst = match info'.term_id with ConstRef c -> c | _ -> assert false in
	     let funfc = e_new_global evd info'.term_id in
	     let unfold_split = map_evars_in_split !evd cmap unfold_split in
	     let unfold_eq_id = add_suffix unfoldi "_eq" in
	     let hook_eqs subst grunfold _ =
		Global.set_strategy (ConstKey funf_cst) Conv_oracle.transparent;
                let () = (* Declare the subproofs of unfolding for where as rewrite rules *)
                  let decl _ (_, id, _) =
                    let gr = Nametab.locate_constant (qualid_of_ident id) in
                    let grc = Universes.fresh_global_instance (Global.env()) (ConstRef gr) in
                    Autorewrite.add_rew_rules (info.base_id ^ "_where") [dummy_loc, grc, true, None];
                    Autorewrite.add_rew_rules (info.base_id ^ "_where_rev") [dummy_loc, grc, false, None]
                  in
                  Evar.Map.iter decl where_map
                in
		let env = Global.env () in
		let () = if not poly then evd := (Evd.from_env env) in
		  build_equations with_ind env !evd i info sign None arity
		                  where_map funf_cst funfc
                                  ~alias:(f, unfold_eq_id, split) prob unfold_split
	      in
	      let evd = ref (Evd.from_env (Global.env ())) in
	      let stmt = it_mkProd_or_LetIn 
		(mkEq (Global.env ()) evd arity (mkApp (f, extended_rel_vect 0 sign))
		    (mkApp (funfc, extended_rel_vect 0 sign))) sign 
	      in
	      let tac =
                Principles_proofs.prove_unfolding_lemma info where_map r f_cst funf_cst
                                      split unfold_split
              in
	        ignore(Obligations.add_definition ~kind:info.decl_kind
			 ~hook:(Lemmas.mk_hook hook_eqs) ~reduce:(fun x -> x)
			 ~implicits:impls unfold_eq_id stmt ~tactic:(of82 tac)
			 (Evd.evar_universe_context !evd) [||])
	    in
	      define_tree None poly impls status evd env
			  (unfoldi, sign, oarity) None unfold_split hook_unfold
      else ()
  in define_tree is_recursive poly impls status evd env (i, sign, oarity)
		 comp split hook

let with_rollback f x =
  States.with_state_protection_on_exception f x

let equations opts (loc, i) l t nt eqs =
  Dumpglob.dump_definition (loc, i) false "def";
  define_by_eqs opts i l t nt eqs

let solve_equations_goal destruct_tac tac gl =
  let concl = pf_concl gl in
  let intros, move, concl =
    let rec intros goal move = 
      match kind_of_term goal with
      | Prod (Name id, _, t) -> 
         let id = fresh_id_in_env [] id (pf_env gl) in
         let tac, move, goal = intros (subst1 (mkVar id) t) (Some id) in
         tclTHEN (to82 intro) tac, move, goal
      | LetIn (Name id, c, _, t) -> 
         if String.equal (Id.to_string id) "target" then 
           tclIDTAC, move, goal
         else 
           let id = fresh_id_in_env [] id (pf_env gl) in
           let tac, move, goal = intros (subst1 c t) (Some id) in
           tclTHEN (to82 intro) tac, move, goal
      | _ -> tclIDTAC, move, goal
    in 
    intros concl None
  in
  let move_tac = 
    match move with
    | None -> fun _ -> tclIDTAC
    | Some id' -> fun id -> to82 (move_hyp id (Misctypes.MoveBefore id'))
  in
  let targetn, branchesn, targ, brs, b =
    match kind_of_term concl with
    | LetIn (Name target, targ, _, b) ->
	(match kind_of_term b with
	| LetIn (Name branches, brs, _, b) ->
	    target, branches, int_of_coq_nat targ, int_of_coq_nat brs, b
	| _ -> error "Unnexpected goal")
    | _ -> error "Unnexpected goal"
  in
  let branches, b =
    let rec aux n c =
      if n == 0 then [], c
      else match kind_of_term c with
      | LetIn (Name id, br, brt, b) ->
	  let rest, b = aux (pred n) b in
	    (id, br, brt) :: rest, b
      | _ -> error "Unnexpected goal"
    in aux brs b
  in
  let ids = targetn :: branchesn :: map pi1 branches in
  let cleantac = tclTHEN (to82 (intros_using ids)) (to82 (clear ids)) in
  let dotac = tclDO (succ targ) (to82 intro) in
  let letintac (id, br, brt) = 
    tclTHEN (to82 (letin_tac None (Name id) br (Some brt) nowhere))
            (tclTHEN (move_tac id) tac)
  in
  let subtacs =
    tclTHENS destruct_tac (map letintac branches)
  in tclTHENLIST [intros; cleantac ; dotac ; subtacs] gl

let dependencies env c ctx =
  let init = global_vars_set env c in
  let deps =
    fold_named_context_reverse 
    (fun variables decl ->
      let n = get_id decl in
      let dvars = global_vars_set_of_decl env decl in
        if Idset.mem n variables then Idset.union dvars variables
        else variables)
      ~init:init ctx
  in
    (init, Idset.diff deps init)
