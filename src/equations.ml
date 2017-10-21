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

type program_info = {
  program_id : Id.t;
  program_sign : rel_context;
  program_arity : Constr.t;
  program_oarity : Constr.t;
  program_rec : Syntax.rec_type option;
  program_impls : Impargs.manual_explicitation list;
}

type compiled_program_info = {
    program_cst : Constant.t;
    program_cmap : (Id.t -> Constr.t) -> Constr.t -> Constr.t;
    program_split : splitting;
    program_split_info : Splitting.term_info }
                  
let nf_program_info evm p =
  { p with
    program_sign = nf_rel_context_evar evm p.program_sign;
    program_arity = nf_evar evm p.program_arity;
    program_oarity = nf_evar evm p.program_oarity }

type flags = {
  polymorphic : bool;
  with_eqns : bool;
  with_ind : bool }  
  
let define_principles flags fixprots progs =
  let fixctx = 
    let fn fixprot (p, prog) = of_tuple (Name p.program_id, None, fixprot) in
    List.rev (List.map2 fn fixprots progs)
  in
  let principles fixdecls (p, prog) =
    let fixsubst = List.map (fun d -> let na, b, t = to_tuple d in
                                      (out_name na, Option.get b)) fixdecls in
    let i = p.program_id in
    let sign = p.program_sign in
    let oarity = p.program_oarity in
    let arity = p.program_arity in
    let gr = ConstRef prog.program_cst in
    let evd = ref Evd.empty in
    let env = Global.env () in
    let f =
      let (f, uc) = Universes.unsafe_constr_of_global gr in
      evd := Evd.from_env env;
      if flags.polymorphic then
  	evd := Evd.merge_context_set Evd.univ_rigid !evd
	                             (Univ.ContextSet.of_context (Univ.instantiate_univ_context uc));
      f
    in
    if flags.with_eqns || flags.with_ind then
      match p.program_rec with
      | Some (Structural _) ->
	 let cutprob, norecprob = 
	   let (ctx, pats, ctx' as ids) = id_subst sign in
	   (ctx @ fixdecls, pats, ctx'), ids
	 in
	 let split, where_map =
           update_split env evd p.program_rec
                        prog.program_cmap f cutprob fixsubst prog.program_split in
	 build_equations flags.with_ind env !evd i prog.program_split_info sign p.program_rec arity 
			 where_map prog.program_cst f norecprob split
      | None ->
	 let prob = id_subst sign in
	 let split, where_map =
           update_split env evd p.program_rec prog.program_cmap
                        f prob [] prog.program_split in
	 build_equations flags.with_ind env !evd i prog.program_split_info sign p.program_rec arity 
			 where_map prog.program_cst f prob split
      | Some (Logical r) ->
	 let prob = id_subst sign in
         (* let () = msg_debug (str"udpdate split" ++ spc () ++ pr_splitting env split) in *)
	 let unfold_split, where_map =
           update_split env evd p.program_rec prog.program_cmap f prob [(i,f)] prog.program_split
         in
	 (* We first define the unfolding and show the fixpoint equation. *)
	 let unfoldi = add_suffix i "_unfold" in
	 let hook_unfold _ cmap info' ectx =
	   let info =
             { info' with base_id = prog.program_split_info.base_id;
                          helpers_info = prog.program_split_info.helpers_info @ info'.helpers_info } in
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
	     let () = if not flags.polymorphic then evd := (Evd.from_env env) in
	     build_equations flags.with_ind env !evd i info sign None arity
		             where_map funf_cst funfc
                             ~alias:(f, unfold_eq_id, prog.program_split) prob unfold_split
	   in
	   let evd = ref (Evd.from_env (Global.env ())) in
	   let stmt = it_mkProd_or_LetIn 
		        (mkEq (Global.env ()) evd arity (mkApp (f, extended_rel_vect 0 sign))
		              (mkApp (funfc, extended_rel_vect 0 sign))) sign 
	   in
	   let tac =
             Principles_proofs.prove_unfolding_lemma info where_map r prog.program_cst funf_cst
                                                     prog.program_split unfold_split
           in
	   ignore(Obligations.add_definition
                    ~kind:info.decl_kind
		    ~hook:(Lemmas.mk_hook hook_eqs) ~reduce:(fun x -> x)
		    ~implicits:p.program_impls unfold_eq_id stmt ~tactic:(of82 tac)
		    (Evd.evar_universe_context !evd) [||])
	 in
	 define_tree None [] flags.polymorphic p.program_impls (Define false) evd env
		     (unfoldi, sign, oarity) None unfold_split hook_unfold
    else ()
  in
  match progs with
  | [prog] ->
     let fixdecls =
       let fn fixprot (p, prog) =
         let f = fst (Universes.unsafe_constr_of_global (ConstRef prog.program_cst)) in
         of_tuple (Name p.program_id, Some f, fixprot)
       in
       List.map2 fn fixprots progs
     in
     principles fixdecls prog
  | l ->
     (** In the mutually recursive case, only the functionals have been defined, 
         we build the block and its projections now *)
     let structargs = Array.map_of_list (fun (p,_) ->
                          (List.length p.program_sign) - 1) l in
     let evd = ref (Evd.from_env (Global.env ())) in
     let decl =
       let blockfn (p, prog) = 
         let na = Name p.program_id in
         let body = Evarutil.e_new_global evd (ConstRef prog.program_cst) in
         let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
         let fullctx = p.program_sign @ fixctx in
         let body = mkApp (body, extended_rel_vect 0 fullctx) in
         let body = it_mkLambda_or_LetIn body p.program_sign in
         na, ty, body
       in
       let blockl = List.map blockfn l in
       let names, tys, bodies = List.split3 blockl in
       Array.of_list names, Array.of_list tys, Array.of_list bodies
     in
     let declare_fn i (p,prog) =
       let fix = mkFix ((structargs, i), decl) in
       let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
       let kn =
         declare_constant p.program_id fix (Some ty) flags.polymorphic
                          !evd (IsDefinition Fixpoint)
       in
       let prog' = { prog with program_cst = kn } in
       (p, prog')
     in
     let l' = List.mapi declare_fn l in
     let fixdecls =
       let fn fixprot (p, prog) =
         let f = fst (Universes.unsafe_constr_of_global (ConstRef prog.program_cst)) in
         of_tuple (Name p.program_id, Some f, fixprot)
       in
       List.rev (List.map2 fn fixprots l')
     in
     List.iter (principles fixdecls) l'
  
let define_by_eqs opts eqs nt =
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
      not (try_bool_opt (OComp true)), irec,
      try_bool_opt (OEquations false), try_bool_opt (OInd false)
  in
  (* TODO Uncomment this line. For now, it makes some tests fail. *)
  let with_comp = with_comp && not !Equations_common.ocaml_splitting in
  let env = Global.env () in
  let poly = Flags.is_universe_polymorphism () in
  let flags = { polymorphic = poly; with_eqns; with_ind } in
  let evd = ref (Evd.from_env env) in
  let recids = List.map (fun (((loc,i),_,_),_) -> i, None) eqs in
  let interp_arities (((loc,i),l,t),eqs) =
    let ienv, ((env', sign), impls) = interp_context_evars env evd l in
    let arity = interp_type_evars env' evd t in
    let sign = nf_rel_context_evar ( !evd) sign in
    let oarity = nf_evar ( !evd) arity in
    let is_recursive = is_recursive i eqs in
    let body = it_mkLambda_or_LetIn oarity sign in
    let _ = Pretyping.check_evars env Evd.empty !evd body in
    let comp, compapp, oarity =
      if with_comp then
        let _ = Pretyping.check_evars env Evd.empty !evd body in
	let compid = add_suffix i "_comp" in
	let ce = make_definition ~poly evd body in
	let comp =
	  Declare.declare_constant compid (DefinitionEntry ce, IsDefinition Definition)
	in (*Typeclasses.add_constant_class c;*)
        let oarity = nf_evar !evd arity in
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
      else None, arity, arity
    in
    match is_recursive with
    | None ->
       { program_id = i;
         program_sign = sign;
         program_oarity = oarity;
         program_arity = oarity;
         program_rec = None;
         program_impls = impls }
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
	 else compapp, Some (Structural recids)
       in
       { program_id = i;
         program_sign = sign;
         program_oarity = oarity;
         program_arity = compapp;
         program_rec = is_recursive;
         program_impls = impls }
  in
  let arities = List.map interp_arities eqs in
  let eqs = List.map snd eqs in
  let env = Global.env () in (* To find the comp constant *)

  let tys = List.map (fun p ->
            let oty = it_mkProd_or_LetIn p.program_oarity p.program_sign in
            let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
            (p.program_id, (oty, ty), p.program_impls)) arities
  in
  let names, otys, impls = List.split3 tys in
  let data =
    Constrintern.compute_internalization_env
    env Constrintern.Recursive names (List.map fst otys) impls
  in
  let fixprots =
    List.map (fun (oty, ty) ->
    mkLetIn (Anonymous,
             Universes.constr_of_global (Lazy.force coq_fix_proto),
	     Universes.constr_of_global (Lazy.force coq_unit), ty)) otys in
  let fixdecls =
    List.map2 (fun i fixprot -> of_tuple (Name i, None, fixprot)) names fixprots in
  let fixdecls = List.rev fixdecls in
  let implsinfo = List.map (fun (_, (oty, ty), impls) ->
                  Impargs.compute_implicits_with_manual env oty false impls) tys in
  let equations = 
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation data) nt;
      List.map3 (fun implsinfo ar eqs ->
        map (interp_eqn ar.program_id ar.program_rec env implsinfo) eqs)
        implsinfo arities eqs)
      ()
  in
  let fixdecls = nf_rel_context_evar !evd fixdecls in
  let covering env p eqs =
    let sign = nf_rel_context_evar !evd p.program_sign in
    let prob =
      if is_structural p.program_rec then
        id_subst (sign @ fixdecls)
      else id_subst sign
    in
    let _oarity = nf_evar !evd p.program_oarity in
    let arity = nf_evar !evd p.program_arity in
    covering env evd (p.program_id,with_comp,data) eqs [] prob arity
  in
  let coverings = List.map2 (covering env) arities equations in
  let status = Define false in
  let (ids, csts) = full_transparent_state in
  let fix_proto_ref = destConstRef (Lazy.force coq_fix_proto) in
  let _kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
  let baseid =
    let p = List.hd arities in string_of_id p.program_id in
  (** Necessary for the definition of [i] *)
  let () =
    let trs = (ids, Cpred.remove fix_proto_ref csts) in
    Hints.create_hint_db false baseid trs true
  in
  let progs = Array.make (List.length eqs) None in
  let hook i p split cmap info ectx =
    let () = inline_helpers info in
    let () = declare_wf_obligations info in
    let f_cst = match info.term_id with ConstRef c -> c | _ -> assert false in
    let () = evd := Evd.from_ctx ectx in
    let split = map_evars_in_split !evd cmap split in
    let p = nf_program_info !evd p in
    let compiled_info = { program_cst = f_cst;
                          program_cmap = cmap;
                          program_split = split;
                          program_split_info = info } in
    progs.(i) <- Some (p, compiled_info);
    if Array.for_all (fun x -> not (Option.is_empty x)) progs then
      (let fixprots = List.map (nf_evar !evd) fixprots in
       let progs = Array.map_to_list (fun x -> Option.get x) progs in
       define_principles flags fixprots progs)
  in
  let idx = ref 0 in
  let define_tree p split =
    let comp = match p.program_rec with
      Some (Logical l) -> Some l
    | _ -> None
    in
    define_tree p.program_rec fixdecls poly p.program_impls status evd env
                (p.program_id, p.program_sign, p.program_oarity)
		comp split (hook !idx p);
    incr idx
  in CList.iter2 define_tree arities coverings

let with_rollback f x =
  States.with_state_protection_on_exception f x

let equations opts eqs nt =
  List.iter (fun (((loc, i), l, t),eqs) -> Dumpglob.dump_definition (loc, i) false "def") eqs;
  define_by_eqs opts eqs nt

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
