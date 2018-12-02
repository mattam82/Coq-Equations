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
open Evar_kinds
open Equations_common
open Decl_kinds

open Syntax
open Covering
open Splitting
open Principles
open EConstr

open Extraction_plugin
                
let inline_helpers i = 
  let l = List.map (fun (_, _, id) -> Libnames.qualid_of_ident id) i.helpers_info in
  Table.extraction_inline true l

let declare_wf_obligations info =
  let make_resolve gr =
    (Hints.empty_hint_info, is_polymorphic info, true,
     Hints.PathAny, Hints.IsGlobRef gr)
  in let constrs =
    Id.Set.fold (fun wfobl acc ->
    let gr = Nametab.locate_constant (qualid_of_ident wfobl) in
    make_resolve (ConstRef gr) :: acc) info.comp_obls [] in
  Hints.add_hints ~local:false [Principles_proofs.wf_obligations_base info] (Hints.HintsResolveEntry constrs)

let nf_program_info evm p =
  { p with
    program_sign = nf_rel_context_evar evm p.program_sign;
    program_arity = nf_evar evm p.program_arity }


let program_fixdecls p fixdecls =
  match p.program_rec with
  | Some (Structural (NestedOn None)) -> (** Actually the definition is not self-recursive *)
     List.filter (fun decl ->
         let na = Context.Rel.Declaration.get_name decl in
         let id = Nameops.Name.get_id na in
         not (Id.equal id p.program_id)) fixdecls
  | _ -> fixdecls

let define_principles flags rec_info fixprots progs =
  let env = Global.env () in
  let evd = ref (Evd.from_env env) in
  let newsplits env fixdecls (p, prog, f) =
    let fixsubst = List.map (fun d -> let na, b, t = to_tuple d in
                                      (Nameops.Name.get_id na, Option.get b)) fixdecls in
    let i = p.program_id in
    let sign = p.program_sign in
    let arity = p.program_arity in
      match rec_info with
      | Some (Guarded _) ->
         let fixdecls = program_fixdecls p fixdecls in
         let cutprob, norecprob =
	   let (ctx, pats, ctx' as ids) = id_subst sign in
	   (ctx @ fixdecls, pats, ctx'), ids
	 in
	 let split, where_map =
           update_split env evd p.program_id rec_info
                        (of_constr f) cutprob fixsubst prog.program_split in
         let eqninfo =
           Principles_proofs.{ equations_id = i;
             equations_where_map = where_map;
             equations_f = f;
             equations_prob = norecprob;
             equations_split = split }
         in
         Some eqninfo
      | None ->
	 let prob = id_subst sign in
	 let split, where_map =
           update_split env evd p.program_id rec_info
                        (of_constr f) prob [] prog.program_split in
         let eqninfo =
           Principles_proofs.{ equations_id = i;
             equations_where_map = where_map;
             equations_f = f;
             equations_prob = prob;
             equations_split = split }
         in
         Some eqninfo

      | Some (Logical r) ->
	 let prob = id_subst sign in
         (* let () = msg_debug (str"udpdate split" ++ spc () ++ pr_splitting env split) in *)
	 let unfold_split, where_map =
           update_split env evd p.program_id rec_info (of_constr f)
                        prob [(i,of_constr f)] prog.program_split
         in
	 (* We first define the unfolding and show the fixpoint equation. *)
         let unfoldi = add_suffix i "_unfold" in
         let hook_unfold _ cmap info' ectx =
           let info =
             { info' with base_id = prog.program_split_info.base_id;
                          helpers_info = prog.program_split_info.helpers_info @ info'.helpers_info;
                          user_obls = Id.Set.union prog.program_split_info.user_obls info'.user_obls } in
	   let () = inline_helpers info in
           let funf_cst = match info'.term_id with ConstRef c -> c | _ -> assert false in
           let () = if flags.polymorphic then evd := Evd.from_ctx ectx in
           let funfc = e_new_global evd info'.term_id in
           let cmap' x = of_constr (cmap (EConstr.to_constr ~abort_on_undefined_evars:false !evd x)) in
           let unfold_split = map_split cmap' unfold_split in
	   let unfold_eq_id = add_suffix unfoldi "_eq" in
           let hook_eqs _ _obls subst grunfold =
	     Global.set_strategy (ConstKey funf_cst) Conv_oracle.transparent;
             let () = (* Declare the subproofs of unfolding for where as rewrite rules *)
               let decl _ (_, id, _) =
                 let gr = Nametab.locate_constant (qualid_of_ident id) in
                 let grc = UnivGen.fresh_global_instance (Global.env()) (ConstRef gr) in
                 Autorewrite.add_rew_rules (info.base_id ^ "_where") [CAst.make (grc, true, None)];
                 Autorewrite.add_rew_rules (info.base_id ^ "_where_rev") [CAst.make (grc, false, None)]
               in
               Evar.Map.iter decl where_map
             in
	     let env = Global.env () in
	     let () = if not flags.polymorphic then evd := (Evd.from_env env) in
             let prog' = { program_cst = funf_cst;
                          program_split = unfold_split;
                          program_split_info = info }
             in
             let p = { program_loc = p.program_loc;
                       program_id = i;
                       program_sign = sign;
                       program_arity = arity;
                       program_rec = None;
                       program_impls = p.program_impls }
             in
             let eqninfo =
               Principles_proofs.{ equations_id = i;
                 equations_where_map = where_map;
                 equations_f = to_constr !evd funfc;
                 equations_prob = prob;
                 equations_split = unfold_split }
             in
             build_equations flags.with_ind env !evd ~alias:(of_constr f, unfold_eq_id, prog.program_split)
               rec_info [p, prog', eqninfo]
	   in
           let () = if not flags.polymorphic then (evd := Evd.from_env (Global.env ())) in
           let stmt = it_mkProd_or_LetIn
                        (mkEq (Global.env ()) evd arity (mkApp (of_constr f, extended_rel_vect 0 sign))
		              (mkApp (funfc, extended_rel_vect 0 sign))) sign 
	   in
           let evd, stmt = Typing.solve_evars (Global.env ()) !evd stmt in
           let tac =
             Principles_proofs.prove_unfolding_lemma info where_map r prog.program_cst funf_cst
                                                     prog.program_split unfold_split
           in
	   ignore(Obligations.add_definition
                    ~kind:info.decl_kind
		    ~univ_hook:(Obligations.mk_univ_hook hook_eqs) ~reduce:(fun x -> x)
                    ~implicits:p.program_impls unfold_eq_id (to_constr evd stmt)
                    ~tactic:(of82 tac)
                    (Evd.evar_universe_context evd) [||])
	 in
	 define_tree None [] flags.polymorphic p.program_impls (Define false) evd env
                     (unfoldi, sign, arity) None unfold_split hook_unfold;
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
  let progs, fixdecls =
    let fn fixprot (p, prog) =
      let f =
        let gr = ConstRef prog.program_cst in
        let inst =
          if flags.polymorphic then
            let ustate = prog.program_split_info.term_ustate in
            let inst = Univ.UContext.instance (UState.context ustate) in
            let () = evd := Evd.merge_universe_context !evd ustate in
            inst
          else Univ.Instance.empty
        in Constr.mkRef (gr, inst)
      in
      (p, prog, f), of_tuple (Name p.program_id, Some (of_constr f), fixprot)
    in
    let progs, fixdecls = List.split (List.map2 fn fixprots progs) in
    progs, List.rev fixdecls
  in
  let newsplits = List.map (fun (p, prog, f as x) -> p, prog, newsplits env fixdecls x) progs in
  principles env newsplits

let is_nested p =
  match p.program_rec with
  | Some (Structural (NestedOn _)) -> true
  | _ -> false

let define_mutual_nested flags progs =
  match progs with
  | [prog] -> progs
  | l ->
     let mutual =
       List.filter (fun (p, prog) -> not (is_nested p)) l
     in
     (** In the mutually recursive case, only the functionals have been defined, 
         we build the block and its projections now *)
     let structargs = Array.map_of_list (fun (p,_) ->
                          match p.program_rec with
                          | Some (Structural (MutualOn (lid,_))) -> lid
                          | _ -> (List.length p.program_sign) - 1) mutual in
     let evd = ref (Evd.from_env (Global.env ())) in
     let mutualapp, nestedbodies =
       let nested = List.length l - List.length mutual in
       let one_nested before p prog afterctx idx =
         let signlen = List.length p.program_sign in
         let fixbody =
           Vars.lift 1 (* lift over itself *)
           (mkApp (mkConst prog.program_cst,
                   rel_vect (signlen + (nested - 1)) (List.length mutual)))
         in
         let after = (nested - 1) - before in
         let fixb = (Array.make 1 idx, 0) in
         let fixna = Array.make 1 (Name p.program_id) in
         let fixty = Array.make 1 (it_mkProd_or_LetIn p.program_arity p.program_sign) in
         (** Apply to itself *)
         let beforeargs = rel_list (signlen + 1) before in
         let fixref = mkRel (signlen + 1) in
         let (afterargs, afterctx) =
           let rec aux (acc, ctx) n afterctx =
             if Int.equal n after then acc, ctx
             else
              match afterctx with
              | ty :: tl ->
                let term = applist (mkRel (signlen + nested), acc) in
                let decl = Context.Rel.Declaration.LocalDef (Name (Id.of_string "H"), term, ty) in
                  aux (List.map (Vars.lift 1) acc @ [mkRel 1], decl :: ctx) (succ n) tl
              | [] -> assert false
           in aux (beforeargs @ [fixref], []) 0 afterctx
         in
         let fixbody = applist (Vars.lift after fixbody, afterargs) in
         (** Apply to its arguments *)
         let fixbody = mkApp (fixbody, extended_rel_vect after p.program_sign) in
	 let fixbody = it_mkLambda_or_LetIn fixbody afterctx in
         let fixbody = it_mkLambda_or_LetIn fixbody p.program_sign in
         it_mkLambda_or_LetIn
         (mkFix (fixb, (fixna, fixty, Array.make 1 fixbody)))
         (List.init (nested - 1) (fun _ -> (Context.Rel.Declaration.LocalAssum (Anonymous, mkProp))))
       in
       let rec fixsubst i k acc l =
         match l with
         | (p', prog') :: rest ->
            (match p'.program_rec with
             | Some (Structural (NestedOn idx)) ->
               (match idx with
	       | Some (idx,_) ->
		 let rest_tys = List.map (fun (p,_) -> it_mkProd_or_LetIn p.program_arity p.program_sign) rest in
                 let term = one_nested k p' prog' rest_tys idx in
                   fixsubst i (succ k) ((true, term) :: acc) rest
               | None -> (* Non immediately recursive nested def *)
                 let term =
                   mkApp (mkConst prog'.program_cst, rel_vect 0 (List.length mutual))
                 in
                   fixsubst i (succ k) ((true, term) :: acc) rest)
             | _ -> fixsubst (pred i) k ((false, mkRel i) :: acc) rest)
         | [] -> List.rev acc
       in
       (** aux1 ... auxn *)
       let nested = fixsubst (List.length mutual) 0 [] l in
       let nested, mutual = List.partition (fun (x, y) -> x) nested in
       let gns = List.fold_right (fun (_, g) acc -> applist (g, acc) :: acc) nested [] in
       let nested = List.fold_left (fun acc g -> applist (g, List.rev acc) :: acc) [] gns in
       let nested = List.rev_map (Reductionops.nf_beta (Global.env ()) !evd) nested in
       List.map snd mutual, nested
     in
     let decl =
       let blockfn (p, prog) = 
         let na = Name p.program_id in
         let evm, body = Evarutil.new_global !evd (ConstRef prog.program_cst) in
         let () = evd := evm in
         let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
         let body = mkApp (body, Array.append (Array.of_list mutualapp) (Array.of_list nestedbodies)) in
         let body = mkApp (Vars.lift (List.length p.program_sign) body,
                           extended_rel_vect 0 p.program_sign) in
         let body = it_mkLambda_or_LetIn body p.program_sign in
         na, ty, body
       in
       let blockl = List.map blockfn mutual in
       let names, tys, bodies = List.split3 blockl in
       Array.of_list names, Array.of_list tys, Array.of_list bodies
     in
     let declare_fix_fns i (p,prog) =
       if not (is_nested p) then
         let fix = mkFix ((structargs, i), decl) in
         let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
         let kn, _ =
           declare_constant p.program_id fix (Some ty) flags.polymorphic
                            !evd (IsDefinition Fixpoint)
         in
         Impargs.declare_manual_implicits true (ConstRef kn) [p.program_impls];
         let prog' = { prog with program_cst = kn } in
         (p, prog')
       else (p,prog)
     in
     let fixes = List.mapi declare_fix_fns l in
     let nested, mutual = List.partition (fun (p,prog) -> is_nested p) fixes in
     let declare_nested (p,prog) body =
       let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
       let args = List.rev_map (fun (p',prog') -> e_new_global evd (ConstRef prog'.program_cst)) mutual in
       let body = Vars.substl args body in
       let kn, _ = declare_constant p.program_id body (Some ty) flags.polymorphic
                                 !evd (IsDefinition Fixpoint) in
       Impargs.declare_manual_implicits true (ConstRef kn) [p.program_impls];
       let prog' = { prog with program_cst = kn } in
       (p, prog')
     in
     let nested = List.map2 declare_nested nested nestedbodies in
     mutual @ nested

let define_by_eqs ~poly opts eqs nt =
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
      | Some lid -> ((li, Some Mutual, l, t, Some (Syntax.Structural lid)), eqns) :: tl
      | _ -> eqs)
    | _ -> assert false
  in
  let env = Global.env () in
  let flags = { polymorphic = poly; with_eqns; with_ind } in
  let evd = ref (Evd.from_env env) in
  let programs = List.map (fun (((loc,i),rec_annot,l,t,by),clauses as ieqs) ->
      let is_rec = is_recursive i eqs in
      interp_arity env evd poly is_rec ieqs) eqs in
  let rec_info = compute_recinfo programs in
  let () = print_recinfo programs in
  let env = Global.env () in (* To find the comp constant *)
  let data, fixdecls, fixprots = compute_fixdecls_data env evd programs in
  let fixdecls = nf_rel_context_evar !evd fixdecls in
  let intenv = { rec_info; fixdecls; intenv = data; notations = nt } in
  let coverings = coverings env evd intenv programs (List.map snd eqs) in
  let programs, coverings = List.split coverings in
  let status = Define false in
  let fix_proto_ref = destConstRef (Lazy.force coq_fix_proto) in
  let _kind = (Decl_kinds.Global, poly, Decl_kinds.Definition) in
  let baseid =
    let p = List.hd programs in Id.to_string p.program_id in
  (** Necessary for the definition of [i] *)
  let () =
    let trs = { TransparentState.full with TransparentState.tr_cst = Cpred.complement (Cpred.singleton fix_proto_ref) } in
    Hints.create_hint_db false baseid trs true
  in
  let progs = Array.make (List.length eqs) None in
  let hook i p split cmap info ectx =
    let () = inline_helpers info in
    let () = declare_wf_obligations info in
    let f_cst = match info.term_id with ConstRef c -> c | _ -> assert false in
    let () = evd := Evd.from_ctx ectx in
    let cmap' x = of_constr (cmap (EConstr.to_constr ~abort_on_undefined_evars:false !evd x)) in
    let split = map_split cmap' split in
    let p = nf_program_info !evd p in
    let compiled_info = { program_cst = f_cst;
                          program_split = split;
                          program_split_info = info } in
    progs.(i) <- Some (p, compiled_info);
    if CArray.for_all (fun x -> not (Option.is_empty x)) progs then
      (let fixprots = List.map (nf_evar !evd) fixprots in
       let progs = Array.map_to_list (fun x -> Option.get x) progs in
       let progs' = define_mutual_nested flags progs in
       if flags.with_eqns || flags.with_ind then
         define_principles flags rec_info fixprots progs')
  in
  let idx = ref 0 in
  let define_tree p split =
    let comp = match p.program_rec with
      Some (WellFounded (_, _, l)) -> Some l
    | _ -> None
    in
    let fixdecls =
      match p.program_rec with
      | Some (Structural (NestedOn None)) | None -> (** Actually the definition is not self-recursive *)
         List.filter (fun decl ->
             let na = Context.Rel.Declaration.get_name decl in
             let id = Nameops.Name.get_id na in
             not (Id.equal id p.program_id)) fixdecls
      | _ -> fixdecls
    in
    define_tree rec_info fixdecls poly p.program_impls status evd env
                (p.program_id, p.program_sign, p.program_arity)
		comp split (hook !idx p);
    incr idx
  in CList.iter2 define_tree programs coverings

let equations ~poly opts eqs nt =
  List.iter (fun (((loc, i), nested, l, t, by),eqs) -> Dumpglob.dump_definition CAst.(make ~loc i) false "def") eqs;
  define_by_eqs ~poly opts eqs nt

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
