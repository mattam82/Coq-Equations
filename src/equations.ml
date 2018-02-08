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
open Term
open Termops
open Environ
open Globnames
open List
open Libnames
open Topconstr
open Entries
open Constrexpr
open Vars
open Tactics
open Tacticals
open Tacmach
open Evarutil
open Evar_kinds
open Equations_common
open Decl_kinds
open Constrintern

open Syntax
open Covering
open Splitting
open Principles
open EConstr

open Extraction_plugin
                
let inline_helpers i = 
  let l = List.map (fun (_, _, id) -> Ident (dummy_loc, id)) i.helpers_info in
  Table.extraction_inline true l

let make_ref dir s = Coqlib.find_reference "Program" dir s

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
    let occurs = List.map occur_eqn eqs in
    if for_all Option.is_empty occurs then None
    else if exists (function Some true -> true | _ -> false) occurs then Some true
    else Some false
  in
  let occurs = List.map (fun (_,eqs) -> occur_eqns eqs) eqs in
  if for_all Option.is_empty occurs then None
  else if exists (function Some true -> true | _ -> false) occurs then Some true
  else Some false

let declare_wf_obligations info =
  let make_resolve gr =
    (Hints.empty_hint_info, is_polymorphic info, true,
     Hints.PathAny, Hints.IsGlobRef gr)
  in let constrs =
    Id.Set.fold (fun wfobl acc ->
    let gr = Nametab.locate_constant (qualid_of_ident wfobl) in
    make_resolve (ConstRef gr) :: acc) info.comp_obls [] in
  Hints.add_hints false [Principles_proofs.wf_obligations_base info] (Hints.HintsResolveEntry constrs)

let nf_program_info evm p =
  { p with
    program_sign = nf_rel_context_evar evm p.program_sign;
    program_arity = nf_evar evm p.program_arity;
    program_oarity = nf_evar evm p.program_oarity }

let program_fixdecls p fixdecls =
  match p.program_rec_annot with
  | Some (NestedOn None) -> (** Actually the definition is not self-recursive *)
     List.filter (fun decl ->
         let na = Context.Rel.Declaration.get_name decl in
         let id = Nameops.out_name na in
         not (Id.equal id p.program_id)) fixdecls
  | _ -> fixdecls

let define_principles flags fixprots progs =
  let env = Global.env () in
  let evd = ref (Evd.from_env env) in
  let newsplits env fixdecls (p, prog) =
    let fixsubst = List.map (fun d -> let na, b, t = to_tuple d in
                                      (out_name na, Option.get b)) fixdecls in
    let i = p.program_id in
    let sign = p.program_sign in
    let oarity = p.program_oarity in
    let arity = p.program_arity in
    let gr = ConstRef prog.program_cst in
    let f =
      let (f, uc) = Universes.unsafe_constr_of_global gr in
      if flags.polymorphic then
        evd := Evd.merge_context_set Evd.univ_rigid !evd (Univ.ContextSet.of_context uc);
      f
    in
      match p.program_rec with
      | Some (Structural _) ->
         let fixdecls = program_fixdecls p fixdecls in
         let cutprob, norecprob =
	   let (ctx, pats, ctx' as ids) = id_subst sign in
	   (ctx @ fixdecls, pats, ctx'), ids
	 in
	 let split, where_map =
           update_split env evd p.program_rec
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
           update_split env evd p.program_rec
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
           update_split env evd p.program_rec (of_constr f)
                        prob [(i,of_constr f)] prog.program_split
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
           let unfold_split = map_evars_in_split !evd (fun f x -> of_constr (cmap f x)) unfold_split in
	   let unfold_eq_id = add_suffix unfoldi "_eq" in
	   let hook_eqs subst grunfold _ =
	     Global.set_strategy (ConstKey funf_cst) Conv_oracle.transparent;
             let () = (* Declare the subproofs of unfolding for where as rewrite rules *)
               let decl _ (_, id, _) =
                 try let gr = Nametab.locate_constant (qualid_of_ident id) in
                     let grc = Universes.fresh_global_instance (Global.env()) (ConstRef gr) in
                     Autorewrite.add_rew_rules (info.base_id ^ "_where") [None, (grc, true, None)];
                     Autorewrite.add_rew_rules (info.base_id ^ "_where_rev") [None, (grc, false, None)]
                 with Not_found ->
                   Feedback.msg_warning Pp.(str"Unfolding subproofs not found for " ++ Id.print id)
               in
               Evar.Map.iter decl where_map
             in
	     let env = Global.env () in
	     let () = if not flags.polymorphic then evd := (Evd.from_env env) in
             let prog' = { program_cst = funf_cst;
                          program_cmap = cmap;
                          program_split = unfold_split;
                          program_split_info = info }
             in
             let p = { program_id = i;
                       program_sign = sign;
                       program_arity = arity;
                       program_oarity = arity;
                       program_rec_annot = None;
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
                             [p, prog', eqninfo]
	   in
	   let evd = ref (Evd.from_env (Global.env ())) in
	   let stmt = it_mkProd_or_LetIn 
                        (mkEq (Global.env ()) evd arity (mkApp (of_constr f, extended_rel_vect 0 sign))
		              (mkApp (funfc, extended_rel_vect 0 sign))) sign 
	   in
	   let tac =
             Principles_proofs.prove_unfolding_lemma info where_map r prog.program_cst funf_cst
                                                     prog.program_split unfold_split
           in
	   ignore(Obligations.add_definition
                    ~kind:info.decl_kind
		    ~hook:(Lemmas.mk_hook hook_eqs) ~reduce:(fun x -> x)
                    ~implicits:p.program_impls unfold_eq_id (to_constr !evd stmt)
                    ~tactic:(of82 tac)
		    (Evd.evar_universe_context !evd) [||])
	 in
	 define_tree None [] flags.polymorphic p.program_impls (Define false) evd env
		     (unfoldi, sign, oarity) None unfold_split hook_unfold;
         None
  in
  let principles env newsplits =
    match newsplits with
    | [p, prog, Some eqninfo] ->
       let evm = !evd in
       (match p.program_rec with
        | Some (Structural _) ->
           build_equations flags.with_ind env evm [p, prog, eqninfo]
        | Some (Logical _) -> ()
        | None ->
           build_equations flags.with_ind env evm [p, prog, eqninfo])
    | [_, _, None] -> ()
    | splits ->
       let splits = List.map (fun (p,prog,s) -> p, prog, Option.get s) splits in
       let evm = !evd in
       build_equations flags.with_ind env evm splits
  in
  let fixdecls =
    let fn fixprot (p, prog) =
      let f = fst (Universes.unsafe_constr_of_global (ConstRef prog.program_cst)) in
      of_tuple (Name p.program_id, Some (of_constr f), fixprot)
    in
    List.rev (List.map2 fn fixprots progs)
  in
  let newsplits = List.map (fun (p, prog as x) -> p, prog, newsplits env fixdecls x) progs in
  principles env newsplits

let is_nested p =
  match p.program_rec_annot with
  | Some (NestedOn _) -> true
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
                          match p.program_rec_annot with
                          | Some (StructuralOn lid) -> lid
                          | _ -> (List.length p.program_sign) - 1) mutual in
     let evd = ref (Evd.from_env (Global.env ())) in
     let decl =
       let blockfn (p, prog) = 
         let na = Name p.program_id in
         let body = Evarutil.e_new_global evd (ConstRef prog.program_cst) in
         let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
         let rec fixsubst i acc l =
           match l with
           | (p', prog') :: rest ->
             (match p'.program_rec_annot with
             | Some (NestedOn idx) ->
               (match idx with
                | Some idx ->
                   let fixbody =
                     Vars.lift 1 (* lift over itself *)
                               (mkApp (mkConst prog'.program_cst,
                                       rel_vect (List.length p'.program_sign) (List.length mutual)))
                   in
                   let fixb = (Array.make 1 idx, 0) in
                   let fixna = Array.make 1 (Name p'.program_id) in
                   let fixty = Array.make 1 (it_mkProd_or_LetIn p'.program_arity p'.program_sign) in
                   (** Apply to itself *)
                   let fixbody = mkApp (fixbody, rel_vect (List.length p'.program_sign) 1) in
                   (** Apply to its arguments *)
                   let fixbody = mkApp (fixbody, extended_rel_vect 0 p'.program_sign) in
                   let fixbody = it_mkLambda_or_LetIn fixbody p'.program_sign in
                   let term = mkFix (fixb, (fixna, fixty, Array.make 1 fixbody)) in
                   fixsubst i (term :: acc) rest
                | None -> (* Non immediately recursive nested def *)
                   let term =
                     mkApp (mkConst prog'.program_cst, rel_vect 0 (List.length mutual))
                   in
                   fixsubst i (term :: acc) rest)
             | _ -> fixsubst (pred i) (mkRel i :: acc) rest)
           | [] -> List.rev acc
         in
         let body = mkApp (body, Array.of_list (fixsubst (List.length mutual) [] l)) in
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
         let kn =
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
     let declare_nested (p,prog) =
       let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
       let idx =
         match p.program_rec_annot with
         | Some (NestedOn lid) -> lid
         | _ -> None
       in
       let body =
         let body = e_new_global evd (ConstRef prog.program_cst) in
         let args = List.map_filter
                      (fun (p',prog') ->
                        if p'.program_id = p.program_id then
                          Option.map (fun _ -> mkRel 1) idx
                        else
                          Some (e_new_global evd (ConstRef prog'.program_cst))) fixes
         in
         let body = mkApp (body, Array.of_list args) in
         let body = mkApp (Vars.lift (List.length p.program_sign) body,
                           extended_rel_vect 0 p.program_sign) in
         let fixbody = it_mkLambda_or_LetIn body p.program_sign in
         match idx with
         | Some idx ->
            let fixb = (Array.make 1 idx, 0) in
            let fixna = Array.make 1 (Name p.program_id) in
            let fixty = Array.make 1 (it_mkProd_or_LetIn p.program_arity p.program_sign) in
            mkFix (fixb, (fixna, fixty, Array.make 1 fixbody))
         | None -> fixbody
       in
       let kn = declare_constant p.program_id body (Some ty) flags.polymorphic
                                 !evd (IsDefinition Fixpoint) in
       Impargs.declare_manual_implicits true (ConstRef kn) [p.program_impls];
       let prog' = { prog with program_cst = kn } in
       (p, prog')
     in
     let nested = List.map declare_nested nested in
     mutual @ nested
     
  
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
  let with_comp = with_comp && not !Equations_common.ocaml_splitting in
  let env = Global.env () in
  let poly = Flags.is_universe_polymorphism () in
  let flags = { polymorphic = poly; with_eqns; with_ind } in
  let evd = ref (Evd.from_env env) in
  let interp_arities (((loc,i),rec_annot,l,t),_ as ieqs) =
    let ienv, ((env', sign), impls) = interp_context_evars env evd l in
    let arity = interp_type_evars env' evd t in
    let sign = nf_rel_context_evar ( !evd) sign in
    let oarity = nf_evar ( !evd) arity in
    let is_rec = is_recursive i eqs in
    let interp_reca k i =
      match k with
      | Struct -> StructuralOn i
      | Nested -> NestedOn (Some i)
    in
    let rec_annot =
      match rec_annot with
      | None ->
         (match is_rec with
          | Some false -> Some (StructuralOn (List.length sign - 1))
          | _ -> None)
      | Some (reck, None) ->
         (match is_recursive i [ieqs] with (* Recursive in its own body? *)
          | Some _ -> Some (interp_reca reck (List.length sign - 1))
          | None -> if reck == Nested then Some (NestedOn None)
                    else Some (StructuralOn (List.length sign - 1)))
      | Some (reck, Some lid) ->
         try
           let k, _, _ = lookup_rel_id (snd lid) sign in
           Some (interp_reca reck (List.length sign - k))
         with Not_found ->
           user_err_loc (Some (fst lid), "struct_index",
                         Pp.(str"No argument named " ++ pr_id (snd lid) ++ str" found"))
    in
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
    match is_rec with
    | None ->
       { program_id = i;
         program_sign = sign;
         program_oarity = oarity;
         program_arity = oarity;
         program_rec_annot = rec_annot;
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
         let ce =
           Declare.definition_entry (* ~fix_exn: FIXME needed ? *)
				    ~poly ~univs:(snd (Evd.universe_context !evd))
                                    (to_constr !evd body)
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
       let compinfo = LogicalProj { comp = Option.map snd comp; comp_app = to_constr !evd compapp;
			            comp_proj = compproj; comp_recarg = succ (length sign) } in
       let compapp, is_rec =
	 if b then compapp, Some (Logical compinfo)
         else compapp, Some (Structural [])
       in
       { program_id = i;
         program_sign = sign;
         program_oarity = oarity;
         program_arity = compapp;
         program_rec_annot = rec_annot;
         program_rec = is_rec;
         program_impls = impls }
  in
  let arities = List.map interp_arities eqs in
  let recids = List.map (fun p ->
                   p.program_id, (match p.program_rec_annot with
                                  | Some ann -> ann
                                  | None -> NestedOn None), None)
                        arities in
  let arities = List.map (fun p ->
                    match p.program_rec with
                    | Some (Structural _) -> { p with program_rec = Some (Structural recids) }
                    | _ -> p) arities in
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
    env Constrintern.Recursive names (List.map (fun x -> to_constr !evd (fst x)) otys) impls
  in
  let fixprots =
    List.map (fun (oty, ty) ->
    mkLetIn (Anonymous,
             e_new_global evd (Lazy.force coq_fix_proto),
             e_new_global evd (Lazy.force coq_unit), ty)) otys in
  let fixdecls =
    List.map2 (fun i fixprot -> of_tuple (Name i, None, fixprot)) names fixprots in
  let fixdecls = List.rev fixdecls in
  let implsinfo = List.map (fun (_, (oty, ty), impls) ->
                  Impargs.compute_implicits_with_manual env (to_constr !evd oty) false impls) tys in
  let equations = 
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation data) nt;
      List.map3 (fun implsinfo ar eqs ->
        List.map (interp_eqn ar.program_id ar.program_rec env implsinfo) eqs)
        implsinfo arities eqs)
      ()
  in
  let fixdecls = nf_rel_context_evar !evd fixdecls in
  let covering env p eqs =
    let sign = nf_rel_context_evar !evd p.program_sign in
    let prob =
      if is_structural p.program_rec then
        match p.program_rec_annot with
        | Some (NestedOn None) -> (** Actually the definition is not self-recursive *)
           let fixdecls =
             List.filter (fun decl ->
                 let na = Context.Rel.Declaration.get_name decl in
                 let id = Nameops.out_name na in
                 not (Id.equal id p.program_id)) fixdecls
           in
           id_subst (sign @ fixdecls)
        | _ -> id_subst (sign @ fixdecls)
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
    let split = map_evars_in_split !evd (fun f x -> of_constr (cmap f x)) split in
    let p = nf_program_info !evd p in
    let compiled_info = { program_cst = f_cst;
                          program_cmap = cmap;
                          program_split = split;
                          program_split_info = info } in
    progs.(i) <- Some (p, compiled_info);
    if CArray.for_all (fun x -> not (Option.is_empty x)) progs then
      (let fixprots = List.map (nf_evar !evd) fixprots in
       let progs = Array.map_to_list (fun x -> Option.get x) progs in
       let progs' = define_mutual_nested flags progs in
       if flags.with_eqns || flags.with_ind then
         define_principles flags fixprots progs')
  in
  let idx = ref 0 in
  let define_tree p split =
    let comp = match p.program_rec with
      Some (Logical l) -> Some l
    | _ -> None
    in
    let fixdecls =
      match p.program_rec_annot with
      | Some (NestedOn None) -> (** Actually the definition is not self-recursive *)
         List.filter (fun decl ->
             let na = Context.Rel.Declaration.get_name decl in
             let id = Nameops.out_name na in
             not (Id.equal id p.program_id)) fixdecls
      | _ -> fixdecls
    in
    define_tree p.program_rec fixdecls poly p.program_impls status evd env
                (p.program_id, p.program_sign, p.program_oarity)
		comp split (hook !idx p);
    incr idx
  in CList.iter2 define_tree arities coverings

let with_rollback f x =
  States.with_state_protection_on_exception f x

let equations opts eqs nt =
  List.iter (fun (((loc, i), nested, l, t),eqs) -> Dumpglob.dump_definition (Some loc, i) false "def") eqs;
  define_by_eqs opts eqs nt

let solve_equations_goal destruct_tac tac gl =
  let concl = pf_concl gl in
  let intros, move, concl =
    let rec intros goal move = 
      match kind_of_term goal with
      | Prod (Name id, _, t) -> 
         let id = fresh_id_in_env [] id (pf_env gl) in
         let tac, move, goal = intros (subst1 (Constr.mkVar id) t) (Some id) in
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
    intros (to_constr (project gl) concl) None
  in
  let move_tac = 
    match move with
    | None -> fun _ -> tclIDTAC
    | Some id' -> fun id -> to82 (move_hyp id (Misctypes.MoveBefore id'))
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
        if Idset.mem n variables then Idset.union dvars variables
        else variables)
      ~init:init ctx
  in
    (init, Idset.diff deps init)
