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
open Inductiveops
open Globnames
open Reductionops
open Pp
open List
open Constrexpr
open Tactics
open Evarutil
open Evar_kinds
open Equations_common
open Syntax
open EConstr
open EConstr.Vars
open Context_map

(** Splitting trees *)

type path_component =
  | Evar of Evar.t
  | Ident of Id.t

type path = path_component list

type splitting =
  | Compute of context_map * where_clause list * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Valid of context_map * types * identifier list * Tacmach.tactic *
             (Proofview.entry * Proofview.proofview) *
             (Goal.goal * constr list * context_map * context_map option * splitting) list
  | Mapping of context_map * splitting (* Mapping Γ |- p : Γ' and splitting Γ' |- p : Δ *)
  | RecValid of identifier * splitting
  | Refined of context_map * refined_node * splitting

and where_clause =
  { where_program : program_info;
    where_program_orig : program_info;
    where_path : path;
    where_orig : path;
    where_context_length : int; (* Length of enclosing context, including fixpoint prototype if any *)
    where_prob : context_map;
    where_arity : types; (* In pi1 prob *)
    where_term : constr; (* In original context, de Bruijn only *)
    where_type : types;
    where_splitting : splitting Lazy.t }

and refined_node =
  { refined_obj : identifier * constr * types;
    refined_rettyp : types;
    refined_arg : int;
    refined_path : path;
    refined_ex : Evar.t;
    refined_app : constr * constr list;
    refined_revctx : context_map;
    refined_newprob : context_map;
    refined_newprob_to_lhs : context_map;
    refined_newty : types }

and splitting_rhs =
  | RProgram of constr
  | REmpty of int

let rec context_map_of_splitting : splitting -> context_map = function
  | Compute (subst, _, _, _) -> subst
  | Split (subst, _, _, _) -> subst
  | Valid (subst, _, _, _, _, _) -> subst
  | Mapping (subst, _) -> subst
  | RecValid (_, s) -> context_map_of_splitting s
  | Refined (subst, _, _) -> subst

let pr_path_component evd = function
  | Evar ev -> Termops.pr_existential_key evd ev
  | Ident id -> Id.print id

let pr_path evd = prlist_with_sep (fun () -> str":") (pr_path_component evd)

let path_component_eq x y =
  match x, y with
  | Evar ev, Evar ev' -> Evar.equal ev ev'
  | Ident id, Ident id' -> Id.equal id id'
  | _, _ -> false

let eq_path path path' =
  let rec aux path path' =
    match path, path' with
    | [], [] -> true
    | hd :: tl, hd' :: tl' -> path_component_eq hd hd' && aux tl tl'
    | _, _ -> false
  in
  aux path path'

let where_id w = w.where_program.program_id

let where_context wheres =
  List.map (fun ({where_program; where_term;
                 where_type; where_splitting } as w) ->
             make_def (Name (where_id w)) (Some where_term) where_type) wheres

let pr_rec_info p =
  let open Pp in
  Names.Id.print p.program_id ++ str " is " ++
  match p.program_rec with
  | Some (Structural ann) ->
    (match ann with
     | MutualOn (i,_) -> str "mutually recursive on " ++ int i
     | NestedOn (Some (i,_)) -> str "nested on " ++ int i
     | NestedOn None -> str "nested but not directly recursive")
  | Some (WellFounded (c, r, info)) ->
    str "wellfounded"
  | None -> str "not recursive"

let pr_splitting env sigma ?(verbose=false) split =
  let verbose pp = if verbose then pp else mt () in
  let pplhs env sigma lhs = pr_pats env sigma (pi2 lhs) in
  let rec aux = function
    | Compute (lhs, wheres, ty, c) ->
      let env' = push_rel_context (pi1 lhs) env in
      let ppwhere w =
        hov 2 (str"where " ++ Id.print (where_id w) ++ str " : " ++
               (try Printer.pr_econstr_env env'  sigma w.where_type ++
                    hov 1 (str "(program type: " ++ Printer.pr_econstr_env env sigma (program_type w.where_program)
                    ++ str ") ") ++ pr_rec_info w.where_program ++
                    str "(where_term: " ++ Printer.pr_econstr_env env sigma w.where_term ++ str ")" ++
                    str "(arity: " ++ Printer.pr_econstr_env env sigma w.where_arity ++ str ")" ++
                    str" (where context length : " ++ int w.where_context_length ++ str ")" ++
                    str " := " ++ Pp.fnl () ++ aux (Lazy.force w.where_splitting)
                with e -> str "*raised an exception"))
      in
      let ppwheres = prlist_with_sep Pp.fnl ppwhere wheres in
      let env'' = push_rel_context (where_context wheres) env' in
      ((match c with
          | RProgram c -> pplhs env' sigma lhs ++ str" := " ++
                          Printer.pr_econstr_env env'' sigma c ++
                          (verbose (str " : " ++ Printer.pr_econstr_env env'' sigma ty))
          | REmpty i -> pplhs env' sigma lhs ++ str" :=! " ++
                        pr_rel_name env'' i)
       ++ Pp.fnl () ++ ppwheres ++
       verbose (str " in context " ++  pr_context_map env sigma lhs))
    | Split (lhs, var, ty, cs) ->
      let env' = push_rel_context (pi1 lhs) env in
      (pplhs env' sigma lhs ++ str " split: " ++ pr_rel_name env' var ++
       Pp.fnl () ++
       verbose (str" : " ++
                Printer.pr_econstr_env env' sigma ty ++
                str " in context " ++
                pr_context_map env sigma lhs ++ spc ()) ++
       (Array.fold_left
          (fun acc so -> acc ++
                         h 2 (match so with
                             | None -> str "*impossible case*" ++ Pp.fnl ()
                             | Some s -> aux s))
          (mt ()) cs))
    | Mapping (ctx, s) ->
      hov 2 (str"Mapping " ++ pr_context_map env sigma ctx ++ Pp.fnl () ++ aux s)
    | RecValid (id, c) ->
      hov 2 (str "RecValid " ++ Id.print id ++ Pp.fnl () ++ aux c)
    | Valid (lhs, ty, ids, ev, tac, cs) ->
      let _env' = push_rel_context (pi1 lhs) env in
      hov 2 (str "Valid " ++ str " in context " ++ pr_context_map env sigma lhs ++
             List.fold_left
               (fun acc (gl, cl, subst, invsubst, s) -> acc ++ aux s) (mt ()) cs)
    | Refined (lhs, info, s) ->
      let (id, c, cty), ty, arg, path, ev, (scf, scargs), revctx, newprob, newty =
        info.refined_obj, info.refined_rettyp,
        info.refined_arg, info.refined_path,
        info.refined_ex, info.refined_app,
        info.refined_revctx, info.refined_newprob, info.refined_newty
      in
      let env' = push_rel_context (pi1 lhs) env in
      hov 2 (pplhs env' sigma lhs ++ str " refine " ++ Id.print id ++ str" " ++
             Printer.pr_econstr_env env' sigma (mapping_constr sigma revctx c) ++
             verbose (str " : " ++ Printer.pr_econstr_env env' sigma cty ++ str" " ++
                      Printer.pr_econstr_env env' sigma ty ++ str" " ++
                      str " in " ++ pr_context_map env sigma lhs ++ spc () ++
                      str "New problem: " ++ pr_context_map env sigma newprob ++ str " for type " ++
                      Printer.pr_econstr_env (push_rel_context (pi1 newprob) env) sigma newty ++ spc () ++
                      spc () ++ str" eliminating " ++ pr_rel_name (push_rel_context (pi1 newprob) env) arg ++ spc () ++
                      str "Revctx is: " ++ pr_context_map env sigma revctx ++ spc () ++
                      str "New problem to problem substitution is: " ++
                      pr_context_map env sigma info.refined_newprob_to_lhs ++ Pp.cut ()) ++
             aux s)
  in aux split

let pp s = pp_with !Topfmt.deep_ft s

let ppsplit s =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  pp (pr_splitting env sigma s)

let map_where f w =
  { w with
    where_program = map_program_info f w.where_program;
    where_prob = map_ctx_map f w.where_prob;
    where_term = f w.where_term;
    where_arity = f w.where_arity;
    where_type = f w.where_type }
    
let map_split f split =
  let rec aux = function
    | Compute (lhs, where, ty, RProgram c) ->
      let where' = 
        List.map
          (fun w -> let w' = map_where f w in
                 { w' with where_splitting = Lazy.from_val (aux (Lazy.force w.where_splitting)) })
          where
      in
      let lhs' = map_ctx_map f lhs in
	Compute (lhs', where', f ty, RProgram (f c))
    | Split (lhs, y, z, cs) ->
      let lhs' = map_ctx_map f lhs in
      Split (lhs', y, f z, Array.map (Option.map aux) cs)
    | Mapping (lhs, s) ->
       let lhs' = map_ctx_map f lhs in
       Mapping (lhs', aux s)
    | RecValid (id, c) -> RecValid (id, aux c)
    | Valid (lhs, y, z, w, u, cs) ->
      let lhs' = map_ctx_map f lhs in
	Valid (lhs', f y, z, w, u, 
	       List.map (fun (gl, cl, subst, invsubst, s) -> 
		 (gl, List.map f cl, map_ctx_map f subst, invsubst, aux s)) cs)
    | Refined (lhs, info, s) ->
      let lhs' = map_ctx_map f lhs in
      let (id, c, cty) = info.refined_obj in
      let (scf, scargs) = info.refined_app in
	Refined (lhs', { info with refined_obj = (id, f c, f cty);
	  refined_app = (f scf, List.map f scargs);
	  refined_rettyp = f info.refined_rettyp;
	  refined_revctx = map_ctx_map f info.refined_revctx;
	  refined_newprob = map_ctx_map f info.refined_newprob;
	  refined_newprob_to_lhs = map_ctx_map f info.refined_newprob_to_lhs;
	  refined_newty = f info.refined_newty}, aux s)
    | Compute (lhs, where, ty, (REmpty _ as em)) ->
       let lhs' = map_ctx_map f lhs in
       Compute (lhs', where, f ty, em)
  in aux split

let is_nested p =
  match p.program_rec with
  | Some (Structural (NestedOn _)) -> true
  | _ -> false

let define_mutual_nested evd get_prog progs =
  let mutual =
    List.filter (fun (p, prog) -> not (is_nested p)) progs
  in
  (* In the mutually recursive case, only the functionals have been defined,
     we build the block and its projections now *)
  let structargs = Array.map_of_list (fun (p,_) ->
                   match p.program_rec with
                   | Some (Structural (MutualOn (lid,_))) -> lid
                   | _ -> (List.length p.program_sign) - 1) mutual in
  let mutualapp, nestedbodies =
    let nested = List.length progs - List.length mutual in
    let one_nested before p prog afterctx idx =
      let signlen = List.length p.program_sign in
      let fixbody =
        Vars.lift 1 (* lift over itself *)
           (mkApp (get_prog prog, rel_vect (signlen + (nested - 1)) (List.length mutual)))
         in
         let after = (nested - 1) - before in
         let fixb = (Array.make 1 idx, 0) in
         let fixna = Array.make 1 (Name p.program_id) in
         let fixty = Array.make 1 (it_mkProd_or_LetIn p.program_arity p.program_sign) in
         (* Apply to itself *)
         let beforeargs = Termops.rel_list (signlen + 1) before in
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
         (* Apply to its arguments *)
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
                   mkApp (get_prog prog', rel_vect 0 (List.length mutual))
                 in
                   fixsubst i (succ k) ((true, term) :: acc) rest)
             | _ -> fixsubst (pred i) k ((false, mkRel i) :: acc) rest)
         | [] -> List.rev acc
       in
       (* aux1 ... auxn *)
       let nested = fixsubst (List.length mutual) 0 [] progs in
       let nested, mutual = List.partition (fun (x, y) -> x) nested in
       let gns = List.fold_right (fun (_, g) acc -> applist (g, acc) :: acc) nested [] in
       let nested = List.fold_left (fun acc g -> applist (g, List.rev acc) :: acc) [] gns in
       let nested = List.rev_map (Reductionops.nf_beta (Global.env ()) !evd) nested in
       List.map snd mutual, nested
     in
     let decl =
       let blockfn (p, prog) =
         let na = Name p.program_id in
         let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
         let body = mkApp (get_prog prog, Array.append (Array.of_list mutualapp) (Array.of_list nestedbodies)) in
         let body = mkApp (Vars.lift (List.length p.program_sign) body,
                           extended_rel_vect 0 p.program_sign) in
         let body = it_mkLambda_or_LetIn body (lift_rel_context 1 p.program_sign) in
         na, ty, body
       in
       let blockl = List.map blockfn mutual in
       let names, tys, bodies = List.split3 blockl in
       Array.of_list names, Array.of_list tys, Array.of_list bodies
     in
     let nested, mutual = List.partition (fun (p,prog) -> is_nested p) progs in
     let declare_fix_fns i (p,prog) =
       let fix = mkFix ((structargs, i), decl) in
       (p, prog, fix)
     in
     let fixes = List.mapi declare_fix_fns mutual in
     let declare_nested (p,prog) body = (p, prog, body) in
     let nested = List.map2 declare_nested nested nestedbodies in
     fixes, nested

let helper_evar evm evar env typ src =
  let sign, typ', instance, _ = push_rel_context_to_named_context ~hypnaming:KeepExistingNames env evm typ in
  let evm' = evar_declare sign evar typ' ~src evm in
    evm', mkEvar (evar, Array.of_list instance)

let path_id path =
  match List.rev path with
  | Ident hd :: tl ->
    List.fold_left (fun id prefix ->
        match prefix with
        | Ident id' -> add_suffix (add_suffix id "_") (Id.to_string id')
        | Evar _ -> assert false) hd tl
  | _ -> assert false

let term_of_tree flags isevar env0 tree =
  let oblevars = ref Evar.Map.empty in
  let helpers = ref [] in
  let rec aux env evm = function
    | Compute ((ctx, _, _), where, ty, RProgram rhs) ->
      let compile_where ({where_program; where_prob; where_term; where_type; where_splitting} as w)
          (env, evm, ctx) =
        (* let env = push_rel_context ctx env0 in *)
        (* FIXME push ctx too if mutual wheres *)
        let where_args = snd (decompose_appvect evm where_term) in
        let evm, c', _ = aux env evm (Lazy.force where_splitting) in
        let evd = ref evm in
        let c' =
          match where_program.program_rec with
          | Some (Structural _) ->
            let c' = mkApp (c', where_args) in
            let c' = (whd_beta !evd c')  in
            let before, after =
              CList.chop ((CList.length where_program.program_sign) - w.where_context_length)
                where_program.program_sign
            in
            let subst = mkProp :: List.rev (Array.to_list where_args) in
            let program_sign = subst_rel_context 0 subst before in
            let program_arity = substnl subst (List.length program_sign) where_program.program_arity in
            let where_program = { where_program with program_sign; program_arity } in
            (match define_mutual_nested evd (fun x -> x) [(where_program, lift 1 c')] with
             | [(m, _, body)], _ ->
               it_mkLambda_or_LetIn body (List.tl after)
             | _, [(m, _, body)] -> it_mkLambda_or_LetIn body (List.tl after)
             | _ -> assert false)
          | _ -> c'
        in
        let c' = nf_beta env !evd c' in
        let ty' = Retyping.get_type_of env !evd c' in
        let () =
          if !Equations_common.debug then
            Feedback.msg_debug Pp.(str "Where_clause compiled to" ++ Printer.pr_econstr_env env !evd c' ++
                                   str " of type " ++ Printer.pr_econstr_env env !evd ty')
        in
        let evm, c', ty' =
          let hd, args = decompose_appvect evm where_term in
          match kind evm hd with
          | Evar (ev, _) when false ->
            let term' = mkLetIn (Name (Id.of_string "prog"), c', ty', lift 1 ty') in
            let evm, term =
              helper_evar evm ev env term'
                (dummy_loc, QuestionMark {
                    qm_obligation=Define false;
                    qm_name=Name (where_id w);
                    qm_record_field=None;
                  }) in
            let ev = fst (destEvar !isevar term) in
            oblevars := Evar.Map.add ev 0 !oblevars;
            helpers := (ev, 0) :: !helpers;
            evm, where_term, where_type
          | Evar (ev, _) when false ->
            Evd.define ev c' evm, where_term, where_type
          | _ -> evm, where_term, where_type
        in
        (env, evm, (make_def (Name (where_id w)) (Some c') ty' :: ctx))
      in
      let env, evm, ctx = List.fold_right compile_where where (env, evm,ctx) in
      let body = it_mkLambda_or_LetIn rhs ctx and typ = it_mkProd_or_subst env evm ty ctx in
      evm, body, typ

    | Compute ((ctx, _, _), where, ty, REmpty split) ->
       assert (List.is_empty where);
       let evm, coq_nat = new_global evm (Lazy.force coq_nat) in
        let split = make_def (Name (Id.of_string "split"))
          (Some (of_constr (coq_nat_of_int (succ (length ctx - split)))))
          coq_nat
       in
       let ty' = it_mkProd_or_LetIn ty ctx in
       let let_ty' = mkLambda_or_LetIn split (lift 1 ty') in
       let evm, term = 
         new_evar env evm ~src:(dummy_loc, QuestionMark {
            qm_obligation=Define false;
            qm_name=Anonymous;
            qm_record_field=None;
        }) let_ty' in
       let ev = fst (destEvar evm term) in
       oblevars := Evar.Map.add ev 0 !oblevars;
       evm, term, ty'

    | Mapping ((ctx, p, ctx'), s) ->
       let evm, term, ty = aux env evm s in
       let args = Array.rev_of_list (snd (constrs_of_pats ~inacc_and_hide:false env evm p)) in
       let term = it_mkLambda_or_LetIn (whd_beta evm (mkApp (term, args))) ctx in
       let ty = it_mkProd_or_subst env evm (prod_appvect evm ty args) ctx in
         evm, term, ty
		    
    | RecValid (id, rest) -> aux env evm rest

    | Refined ((ctx, _, _), info, rest) ->
	let (id, _, _), ty, rarg, path, ev, (f, args), newprob, newty =
	  info.refined_obj, info.refined_rettyp,
	  info.refined_arg, info.refined_path,
	  info.refined_ex, info.refined_app, info.refined_newprob, info.refined_newty
	in
	let evm, sterm, sty = aux env evm rest in
	let evm, term, ty = 
          let term = mkLetIn (Name (Id.of_string "prog"), sterm, sty, lift 1 sty) in
	  let evm, term = helper_evar evm ev (Global.env ()) term
        (dummy_loc, QuestionMark {
            qm_obligation=Define false;
            qm_name=Name id;
            qm_record_field=None;
        })
	  in
	    oblevars := Evar.Map.add ev 0 !oblevars;
	    helpers := (ev, rarg) :: !helpers;
	    evm, term, ty
	in
	let term = applist (f, args) in
	let term = it_mkLambda_or_LetIn term ctx in
        let ty = it_mkProd_or_subst env evm ty ctx in
	  evm, term, ty

    | Valid ((ctx, _, _), ty, substc, tac, (entry, pv), rest) ->
	let tac = Proofview.tclDISPATCH 
          (List.map (fun (goal, args, subst, invsubst, x) ->
            Refine.refine ~typecheck:false begin fun evm ->
              let evm, term, ty = aux env evm x in
              (evm, applistc term args) end) rest)
	in
        let tac = Proofview.tclTHEN (Proofview.Unsafe.tclEVARS evm) tac in
	let _, pv', _, _ = Proofview.apply env tac pv in
	let c = List.hd (Proofview.partial_proof entry pv') in
	  Proofview.return pv', 
	  it_mkLambda_or_LetIn (subst_vars substc c) ctx, it_mkProd_or_LetIn ty ctx
	      
    | Split ((ctx, _, _) as subst, rel, ty, sp) ->
      (* Produce parts of a case that will be relevant. *)
      let evm, block = Equations_common.(get_fresh evm coq_block) in
      let ty = mkLetIn (Anonymous, block, Retyping.get_type_of env evm block, lift 1 ty) in
      let evd = ref evm in
      let ctx', case_ty, branches_res, nb_cuts, rev_subst, to_apply, simpl =
        Sigma_types.smart_case env evd ctx rel ty in

      (* The next step is to use [simplify]. *)
      let simpl_step = if simpl then
          Simplify.simplify [None, Simplify.Infer_many] env evd
        else Simplify.identity env evd
      in
      let branches = Array.map2 (fun (ty, nb, csubst) next ->
        (* We get the context from the constructor arity. *)
        let new_ctx, ty = EConstr.decompose_prod_n_assum !isevar nb ty in
        let new_ctx = Namegen.name_context env !isevar new_ctx in
        let ty =
          if simpl || nb_cuts > 0 then
            let env = push_rel_context (new_ctx @ ctx') env in
            Tacred.hnf_constr env !evd ty
          else ty
        in
        (* Remove the cuts and append them to the context. *)
        let cut_ctx, ty = EConstr.decompose_prod_n_assum !isevar nb_cuts ty in
        (* TODO This context should be the same as (pi1 csubst). We could
           * either optimize (but names in [csubst] are worse) or just insert
           * a sanity-check. *)
        if !Equations_common.debug then begin
          let open Feedback in
          let ctx = cut_ctx @ new_ctx @ ctx' in
          msg_info(str"Simplifying term:");
          msg_info(let env = push_rel_context ctx env in
                   Printer.pr_econstr_env env !evd ty);
          msg_info(str"... in context:");
          msg_info(pr_context env !evd ctx);
          msg_info(str"... named context:");
          msg_info(Printer.pr_named_context env !evd (EConstr.Unsafe.to_named_context (named_context env)));
        end;
        let ((hole, c), lsubst) = simpl_step (cut_ctx @ new_ctx @ ctx', ty) in
        if !debug then
          begin
            let open Feedback in
            msg_debug (str"Finished simplifying");
            msg_info(let env = push_rel_context ctx env in
                     Printer.pr_econstr_env env !evd c);
          end;
        let subst = compose_subst ~unsafe:true env ~sigma:!evd csubst subst in
        let subst = compose_subst ~unsafe:true env ~sigma:!evd lsubst subst in
        (* Now we build a term to put in the match branch. *)
        let c =
          match hole, next with
          (* Dead code: we should have found a proof of False. *)
          | None, None -> c
          (* Normal case: build recursively a subterm. *)
          | Some ((next_ctx, _), ev), Some s ->
            let evm, next_term, next_ty = aux env !evd s in
            (* Now we need to instantiate [ev] with the term [next_term]. *)
            (* [next_term] starts with lambdas, so we apply it to its context. *)
            let args = Equations_common.extended_rel_vect 0 next_ctx in
            let next_term = beta_appvect !isevar next_term args in
            (* We might need to permutate some rels. *)
            let next_subst = context_map_of_splitting s in
            let perm_subst = Context_map.make_permutation ~env evm subst next_subst in
            let next_term = Context_map.mapping_constr evm perm_subst next_term in
            (* We know the term is a correct instantiation of the evar, we
             * just need to apply it to the correct variables. *)
            let ev_info = Evd.find_undefined evm (fst ev) in
            let ev_ctx = Evd.evar_context ev_info in
            (* [next_term] is typed under [env, next_ctx] while the evar
             * is typed under [ev_ctx] *)
            let ev_ctx_constrs = List.map (fun decl ->
                let id = Context.Named.Declaration.get_id decl in
                EConstr.mkVar id) ev_ctx in
            let rels, named = List.chop (List.length next_ctx) ev_ctx_constrs in
            let vars_subst = List.map2 (fun decl c ->
                let id = Context.Named.Declaration.get_id decl in
                id, c) (Environ.named_context env) named in
            let term = Vars.replace_vars vars_subst next_term in
            let term = Vars.substl rels term in
            let _ =
              let env = Evd.evar_env ev_info in
              Typing.type_of env evm term
            in
            evd := Evd.define (fst ev) term evm;
            c
          (* This should not happen... *)
          | _ -> failwith "Should not fail here, please report."
        in
        EConstr.it_mkLambda_or_LetIn c (cut_ctx @ new_ctx)
        ) branches_res sp in

      (* Get back to the original context. *)
      let case_ty = mapping_constr !evd rev_subst case_ty in
      let branches = Array.map (mapping_constr !evd rev_subst) branches in

      (* Fetch the type of the variable that we want to eliminate. *)
      let after, decl, before = split_context (pred rel) ctx in
      let rel_ty = Context.Rel.Declaration.get_type decl in
      let rel_ty = Vars.lift rel rel_ty in
      let rel_t = EConstr.mkRel rel in
      let pind, args = find_inductive env !evd rel_ty in

      (* Build the case. *)
      let case_info = Inductiveops.make_case_info env (fst pind) Constr.RegularStyle in
      let indfam = Inductiveops.make_ind_family (from_peuniverses !evd pind, args) in
      let case = Inductiveops.make_case_or_project env !evd indfam case_info
          case_ty rel_t branches in
      let term = EConstr.mkApp (case, Array.of_list to_apply) in
      let term = EConstr.it_mkLambda_or_LetIn term ctx in
      let typ = it_mkProd_or_subst env evm ty ctx in
      let term = Evarutil.nf_evar !evd term in
      evd := Typing.check env !evd term typ;
      !evd, term, typ
  in
  let evm, term, typ = aux env0 !isevar tree in
    isevar := evm;
    !helpers, !oblevars, term, typ


let change_lhs s (l, p, r) =
  let open Context.Rel.Declaration in
  let l' =
    List.map
      (function LocalDef (Name id, b, t) as decl ->
         (try let b' = List.assoc id s in LocalDef (Name id, b', t)
          with Not_found -> decl)
              | decl -> decl) l
  in l', p, r

let change_splitting s sp =
  let rec aux = function
    | Compute (lhs, where, ty, r) ->
      Compute (change_lhs s lhs, where, ty, r)
    | Split (lhs, rel, ty, sp) ->
      Split (change_lhs s lhs, rel, ty, Array.map (fun x -> Option.map aux x) sp)
    | Mapping (lhs, sp) ->
      Mapping (change_lhs s lhs, aux sp)
    | RecValid (id, rest) -> RecValid (id, aux rest)
    | Refined (lhs, info, rest) ->
      Refined (change_lhs s lhs, info, aux rest)
    | Valid (lhs, ty, substc, tac, (entry, pv), rest) ->
      let rest' = List.map (fun (gl, x, y, z, w) ->
          (gl, x, y, z, aux w)) rest in
      Valid (lhs, ty, substc, tac, (entry, pv), rest')
  in aux sp

let define_constants flags isevar env0 tree =
  let () = assert (not (Evd.has_undefined !isevar)) in
  let helpers = ref [] in
  let rec aux env evm = function
    | Compute (lhs, where, ty, RProgram rhs) ->
      let define_where ({where_program; where_prob; where_term; where_type; where_splitting; where_path} as w)
          (env, evm, s, ctx) =
        let where_term, where_args = decompose_appvect evm where_term in
        let (cst, (evm, e)) =
          Equations_common.declare_constant (path_id where_path)
            where_term (Some (program_type where_program))
            flags.polymorphic evm (Decl_kinds.(IsDefinition Definition))
        in
        let env = Global.env () in
        let evm = Evd.update_sigma_env evm env in
        let where_term = mkApp (e, where_args) in
        let w' = { w with where_term; where_prob = change_lhs s where_prob;
                          where_splitting = Lazy.from_val (change_splitting s (Lazy.force w.where_splitting)) } in
        (env, evm, (where_id w, where_term) :: s, w' :: ctx)
      in
      let env, evm, _, where = List.fold_right define_where where (env, evm, [], []) in
      evm, Compute (lhs, where, ty, RProgram rhs)

    | Compute (lhs, where, ty, REmpty split) ->
      evm, Compute (lhs, where, ty, REmpty split)

    | Mapping (lhs, s) ->
      let evm, s' = aux env evm s in
      evm, Mapping (lhs, s')

    | RecValid (id, rest) ->
      let evm, s' = aux env evm rest in
      evm, RecValid (id, s')

    | Refined ((ctx, _, _) as lhs, info, rest) ->
      let evm', rest' = aux env evm rest in
      let isevar = ref evm' in
      let _, _, t, ty = term_of_tree flags isevar env rest' in
      let (cst, (evm, e)) =
        Equations_common.declare_constant (pi1 info.refined_obj)
          t (Some ty) flags.polymorphic !isevar (Decl_kinds.(IsDefinition Definition))
      in
      let () = helpers := (cst, info.refined_arg) :: !helpers in
      evm, Refined (lhs, { info with refined_app = (e, snd info.refined_app) }, rest')

    | Valid ((ctx, _, _) as lhs, ty, substc, tac, (entry, pv), rest) ->
      let isevar = ref evm in
      let rest' = List.map (fun (gl, x, y, z, w) ->
          let evm', w' = aux env !isevar w in
          isevar := evm'; gl, x, y, z, w') rest in
      !isevar, Valid (lhs, ty, substc, tac, (entry, pv), rest')

    | Split (lhs, rel, ty, sp) ->
      let evm, sp' = CArray.fold_left_map (fun evm s ->
          match s with
          | Some s -> let evm, s' = aux env evm s in evm, Some s'
          | None -> evm, None) evm sp
      in evm, Split (lhs, rel, ty, sp')
  in
  let evm, tree = aux env0 !isevar tree in
    isevar := evm; tree

let is_comp_obl sigma comp hole_kind =
  match comp with
  | None -> false
  | Some r -> 
      match hole_kind, r with 
      | ImplicitArg (ConstRef c, (n, _), _), (loc, id) ->
        is_rec_call sigma r (mkConst c)
      | _ -> false

let zeta_red =
  let red = Tacred.cbv_norm_flags
      CClosure.(RedFlags.red_add RedFlags.no_red RedFlags.fZETA)
  in
    reduct_in_concl (red, DEFAULTcast)

type term_info = {
  term_id : Names.GlobRef.t;
  term_ustate : UState.t;
  term_evars : (Id.t * Constr.t) list;
  base_id : string;
  decl_kind: Decl_kinds.definition_kind;
  helpers_info : (Evar.t * int * identifier) list;
  comp_obls : Id.Set.t; (** The recursive call proof obligations *)
  user_obls : Id.Set.t; (** The user obligations *)
}

type compiled_program_info = {
    program_cst : Constant.t;
    program_split : splitting;
    program_split_info : term_info }
                  

let is_polymorphic info = pi2 info.decl_kind


let solve_equations_obligations flags i isevar split hook =
  let kind = (Decl_kinds.Local, flags.polymorphic, Decl_kinds.(DefinitionBody Definition)) in
  let _hook uctx evars locality gr = ()
    (* let l =
     *   Array.map_to_list (fun (id, ty, loc, s, d, tac) -> Libnames.qualid_of_ident id) obls in
     * Extraction_plugin.Table.extraction_inline true l; *)
    (* let kind = (locality, poly, Decl_kinds.Definition) in
     * let baseid = Id.to_string i in
     * let term_info = { term_id = gr; term_ustate = uctx; term_evars = evars;
     *                   base_id = baseid; helpers_info = []; decl_kind = kind;
     *                   comp_obls = Id.Set.empty; user_obls = Id.Set.empty(\* union !compobls !userobls *\) } in
     *   hook split (fun x -> x) term_info uctx *)
  in
  let evars = Evar.Map.bindings (Evd.undefined_map !isevar) in
  let env = Global.env () in
  let types =
    List.map (fun (ev, evi) ->
        let type_ = Termops.it_mkNamedProd_or_LetIn evi.Evd.evar_concl (Evd.evar_context evi) in
        env, ev, evi, type_) evars in
  (* Make goals from a copy of the evars *)
  let isevar0 = ref !isevar in
  let tele =
    let rec aux types evm =
      match types with
      | [] -> Proofview.TNil evm
      | (evar_env, ev, evi, type_) :: tys ->
        let evar_env = nf_env_evar !isevar0 evar_env in
        Proofview.TCons (evar_env, evm, nf_evar !isevar0 type_,
           (fun evm' wit ->
             isevar0 := Evd.define ev (applist (wit, List.rev (Context.Named.to_instance mkVar (Evd.evar_context evi)))) !isevar0;
             aux tys evm'))
    in aux types (Evd.from_env env)
  in
  let terminator = function
    | Proof_global.Admitted (id, gk, pe, us) ->
      user_err_loc (None, "end_obligations", str "Cannot handle admitted proof for equations")
    | Proof_global.Proved (opaque, lid, obj) ->
      Feedback.msg_debug (str"Should define the initial evars accoding to the proofs");
      let open Decl_kinds in
      let obls = ref 0 in
      let kind = match pi3 obj.Proof_global.persistence with
        | DefinitionBody d -> IsDefinition d
        | Proof p -> IsProof p
      in
      let () =
        List.iter2 (fun (evar_env, ev, evi, type_) entry ->
            let id =
              match Evd.evar_ident ev !isevar with
              | Some id -> id
              | None -> let n = !obls in incr obls; add_suffix i ("_obligation_" ^ string_of_int n)
            in
            let cst = Declare.declare_constant id (Entries.DefinitionEntry entry, kind) in
            let newevars, app = Evarutil.new_global !isevar (ConstRef cst) in
            isevar :=
              Evd.define ev (applist (app, List.rev (Context.Named.to_instance mkVar (Evd.evar_context evi))))
                newevars)
          types obj.Proof_global.entries
      in hook split
  in
  Feedback.msg_debug (str"Starting proof");
  Proof_global.(start_dependent_proof i kind tele (make_terminator terminator))
  (* Proof_global.simple_with_current_proof (fun _ p  -> Proof.V82.grab_evars p) *)


let define_tree is_recursive fixprots flags impls status isevar env (i, sign, arity)
                comp split hook =
  let env = Global.env () in
  let helpers, oblevs, t, ty = term_of_tree flags isevar env split in
  let obls, (emap, cmap), t', ty' =
    (* XXX: EConstr Problem upstream indeed. *)
    Obligations.eterm_obligations env i !isevar
      0 ~status (EConstr.to_constr ~abort_on_undefined_evars:false !isevar t)
                (EConstr.to_constr ~abort_on_undefined_evars:false !isevar (whd_betalet !isevar ty))
  in
  let compobls = ref Id.Set.empty in
  let userobls = ref Id.Set.empty in
  let obls = 
    Array.map (fun (id, ty, loc, s, d, t) ->
      let assc = rev_assoc Id.equal id emap in
      let tac = 
	if Evar.Map.mem assc oblevs 
	then 
          let intros = Evar.Map.find assc oblevs in
          Some (Tacticals.New.tclTHEN (Tacticals.New.tclDO intros intro) (equations_tac ()))
        else if is_comp_obl !isevar comp (snd loc) then
          let () = compobls := Id.Set.add id !compobls in
          let open Tacticals.New in
	    Some (tclORELSE
		    (tclTRY
                       (tclTHENLIST [zeta_red; Tactics.intros; solve_rec_tac ()]))
		    !Obligations.default_tactic)
        else (userobls := Id.Set.add id !userobls;
              Some ((!Obligations.default_tactic)))
      in (id, ty, loc, s, d, tac)) obls
  in
  let helpers = List.map (fun (ev, arg) ->
    (ev, arg, List.assoc ev emap)) helpers
  in
  let hook uctx evars locality gr =
    let l =
      Array.map_to_list (fun (id, ty, loc, s, d, tac) -> Libnames.qualid_of_ident id) obls in
    Extraction_plugin.Table.extraction_inline true l;
    let kind = (locality, flags.polymorphic, Decl_kinds.Definition) in
    let baseid = Id.to_string i in
    let term_info = { term_id = gr; term_ustate = uctx; term_evars = evars;
                      base_id = baseid; helpers_info = helpers; decl_kind = kind;
                      comp_obls = !compobls; user_obls = Id.Set.union !compobls !userobls } in
    let cmap = cmap (fun id -> try List.assoc id evars
                      with Not_found -> anomaly (Pp.str"Incomplete obligation to term substitution"))
    in
      hook split cmap term_info uctx
  in
  let univ_hook = Obligations.mk_univ_hook hook in
  let reduce x =
    let flags = CClosure.betaiotazeta in
    (* let flags = match comp with None -> flags *)
    (*   | Some f -> fCONST f.comp :: fCONST f.comp_proj :: flags *)
    (* in *)
    to_constr !isevar (clos_norm_flags flags (Global.env ()) !isevar (of_constr x))
  in
  let kind = (Decl_kinds.Global, flags.polymorphic, Decl_kinds.Definition) in
  let ty' = it_mkProd_or_LetIn arity sign in
    match is_recursive with
    | Some (Syntax.Guarded [id]) ->
        let ty' = it_mkProd_or_LetIn ty' [make_assum Anonymous ty'] in
        let ty' = EConstr.to_constr !isevar ty' in
	let recarg =
	  match snd id with
          | MutualOn (_, Some (loc, id))
	  | NestedOn (Some (_, Some (loc, id))) -> Some (CAst.make ~loc id)
	  | _ -> None
        in
	ignore(Obligations.add_mutual_definitions [(i, t', ty', impls, obls)]
                 (Evd.evar_universe_context !isevar) [] ~kind
                 ~reduce ~univ_hook (Obligations.IsFixpoint [recarg, CStructRec]))
    | Some (Guarded ids) ->
        let ty' = it_mkProd_or_LetIn ty' fixprots in
        let ty' = EConstr.to_constr !isevar ty' in
        ignore(Obligations.add_definition
                 ~univ_hook ~kind
                 ~implicits:impls (add_suffix i "_functional") ~term:t' ty' ~reduce
		 (Evd.evar_universe_context !isevar) obls)
    | _ ->
       let ty' = EConstr.to_constr !isevar ty' in
       ignore(Obligations.add_definition ~univ_hook ~kind
	       ~implicits:impls i ~term:t' ty'
	       ~reduce (Evd.evar_universe_context !isevar) obls)


let simplify_evars evars t =
  let rec aux t =
    match Constr.kind (EConstr.Unsafe.to_constr t) with
    | App (f, args) ->
      (match Constr.kind f with
       | Evar ev ->
         let f' = nf_evar evars (EConstr.of_constr f) in
         beta_applist evars (f', Array.map_to_list EConstr.of_constr args)
       | _ -> EConstr.map evars aux t)
    | Evar ev -> nf_evar evars t
    | _ -> EConstr.map evars aux t
  in aux t

let define_tree is_recursive fixprots flags impls status isevar env (i, sign, arity)
                comp split hook =
  let hook split =
    let _ = isevar := Evarutil.nf_evar_map_undefined !isevar in
    let () = isevar := Evd.minimize_universes !isevar in
    let split = map_split (simplify_evars !isevar) split in
    let split = define_constants flags isevar env split in
    define_tree is_recursive fixprots flags impls status isevar env (i, sign, arity) comp split hook
  in
  if Evd.has_undefined !isevar then
    solve_equations_obligations flags i isevar split hook
  else hook split

let mapping_rhs sigma s = function
  | RProgram c -> RProgram (mapping_constr sigma s c)
  | REmpty i ->
      try match nth (pi2 s) (pred i) with
      | PRel i' -> REmpty i'
      | _ -> assert false
      with Not_found -> assert false

let map_rhs f g = function
  | RProgram c -> RProgram (f c)
  | REmpty i -> REmpty (g i)
