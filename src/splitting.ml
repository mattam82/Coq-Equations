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
open Context
open Inductiveops
open Globnames
open Reductionops
open Pp
open List
open Evarutil
open Evar_kinds
open Equations_common
open Syntax

module CVars = Vars
module RelDecl = Context.Rel.Declaration
module NamedDecl = Context.Named.Declaration

open EConstr
open EConstr.Vars
open Context_map

(** Splitting trees *)

type path_component = Id.t

type path = path_component list

let path_id ?(unfold=false) path =
  match List.rev path with
  | hd :: tl ->
    List.fold_left (fun id suffix ->
        add_suffix (add_suffix id "_") (Id.to_string suffix))
      (if unfold then add_suffix hd "_unfold" else hd) tl
  | _ -> assert false

module PathOT =
  struct
    type t = path

    let path_component_compare id id' =
      Id.compare id id'

    let rec compare p p' =
      match p, p' with
      | ev :: p, ev' :: p' ->
         let c = path_component_compare ev ev' in
         if c == 0 then compare p p'
         else c
      | _ :: _, [] -> -1
      | [], _ :: _ -> 1
      | [], [] -> 0
  end

module PathMap = struct
  include Map.Make (PathOT)
end

type wf_rec = {
  wf_rec_term : constr;
  wf_rec_functional : constr option;
  wf_rec_arg : constr;
  wf_rec_rel : constr }

type struct_rec = {
  struct_rec_arg : Syntax.rec_annot;
  struct_rec_protos : int;
}

type rec_node =
  | WfRec of wf_rec
  | StructRec of struct_rec

type rec_info =
  { rec_prob : context_map;
    rec_lets : rel_context;
    rec_sign : rel_context;
    rec_arity : constr;
    rec_args : int; (* number of arguments of the recursive function *)
    rec_node : rec_node }

type splitting =
  | Compute of context_map * where_clause list * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Mapping of context_map * splitting (* Mapping Γ |- p : Γ' and splitting Γ' |- p : Δ *)
  | Refined of context_map * refined_node * splitting

and where_clause =
  { where_program : program;
    where_program_orig : program_info;
    where_program_args : constr list; (* In original context, de Bruijn only *)
    where_path : path;
    where_orig : path;
    where_context_length : int; (* Length of enclosing context, including fixpoint prototype if any *)
    where_type : types }

and refined_node =
  { refined_obj : identifier * constr * types;
    refined_rettyp : types;
    refined_arg : int * int; (* Index counting lets or not *)
    refined_path : path;
    refined_term : EConstr.t;
    refined_args : constr list;
    refined_revctx : context_map;
    refined_newprob : context_map;
    refined_newprob_to_lhs : context_map;
    refined_newty : types }

and program =
  { program_info : program_info;
    program_prob : context_map;
    program_rec : rec_info option;
    program_splitting : splitting;
    program_term : constr }

and splitting_rhs =
  | RProgram of constr
  | REmpty of int * splitting option array

let where_term w =
  applist (w.where_program.program_term, w.where_program_args)

let context_map_of_splitting : splitting -> context_map = function
  | Compute (subst, _, _, _) -> subst
  | Split (subst, _, _, _) -> subst
  | Mapping (subst, _) -> subst
  | Refined (subst, _, _) -> subst

let pr_path evd = prlist_with_sep (fun () -> str":") Id.print

let path_component_eq id id' = Id.equal id id'

let eq_path path path' =
  let rec aux path path' =
    match path, path' with
    | [], [] -> true
    | hd :: tl, hd' :: tl' -> path_component_eq hd hd' && aux tl tl'
    | _, _ -> false
  in
  aux path path'

let program_id p = p.program_info.program_id
let program_type p = program_type p.program_info
let program_sign p = p.program_info.program_sign
let program_impls p = p.program_info.program_impls
let program_rec p = p.program_info.program_rec
let program_arity p = p.program_info.program_arity

let where_id w = w.where_program.program_info.program_id

let where_context wheres =
  List.map (fun ({where_program; where_type } as w) ->
             make_def (Context.nameR (where_id w)) (Some (where_term w)) where_type) wheres

let where_program_type w =
  program_type w.where_program

let pr_program_info env sigma p =
  let open Pp in
  Names.Id.print p.program_id ++ str " : " ++
  Printer.pr_econstr_env env sigma (Syntax.program_type p) ++ str " : " ++
  Printer.pr_econstr_env env sigma (mkType p.program_sort) ++
  str " ( " ++
  (match p.program_rec with
   | Some (Structural ann) ->
    (match ann with
    | MutualOn (Some (i,_)) -> str "mutually recursive on " ++ int i
    | MutualOn None -> str "mutually recursive on ? "
    | NestedOn (Some (i,_)) -> str "nested on " ++ int i
    | NestedOn None -> str "nested on ? "
    | NestedNonRec -> str "nested but not directly recursive")
   | Some (WellFounded (c, r, info)) ->
    str "wellfounded"
   | None -> str "not recursive") ++ str")"

let pr_splitting env sigma ?(verbose=false) split =
  let verbose pp = if verbose then pp else mt () in
  let pplhs env sigma lhs = pr_pats env sigma (pi2 lhs) in
  let rec aux = function
    | Compute (lhs, wheres, ty, c) ->
      let env' = push_rel_context (pi1 lhs) env in
      let ppwhere w =
        hov 2 (str"where " ++ Id.print (where_id w) ++ str " : " ++
               (try Printer.pr_econstr_env env'  sigma w.where_type ++
                    hov 1 (str "(program type: " ++ Printer.pr_econstr_env env sigma (where_program_type w)
                    ++ str ") ") ++ pr_program_info env sigma w.where_program.program_info ++
                    str "(path: " ++ Id.print (path_id w.where_path) ++ str")" ++ spc () ++
                    str "(where_term: " ++ Printer.pr_econstr_env env sigma (where_term w) ++ str ")" ++
                    str "(arity: " ++ Printer.pr_econstr_env env sigma w.where_program.program_info.program_arity ++ str ")" ++
                    str" (where context length : " ++ int w.where_context_length ++ str ")" ++
                    str " := " ++ Pp.fnl () ++ aux w.where_program.program_splitting
                with e -> str "*raised an exception"))
      in
      let ppwheres = prlist_with_sep Pp.fnl ppwhere wheres in
      let env'' = push_rel_context (where_context wheres) env' in
      ((match c with
          | RProgram c -> pplhs env' sigma lhs ++ str" := " ++
                          Printer.pr_econstr_env env'' sigma c ++
                          (verbose (str " : " ++ Printer.pr_econstr_env env'' sigma ty))
          | REmpty (i, _) -> pplhs env' sigma lhs ++ str" :=! " ++
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
    | Refined (lhs, info, s) ->
      let (id, c, cty), ty, arg, path, scargs, revctx, newprob, newty =
        info.refined_obj, info.refined_rettyp,
        info.refined_arg, info.refined_path,
        info.refined_args,
        info.refined_revctx, info.refined_newprob, info.refined_newty
      in
      let env' = push_rel_context (pi1 lhs) env in
      hov 2 (pplhs env' sigma lhs ++ str " with " ++ Id.print id ++ str" := " ++
             Printer.pr_econstr_env env' sigma (mapping_constr sigma revctx c) ++ Pp.cut () ++
             verbose (str " : " ++ Printer.pr_econstr_env env' sigma cty ++ str" " ++
                      Printer.pr_econstr_env env' sigma ty ++ str" " ++
                      str " in " ++ pr_context_map env sigma lhs ++ spc () ++
                      str " refine term " ++ Printer.pr_econstr_env env' sigma info.refined_term ++
                      str " refine args " ++ prlist_with_sep spc (Printer.pr_econstr_env env' sigma)
                        info.refined_args ++
                      str "New problem: " ++ pr_context_map env sigma newprob ++ str " for type " ++
                      Printer.pr_econstr_env (push_rel_context (pi1 newprob) env) sigma newty ++ spc () ++
                      spc () ++ str" eliminating " ++ pr_rel_name (push_rel_context (pi1 newprob) env) (snd arg)
                      ++ spc () ++
                      str "Revctx is: " ++ pr_context_map env sigma revctx ++ spc () ++
                      str "New problem to problem substitution is: " ++
                      pr_context_map env sigma info.refined_newprob_to_lhs ++ Pp.cut ()) ++
             aux s)
  in
  try aux split with e -> str"Error pretty-printing splitting"

let pr_program env evd p =
  pr_program_info env evd p.program_info ++ fnl () ++
  pr_splitting env evd p.program_splitting

let pr_programs env evd p =
  prlist_with_sep fnl (pr_program env evd) p

let pp s = pp_with !Topfmt.deep_ft s

let ppsplit s =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  pp (pr_splitting env sigma s)

let map_wf_rec f r =
  { wf_rec_term = f r.wf_rec_term;
    wf_rec_functional = Option.map f r.wf_rec_functional;
    wf_rec_arg = f r.wf_rec_arg;
    wf_rec_rel = f r.wf_rec_rel }

let map_struct_rec f r =
  { struct_rec_arg = r.struct_rec_arg;
    struct_rec_protos = r.struct_rec_protos}

let map_rec_node f = function
  | StructRec s -> StructRec (map_struct_rec f s)
  | WfRec s -> WfRec (map_wf_rec f s)

let map_rec_info f r =
  { rec_prob = map_ctx_map f r.rec_prob;
    rec_lets = map_rel_context f r.rec_lets;
    rec_sign = map_rel_context f r.rec_sign;
    rec_arity = f r.rec_arity;
    rec_args = r.rec_args;
    rec_node = map_rec_node f r.rec_node
  }

let rec map_program f p =
  { program_info = map_program_info f p.program_info;
    program_prob = map_ctx_map f p.program_prob;
    program_splitting = map_split f p.program_splitting;
    program_rec = Option.map (map_rec_info f) p.program_rec;
    program_term = f p.program_term }

and map_where f w =
  { w with
    where_program_orig = map_program_info f w.where_program_orig;
    where_program = map_program f w.where_program;
    where_program_args = List.map f w.where_program_args;
    where_type = f w.where_type }

and map_split f split =
  let rec aux = function
    | Compute (lhs, where, ty, RProgram c) ->
      let where' = List.map (fun w -> map_where f w) where in
      let lhs' = map_ctx_map f lhs in
        Compute (lhs', where', f ty, RProgram (f c))
    | Split (lhs, y, z, cs) ->
      let lhs' = map_ctx_map f lhs in
      Split (lhs', y, f z, Array.map (Option.map aux) cs)
    | Mapping (lhs, s) ->
       let lhs' = map_ctx_map f lhs in
       Mapping (lhs', aux s)
    | Refined (lhs, info, s) ->
      let lhs' = map_ctx_map f lhs in
      let (id, c, cty) = info.refined_obj in
      let scargs = info.refined_args in
        Refined (lhs', { info with refined_obj = (id, f c, f cty);
          refined_term = f info.refined_term;
          refined_args = List.map f scargs;
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
  match p.Syntax.program_rec with
  | Some (Structural (NestedOn _)) -> true
  | Some (Structural NestedNonRec) -> true
  | _ -> false

let compute_possible_guardness_evidences sigma n fixbody fixtype =
  match n with
  | Some i -> [i]
  | None ->
      (* If recursive argument was not given by user, we try all args.
         An earlier approach was to look only for inductive arguments,
         but doing it properly involves delta-reduction, and it finally
         doesn't seem to worth the effort (except for huge mutual
         fixpoints ?) *)
    let m = Termops.nb_prod sigma fixtype in
    let ctx = fst (decompose_prod_n_assum sigma m fixtype) in
    List.map_i (fun i _ -> i) 0 ctx

let define_mutual_nested env evd get_prog progs =
  let mutual =
    List.filter (fun (p, prog) -> not (is_nested p)) progs
  in
  (* In the mutually recursive case, only the functionals have been defined,
     we build the block and its projections now *)
  let structargs = Array.map_of_list (fun (p,_) ->
                   match p.Syntax.program_rec with
                   | Some (Structural (MutualOn (Some (lid,_)))) -> Some lid
                   | _ -> None) mutual in
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
      let fixna = Array.make 1 (nameR p.program_id) in
      let fixty = Array.make 1 (Syntax.program_type p) in
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
              let decl = Context.Rel.Declaration.LocalDef (nameR (Id.of_string "H"), term, ty) in
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
        (List.init (nested - 1) (fun _ -> (Context.Rel.Declaration.LocalAssum (anonR, mkProp))))
    in
    let rec fixsubst i k acc l =
      match l with
      | (p', prog') :: rest ->
        (match p'.Syntax.program_rec with
         | Some (Structural (NestedOn idx)) ->
           let idx =
             match idx with
             | Some (idx, _) -> idx
             | None -> pred (List.length p'.program_sign)
           in
           let rest_tys = List.map (fun (p,_) -> Syntax.program_type p) rest in
           let term = one_nested k p' prog' rest_tys idx in
           fixsubst i (succ k) ((true, term) :: acc) rest

         | Some (Structural NestedNonRec) ->
           (* Non immediately recursive nested def *)
           let term =
             mkApp (get_prog prog', rel_vect 0 (List.length mutual))
           in
           fixsubst i (succ k) ((true, term) :: acc) rest
         | _ -> fixsubst (pred i) k ((false, mkRel i) :: acc) rest)
      | [] -> List.rev acc
    in
    (* aux1 ... auxn *)
    let nested = fixsubst (List.length mutual) 0 [] progs in
    let nested, mutual = List.partition (fun (x, y) -> x) nested in
    let gns = List.fold_right (fun (_, g) acc -> applist (g, acc) :: acc) nested [] in
    let nested = List.fold_left (fun acc g -> applist (g, List.rev acc) :: acc) [] gns in
    let nested = List.rev_map (Reductionops.nf_beta env !evd) nested in
    List.map snd mutual, nested
  in
  let decl =
    let blockfn (p, prog) =
      let na = nameR p.program_id in
      let ty = Syntax.program_type p in
      let sign = p.program_sign in
      let body = beta_appvect !evd (get_prog prog)
          (Array.append (Array.of_list mutualapp) (Array.of_list nestedbodies)) in
      let body = beta_appvect !evd (Vars.lift (List.length sign) body) (extended_rel_vect 0 sign) in
      let body = it_mkLambda_or_LetIn body (lift_rel_context 1 sign) in
      na, ty, body
    in
    let blockl = List.map blockfn mutual in
    let names, tys, bodies = List.split3 blockl in
    Array.of_list names, Array.of_list tys, Array.of_list bodies
  in
  let nested, mutual = List.partition (fun (p,prog) -> is_nested p) progs in
  let indexes =
    let names, tys, bodies = decl in
    let possible_indexes =
      Array.map3 (compute_possible_guardness_evidences !evd) structargs bodies tys
    in
    let tys' = Array.map EConstr.Unsafe.to_constr tys in
    let bodies' = Array.map EConstr.Unsafe.to_constr bodies in
    (* try  *)Pretyping.search_guard env (Array.to_list possible_indexes)
          (names, tys', bodies')
    (* with Not_found -> anomaly (str"Calling search_guard raised Not_found") *)
  in
  let declare_fix_fns i (p,prog) =
    let newidx = indexes.(i) in
    let p = { p with Syntax.program_rec = Some (Structural (MutualOn (Some (newidx, None)))) } in
    let fix = mkFix ((indexes, i), decl) in
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

let term_of_tree env0 isevar sort tree =
  let rec aux env evm sort = function
    | Compute ((ctx, _, _), where, ty, RProgram rhs) ->
      let compile_where ({where_program; where_type} as w)
          (env, evm, ctx) =
        let evm, c', ty' = evm, where_term w, where_type in
        (env, evm, (make_def (nameR (where_id w)) (Some c') ty' :: ctx))
      in
      let env, evm, ctx = List.fold_right compile_where where (env, evm,ctx) in
      let body = it_mkLambda_or_LetIn rhs ctx and typ = it_mkProd_or_subst env evm ty ctx in
      evm, body, typ

    | Compute ((ctx, _, _) as lhs, where, ty, REmpty (split, sp)) ->
       assert (List.is_empty where);
       let evm, bot = new_global evm (Lazy.force logic_bot) in
       let evm, prf, _ = aux env evm sort (Split (lhs, split, bot, sp)) in
       let evm, case = new_global evm (Lazy.force logic_bot_case) in
       let term = mkApp (case, [| ty; beta_appvect evm prf (extended_rel_vect 0 ctx) |]) in
       let term = it_mkLambda_or_LetIn term ctx in
       let ty = it_mkProd_or_subst env evm ty ctx in
       evm, term, ty

    | Mapping ((ctx, p, ctx'), s) ->
      let evm, term, ty = aux env evm sort s in
      let args = Array.rev_of_list (snd (constrs_of_pats ~inacc_and_hide:false env evm p)) in
      let term = it_mkLambda_or_LetIn (whd_beta evm (mkApp (term, args))) ctx in
      let ty = it_mkProd_or_subst env evm (prod_appvect evm ty args) ctx in
      evm, term, ty

    | Refined ((ctx, _, _), info, rest) ->
      let (id, _, _), ty, rarg, path, f, args, newprob, newty =
        info.refined_obj, info.refined_rettyp,
        info.refined_arg, info.refined_path,
        info.refined_term,
        info.refined_args, info.refined_newprob, info.refined_newty
      in
      let evm, sterm, sty = aux env evm sort rest in
      let term = applist (f, args) in
      let term = it_mkLambda_or_LetIn term ctx in
      let ty = it_mkProd_or_subst env evm ty ctx in
      evm, term, ty

    | Split ((ctx, _, _) as subst, rel, ty, sp) ->
      (* Produce parts of a case that will be relevant. *)
      let evm, block = Equations_common.(get_fresh evm coq_block) in
      let blockty = mkLetIn (anonR, block, Retyping.get_type_of env evm block, lift 1 ty) in
      let evd = ref evm in
      let ctx', case_ty, branches_res, nb_cuts, rev_subst, to_apply, simpl =
        Sigma_types.smart_case env evd ctx rel blockty in

      (* The next step is to use [simplify]. *)
      let simpl_step = if simpl then
          Simplify.simplify [None, Simplify.Infer_many] env evd
        else Simplify.identity env evd
      in
      let branches = Array.map2 (fun (ty, nb, csubst) next ->
        (* We get the context from the constructor arity. *)
        let new_ctx, ty = EConstr.decompose_prod_n_assum !isevar nb ty in
        let new_ctx = Namegen.name_context env !isevar new_ctx in
        let envnew = push_rel_context (new_ctx @ ctx') env in
        (* Remove the cuts and append them to the context. *)
        let cut_ctx, ty = Equations_common.splay_prod_n_assum envnew !isevar nb_cuts ty in
        let ty =
          if simpl then
            Tacred.hnf_constr (push_rel_context cut_ctx envnew) !evd ty
          else ty
        in
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
        let ((hole, c), lsubst) = simpl_step (cut_ctx @ new_ctx @ ctx', ty, sort) in
        if !debug then
          begin
            let open Feedback in
            msg_debug (str"Finished simplifying");
            msg_info(let ctx = cut_ctx @ new_ctx @ ctx' in
                     let env = push_rel_context ctx env in
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
          | Some ((next_ctx, _, glu), ev), Some s ->
            let evm, next_term, next_ty = aux env !evd glu s in
            (* Now we need to instantiate [ev] with the term [next_term]. *)
            (* We might need to permutate some rels. *)
            let next_subst = context_map_of_splitting s in
            let perm_subst = Context_map.make_permutation ~env evm subst next_subst in
            (* [next_term] starts with lambdas, so we apply it to its context. *)
            let args = Equations_common.extended_rel_vect 0 (pi3 perm_subst) in
            let next_term = beta_appvect !evd next_term args in
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
            (* let _ =
             *   let env = Evd.evar_env ev_info in
             *   Typing.type_of env evm term
             * in *)
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

      (* Remove the block lets *)
      let rec clean_block c =
        match kind !evd c with
        | LetIn (_, b, _, b') when Equations_common.is_global !evd (Lazy.force coq_block) b ->
          clean_block (subst1 b b')
        | _ -> EConstr.map !evd clean_block c
      in
      let case_ty = clean_block case_ty in
      let branches = Array.map clean_block branches in

      (* Fetch the type of the variable that we want to eliminate. *)
      let after, decl, before = split_context (pred rel) ctx in
      let rel_ty = Context.Rel.Declaration.get_type decl in
      let rel_ty = Vars.lift rel rel_ty in
      let rel_t = EConstr.mkRel rel in
      let pind, args = find_inductive env !evd rel_ty in

      (* Build the case. *)
      let case_info = Inductiveops.make_case_info env (fst pind) Sorts.Relevant Constr.RegularStyle in
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
  let evm, term, typ = aux env0 !isevar sort tree in
    isevar := evm;
    term, typ

let define_mutual_nested_csts flags env evd get_prog progs =
  let mutual, nested =
    define_mutual_nested env evd (fun prog -> get_prog evd prog) progs
  in
  let mutual =
    List.map (fun (p, prog, fix) ->
        let ty = p.Syntax.program_orig_type in
        let kn, (evm, term) =
          declare_constant p.program_id fix (Some ty) flags.polymorphic
            !evd Decl_kinds.(IsDefinition Fixpoint)
        in
        evd := evm;
        Impargs.declare_manual_implicits false (ConstRef kn) p.program_impls;
        (p, prog, term)) mutual
  in
  let args = List.rev_map (fun (p', _, term) -> term) mutual in
  let nested =
    List.map (fun (p, prog, fix) ->
        let ty = p.Syntax.program_orig_type in
        let body = Vars.substl args fix in
        let kn, (evm, e) =
          declare_constant p.program_id body (Some ty) flags.polymorphic
            !evd Decl_kinds.(IsDefinition Fixpoint) in
        evd := evm;
        Impargs.declare_manual_implicits false (ConstRef kn) p.program_impls;
        (p, prog, e)) nested in
  mutual, nested

type program_shape =
  | Single of program_info * context_map * rec_info option * splitting * constr
  | Mutual of program_info * context_map * rec_info * splitting * rel_context * constr

let make_program env evd p prob s rec_info =
  match rec_info with
  | Some r ->
    let sort = p.program_sort in
    let lhs = id_subst r.rec_lets in
    (match r.rec_node with
     | WfRec wfr ->
       let fn =
         match wfr.wf_rec_functional with
         | None -> let term, ty = term_of_tree env evd sort s in term
         | Some t -> t
       in
       let term = beta_appvect !evd wfr.wf_rec_term
           [| beta_appvect !evd fn (extended_rel_vect 0 (pi1 lhs)) |] in
       Single (p, prob, rec_info, s, it_mkLambda_or_LetIn term (pi1 lhs))
     | StructRec sr ->
       let term, ty = term_of_tree env evd sort s in
       let args = extended_rel_vect 0 r.rec_lets in
       let term = beta_appvect !evd term args in
       let before, after =
         CList.chop r.rec_args r.rec_sign
       in
       let fixdecls, after =
         CList.chop sr.struct_rec_protos after in
       let subst = List.append (List.map (fun _ -> mkProp) fixdecls) (List.rev (Array.to_list args)) in
       let program_sign = subst_rel_context 0 subst before in
       let program_arity = substnl subst r.rec_args r.rec_arity in
       let p' = { p with program_sign; program_arity } in
       let p' =
         match p.program_rec with
         | Some (Structural ann) ->
           let ann' =
             match ann with
             | NestedOn None ->
               (match s with
                | Split (ctx, var, _, _) ->
                  NestedOn (Some ((List.length (pi1 ctx)) - var - sr.struct_rec_protos, None))
                | _ -> ann)
             | _ -> ann
           in
           { p' with program_rec = Some (Structural ann') }
         | _ -> p'
       in
       Mutual (p', prob, r, s, after, (* lift 1  *)term))
  | None ->
    Single (p, prob, rec_info, s, fst (term_of_tree env evd p.program_sort s))

let update_rec_info p rec_info =
  match p.Syntax.program_rec, rec_info.rec_node with
  | Some (Structural ra), StructRec sr ->
    {rec_info with rec_node = StructRec { sr with struct_rec_arg = ra }}
  | _, _ -> rec_info

let make_programs env evd flags ?(define_constants=false) programs =
  let sterms = List.map (fun (p', prob, split, rec_info) ->
      make_program env evd p' prob split rec_info)
      programs in
  match sterms with
   [Single (p, prob, rec_info, s, term)] ->
   let term = nf_beta env !evd term in
   let term =
     if define_constants then
       let (cst, (evm, e)) =
         Equations_common.declare_constant p.program_id
           term (Some (p.Syntax.program_orig_type))
           flags.polymorphic !evd (Decl_kinds.(IsDefinition Definition))
       in
       evd := evm;
       let () = Impargs.declare_manual_implicits false (ConstRef cst) p.program_impls in
       let () = Declare.definition_message p.program_id in
       e
     else term
   in
   [{ program_info = p;
      program_prob = prob;
      program_rec = rec_info;
      program_splitting = s;
      program_term = term }]
  | _ ->
    let terms =
      List.map (function
          | Mutual (p, prob, r, s', after, term) -> (p, (prob, r, s', after, lift 1 term))
          | Single (p, _, _, _, _) -> user_err_loc (Some p.program_loc, "make_programs",
                                             str "Cannot define " ++ Names.Id.print p.program_id ++
                                             str " mutually with other programs "))
        sterms
    in
    let mutual, nested =
      if define_constants then
        if List.length terms > 1 && not (List.exists (fun (p, _) -> is_nested p) terms) then
          let terms =
            List.map (fun (p, (prob, r, s', after, term)) ->
                let term = it_mkLambda_or_LetIn term after in
                let kn, (evm, e) =
                  declare_constant (Nameops.add_suffix p.program_id "_functional") term None
                    flags.polymorphic
                    !evd Decl_kinds.(IsDefinition Fixpoint)
                in
                evd := evm; (p, (prob, r, s', after, e)))
              terms
          in
          define_mutual_nested_csts flags (Global.env ()) evd (fun evd (prob, r, s', after, term) ->
              (applist (term, extended_rel_list 0 after))) terms
        else
          define_mutual_nested_csts flags (Global.env ()) evd (fun evd (prob, r, s', after, term) ->
              (it_mkLambda_or_LetIn term after)) terms
      else
        let env =
          let (p, (prob, r, s, after, term)) = List.hd terms in
          push_rel_context after env
        in
        define_mutual_nested env evd (fun (_, _, _, _, x) -> x) terms
    in
    let make_prog (p, (prob, rec_info, s', after, _), b) =
      let term = it_mkLambda_or_LetIn b after in
      let term = nf_beta env !evd term in
      let rec_info = update_rec_info p rec_info in
      let p = { p with program_sign = p.program_sign @ after } in
      { program_info = p;
        program_prob = prob;
        program_rec = Some rec_info;
        program_splitting = s';
        program_term = term }
    in
    let mutual = List.map make_prog mutual in
    let nested = List.map make_prog nested in
    mutual @ nested

let make_single_program env evd flags p prob s rec_info =
  match make_programs env evd flags [p, prob, s, rec_info] with
  | [p] -> p
  | _ -> raise (Invalid_argument "make_single_program: more than one program")

let change_lhs s (l, p, r) =
  let open Context.Rel.Declaration in
  let l' =
    List.map
      (function LocalDef ({binder_name=Name id}, b, t) as decl ->
         (try let b' = List.assoc id s in LocalDef (nameR id, b', t)
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
    | Refined (lhs, info, rest) ->
      Refined (change_lhs s lhs, info, aux rest)
  in aux sp

let check_splitting env evd sp =
  let check_type ctx t =
    let _evm, _ty = Typing.type_of (push_rel_context ctx env) evd t in
    ()
  in
  let check_term ctx t ty =
    let _evm = Typing.check (push_rel_context ctx env) evd t ty in
    ()
  in
  let check_rhs ctx ty = function
    | RProgram c -> check_term ctx c ty
    | REmpty _ -> ()
  in
  let rec aux = function
    | Compute (lhs, where, ty, r) ->
      let _ = check_ctx_map env evd lhs in
      let ctx = check_wheres lhs where in
      let _ = check_type ctx ty in
      let _ = check_rhs ctx ty r in
      ()
    | Split (lhs, rel, ty, sp) ->
      let _ = check_ctx_map env evd lhs in
      let _r = lookup_rel rel (push_rel_context (pi1 lhs) env) in
      let _ = check_type (pi1 lhs) ty in
      Array.iter (Option.iter aux) sp
    | Mapping (lhs, sp) ->
      let _ = check_ctx_map env evd lhs in
      aux sp
    | Refined (lhs, info, rest) ->
      let _ = check_ctx_map env evd lhs in
      aux rest
  and check_wheres lhs wheres =
    let check_where ctx w =
      let () = check_program w.where_program in
      let () = check_type ctx w.where_type in
      let () = check_term ctx (applist (w.where_program.program_term, w.where_program_args)) w.where_type in
      let () = assert(w.where_context_length = List.length ctx) in
      let def = make_def (nameR (where_id w)) (Some (where_term w)) w.where_type in
      def :: ctx
    in
    let ctx = List.fold_left check_where (pi1 lhs) wheres in
    ctx
  and check_program p =
    let ty = program_type p in
    let () = check_type [] ty in
    let _ = check_ctx_map env evd p.program_prob in
    let _ =
      match p.program_rec with
      | None -> []
      | Some r ->
        let ty = it_mkLambda_or_LetIn r.rec_arity r.rec_sign in
        let () = check_type [] ty in
        match r.rec_node with
        | WfRec wf ->
          let () = check_type [] wf.wf_rec_term in
          []
        | StructRec s -> []
    in
    aux p.program_splitting
  in aux sp

let define_one_program_constants flags env0 isevar unfold p =
  let () = assert (not (Evd.has_undefined !isevar)) in
  let helpers = ref [] in
  let rec aux_program env evm p path =
    match p.program_rec with
    | Some ({ rec_node = WfRec r } as wfr) ->
      let evm, s' = aux env evm p.program_splitting in
      let isevar = ref evm in
      let env = Global.env () in
      let term, ty = term_of_tree env isevar p.program_info.program_sort s' in
      let (cst, (evm, e)) =
        Equations_common.declare_constant (path_id (Id.of_string "functional" :: path))
          term (Some ty)
          flags.polymorphic !isevar (Decl_kinds.(IsDefinition Definition))
      in
      let () = helpers := (cst, (0,0)) :: !helpers in
      let env = Global.env () in
      let evm = Evd.update_sigma_env evm env in
      evm, { p with program_splitting = s';
                    program_rec = Some { wfr with rec_node = WfRec { r with wf_rec_functional = Some e } } }

    | _ -> let evm, s = aux env evm p.program_splitting in
      evm, { p with program_splitting = s }
  and aux env evm = function
    | Compute (lhs, where, ty, RProgram rhs) ->
      let define_where ({where_program;
                         where_program_args;
                         where_type; where_path} as w)
          (env, evm, s, ctx) =
        let p = where_program in
        let program_prob = change_lhs s p.program_prob in
        let program_splitting = change_splitting s p.program_splitting in
        let evm, p' = aux_program env evm { p with program_splitting } where_path in
        let env = Global.env () in
        let evm = Evd.update_sigma_env evm env in
        let isevar = ref evm in
        let program' = make_single_program env isevar flags where_program.program_info
            program_prob p'.program_splitting p'.program_rec in
        let term' = program'.program_term in
        let (cst, (evm, e)) =
          Equations_common.declare_constant (path_id ~unfold where_path)
            term' None(* (Some (program_type where_program)) *)
            flags.polymorphic !isevar (Decl_kinds.(IsDefinition Definition))
        in
        let () = helpers := (cst, (0,0)) :: !helpers in
        let env = Global.env () in
        let evm = Evd.update_sigma_env evm env in
        let p' = { program' with program_term = e } in
        let w' = { w with where_program = p' } in
        (env, evm, (where_id w, where_term w') :: s, w' :: ctx)
      in
      let env, evm, _, where = List.fold_right define_where where (env, evm, [], []) in
      evm, Compute (lhs, where, ty, RProgram rhs)

    | Compute (lhs, where, ty, REmpty (split, sp)) ->
      evm, Compute (lhs, where, ty, REmpty (split, sp))

    | Mapping (lhs, s) ->
      let evm, s' = aux env evm s in
      evm, Mapping (lhs, s')

    | Refined ((ctx, _, _) as lhs, info, rest) ->
      let evm', rest' = aux env evm rest in
      let isevar = ref evm' in
      let env = Global.env () in
      let sort = Sorts.univ_of_sort
          (Retyping.get_sort_of (push_rel_context (pi1 lhs) env) !isevar info.refined_rettyp) in
      let t, ty = term_of_tree env isevar sort rest' in
      let (cst, (evm, e)) =
        Equations_common.declare_constant (path_id ~unfold info.refined_path)
          t (Some ty) flags.polymorphic !isevar (Decl_kinds.(IsDefinition Definition))
      in
      let () = helpers := (cst, info.refined_arg) :: !helpers in
      evm, Refined (lhs, { info with refined_term = e }, rest')

    | Split (lhs, rel, ty, sp) ->
      let evm, sp' = CArray.fold_left_map (fun evm s ->
          match s with
          | Some s -> let evm, s' = aux env evm s in evm, Some s'
          | None -> evm, None) evm sp
      in evm, Split (lhs, rel, ty, sp')
  in
  let evm, tree = aux_program env0 !isevar p [p.program_info.program_id] in
    isevar := evm; !helpers, tree

let define_program_constants flags env evd ?(unfold=false) programs =
  let helpers, programs =
    List.fold_left_map (fun helpers p ->
        let helpers', p = define_one_program_constants flags env evd unfold p in
        helpers @ helpers', p) [] programs
  in
  let env = Global.env () in
  let programs = make_programs env evd flags ~define_constants:true
      (List.map (fun p -> (p.program_info, p.program_prob, p.program_splitting, p.program_rec)) programs)
  in helpers, programs

let is_comp_obl sigma comp hole_kind =
  match comp with
  | None -> false
  | Some r ->
      match hole_kind, r with
      | ImplicitArg (ConstRef c, (n, _), _), (loc, id) ->
        is_rec_call sigma (snd r) (mkConst c)
      | _ -> false

type term_info = {
  term_id : Names.GlobRef.t;
  term_ustate : UState.t;
  base_id : string;
  decl_kind: Decl_kinds.definition_kind;
  helpers_info : (Constant.t * (int * int)) list;
  comp_obls : Constant.t list; (** The recursive call proof obligations *)
  user_obls : Id.Set.t; (** The user obligations *)
}

type compiled_program_info = {
    program_cst : Constant.t;
    program_split_info : term_info }


let is_polymorphic info = pi2 info.decl_kind

let rec decompose len c t accu =
  let open Constr in
  let open Context.Rel.Declaration in
  if len = 0 then (c, t, accu)
  else match kind c, kind t with
  | Lambda (na, u, c), Prod (_, _, t) ->
    decompose (pred len) c t (LocalAssum (na, u) :: accu)
  | LetIn (na, b, u, c), LetIn (_, _, _, t) ->
    decompose (pred len) c t (LocalDef (na, b, u) :: accu)
  | _ -> assert false

let rec shrink ctx sign c t accu =
  let open Constr in
  let open CVars in
  match ctx, sign with
  | [], [] -> (c, t, accu)
  | p :: ctx, decl :: sign ->
      if noccurn 1 c && noccurn 1 t then
        let c = subst1 mkProp c in
        let t = subst1 mkProp t in
        shrink ctx sign c t accu
      else
        let c = Term.mkLambda_or_LetIn p c in
        let t = Term.mkProd_or_LetIn p t in
        let accu = if RelDecl.is_local_assum p
                   then mkVar (NamedDecl.get_id decl) :: accu
                   else accu
    in
    shrink ctx sign c t accu
| _ -> assert false

let shrink_entry sign const =
  let open Entries in
  let typ = match const.const_entry_type with
  | None -> assert false
  | Some t -> t
  in
  (* The body has been forced by the call to [build_constant_by_tactic] *)
  (* let () = assert (Future.is_over const.const_entry_body) in *)
  let ((body, uctx), eff) = Future.force const.const_entry_body in
  let (body, typ, ctx) = decompose (List.length sign) body typ [] in
  let (body, typ, args) = shrink ctx sign body typ [] in
  let const = { const with
    const_entry_body = Future.from_val ((body, uctx), eff);
    const_entry_type = Some typ;
  } in
  (const, args)

let error_complete () =
  user_err_loc (None, "define",
                str "Equations definition is complete and requires no further proofs. " ++
                str "Use the \"Equations\" command to define it.")

let solve_equations_obligations flags recids i sigma hook =
  let kind = (Decl_kinds.Local, flags.polymorphic, Decl_kinds.(DefinitionBody Definition)) in
  let evars = Evar.Map.bindings (Evd.undefined_map sigma) in
  let env = Global.env () in
  let types =
    List.map (fun (ev, evi) ->
        if !Equations_common.debug then
          Feedback.msg_debug (str"evar type" ++ Printer.pr_econstr_env env sigma evi.Evd.evar_concl);
        let section_length = List.length (named_context env) in
        let evcontext = Evd.evar_context evi in
        let local_context, section_context =
          List.chop (List.length evcontext - section_length) evcontext
        in
        let type_ = Termops.it_mkNamedProd_or_LetIn evi.Evd.evar_concl local_context in
        let type_ = nf_beta env sigma type_ in
        env, ev, evi, local_context, type_) evars in
  (* Make goals from a copy of the evars *)
  let isevar0 = ref sigma in
  let wits = ref [] in
  let tele =
    let rec aux types evm =
      match types with
      | [] -> Proofview.TNil evm
      | (evar_env, ev, evi, local_context, type_) :: tys ->
        let evar_env = nf_env_evar !isevar0 evar_env in
        Proofview.TCons (evar_env, evm, nf_evar !isevar0 type_,
           (fun evm' wit ->
             isevar0 :=
               Evd.define ev (applist (wit, List.rev (Context.Named.to_instance mkVar local_context)))
                 !isevar0;
             wits := wit :: !wits;
             aux tys evm'))
    in aux types (Evd.from_ctx (Evd.evar_universe_context sigma))
  in
  let terminator = function
    | Proof_global.Admitted (id, gk, pe, us) ->
      user_err_loc (None, "end_obligations", str "Cannot handle admitted proof for equations")
    | Proof_global.Proved (opaque, lid, obj) ->
      if !Equations_common.debug then
        Feedback.msg_debug (str"Defining the initial evars accoding to the proofs");
      let open Decl_kinds in
      let obls = ref 1 in
      let kind = match pi3 obj.Proof_global.persistence with
        | DefinitionBody d -> IsDefinition d
        | Proof p -> IsProof p
      in
      let evd = ref sigma in
      let recobls =
        CList.map2 (fun (wit, (evar_env, ev, evi, local_context, type_)) entry ->
        let id =
          match Evd.evar_ident ev sigma with
          | Some id -> id
          | None -> let n = !obls in incr obls; add_suffix i ("_obligation_" ^ string_of_int n)
        in
        let entry, args = shrink_entry local_context entry in
        let cst = Declare.declare_constant id (Entries.DefinitionEntry entry, kind) in
        let sigma, app = Evarutil.new_global !evd (ConstRef cst) in
        evd := Evd.define ev (applist (app, List.map of_constr args)) sigma;
        cst)
        (CList.combine (List.rev !wits) types) obj.Proof_global.entries
      in
      hook recobls !evd
  in
  let do_intros =
    (* Force introductions to be able to shrink the bodies later on. *)
    List.map
      (fun (env, ev, evi, ctx, _) ->
         Tacticals.New.tclDO (List.length ctx) Tactics.intro)
      types
  in
  (* Feedback.msg_debug (str"Starting proof"); *)
  let pstate = Proof_global.(start_dependent_proof i kind tele (make_terminator terminator)) in
  let pstate = Proof_global.modify_proof
    (fun p  ->
       fst (Pfedit.solve Goal_select.SelectAll None (Proofview.tclDISPATCH do_intros) p)) pstate in
  let pstate = Proof_global.modify_proof
    (fun p  ->
       fst (Pfedit.solve (Goal_select.SelectAll) None (Tacticals.New.tclTRY !Obligations.default_tactic) p)) pstate in
  let prf = Proof_global.give_me_the_proof pstate in
  let pstate = if Proof.is_done prf then
    if flags.open_proof then error_complete ()
    else
      (Lemmas.save_pstate_proved ~pstate ~opaque:Proof_global.Transparent ~idopt:None; None)
  else if flags.open_proof then Some pstate
  else
    user_err_loc (None, "define", str"Equations definition generated subgoals that " ++
                                  str "could not be solved automatically. Use the \"Equations?\" command to" ++
                                  str " refine them interactively")
  in
  pstate

let solve_equations_obligations_program flags recids i sigma hook =
  let kind = (Decl_kinds.Local, flags.polymorphic, Decl_kinds.(Definition)) in
  let env = Global.env () in
  let sigma, term = get_fresh sigma (Equations_common.logic_top_intro) in
  let sigma, ty = get_fresh sigma (Equations_common.logic_top) in
  let sigma = Evd.minimize_universes sigma in
  let sigma, _ = Evd.nf_univ_variables sigma in
  let sigma = Evarutil.nf_evar_map_undefined sigma in
  let oblsid = Nameops.add_suffix i "_obligations" in
  let oblsinfo, (evids, cmap), term, ty =
    Obligations.eterm_obligations env oblsid sigma 0
    ~status:(Evar_kinds.Define false) term ty
  in
  let hook uctx evars locality gr =
    (* let l =
     *   Array.map_to_list (fun (id, ty, loc, s, d, tac) -> Libnames.qualid_of_ident id) obls in
     * Extraction_plugin.Table.extraction_inline true l; *)
    let sigma = Evd.merge_universe_context sigma uctx in
    let evc id = EConstr.of_constr (List.assoc_f Id.equal id evars) in
    let sigma =
      Evd.fold_undefined
      (fun ev evi sigma ->
      let args =
        Array.of_list (List.map (fun d -> EConstr.mkVar (Context.Named.Declaration.get_id d))
                       (Evd.evar_filtered_context evi)) in
      let evart = EConstr.mkEvar (ev, args) in
      let evc = cmap evc evart in
      Evd.define ev (whd_beta sigma (EConstr.of_constr evc)) sigma)
      sigma sigma
    in
    let recobls =
      List.map (fun (id, c) ->
      (* Due to shrinking, we can get lambda abstractions first *)
      let _, body = decompose_lam_assum sigma (EConstr.of_constr c) in
      let hd, _ = decompose_app sigma body in
      try fst (EConstr.destConst sigma hd)
      with Constr.DestKO -> assert false) evars
    in
    hook recobls sigma
  in
  let hook = Lemmas.mk_hook hook in
  let reduce x =
    let flags = CClosure.beta in
    to_constr sigma (clos_norm_flags flags (Global.env ()) sigma (of_constr x))
  in
  ignore (Obligations.add_definition oblsid ~term ty (Evd.evar_universe_context sigma)
          ~kind ~reduce ~hook ~opaque:false oblsinfo)

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

let unfold_entry cst = Hints.HintsUnfoldEntry [EvalConstRef cst]
let add_hint local i cst =
  Hints.add_hints ~local [Id.to_string i] (unfold_entry cst)

type 'a hook =
  | HookImmediate : (program -> term_info -> 'a) -> 'a hook
  | HookLater : (int -> program -> term_info -> unit) -> unit hook

let rec_type_ids =
  CList.map_append
    (function Some (Guarded l) -> List.map fst l
            | Some (Logical ids) -> [snd ids]
            | None -> [])

let define_programs (type a) env evd is_recursive fixprots flags ?(unfold=false) programs : a hook -> a * Proof_global.t option  =
  fun hook ->
  let call_hook recobls p helpers uctx locality gr (hook : program -> term_info -> a) : a =
    (* let l =
     *   Array.map_to_list (fun (id, ty, loc, s, d, tac) -> Libnames.qualid_of_ident id) obls in
     * Extraction_plugin.Table.extraction_inline true l; *)
    let kind = (locality, flags.polymorphic, Decl_kinds.Definition) in
    let baseid = Id.to_string (program_id p) in
    let term_info = { term_id = gr; term_ustate = uctx;
                      base_id = baseid; helpers_info = helpers; decl_kind = kind;
                      comp_obls = recobls; user_obls = Id.Set.empty } in
    hook p term_info
  in
  let all_hook hook recobls sigma =
    let sigma = Evd.minimize_universes sigma in
    let sigma = Evarutil.nf_evar_map_undefined sigma in
    let () =
      if !Equations_common.debug then
        Feedback.msg_debug (str"Defining programs, before simplify_evars " ++ pr_programs env sigma programs);
    in
    let programs = List.map (map_program (simplify_evars sigma)) programs in
    let () =
      if !Equations_common.debug then
        Feedback.msg_debug (str"Defining programs " ++ pr_programs env sigma programs);
    in
    let evd = ref sigma in
    let helpers, programs = define_program_constants flags env evd ~unfold programs in
    let sigma = !evd in
    let programs = List.map (map_program (simplify_evars sigma)) programs in
    let programs = List.map (map_program (nf_evar sigma)) programs in
    let ustate = Evd.evar_universe_context sigma in
    let () = List.iter (fun (cst, _) -> add_hint true (program_id (List.hd programs)) cst) helpers in
    hook recobls helpers ustate Decl_kinds.Global programs
  in
  let recids = rec_type_ids is_recursive in
  match hook with
  | HookImmediate f ->
    assert(not (Evd.has_undefined !evd));
    let hook recobls helpers ustate kind programs =
      let p = List.hd programs in
      let cst, _ = (destConst !evd p.program_term) in
      call_hook recobls p helpers ustate Decl_kinds.Global (ConstRef cst) f
    in
    all_hook hook [] !evd, None
  | HookLater f ->
    let hook recobls helpers ustate kind programs =
      List.iteri (fun i p ->
          let cst, _ = (destConst !evd p.program_term) in
          call_hook recobls p helpers ustate Decl_kinds.Global (ConstRef cst) (f i)) programs
    in
    if Evd.has_undefined !evd then
      if flags.open_proof then
        (), solve_equations_obligations flags recids (program_id (List.hd programs)) !evd (all_hook hook)
      else
        solve_equations_obligations_program flags recids (program_id (List.hd programs)) !evd (all_hook hook), None
    else
      if flags.open_proof then error_complete ()
      else all_hook hook [] !evd, None

let define_program_immediate env evd is_recursive fixprots flags ?(unfold=false) program =
  define_programs env evd is_recursive fixprots flags ~unfold [program]
    (HookImmediate (fun x y -> (x, y)))

let define_programs env evd is_recursive fixprots flags ?(unfold=false) programs hook =
  snd @@ define_programs env evd is_recursive fixprots flags ~unfold programs (HookLater hook)

let mapping_rhs sigma s = function
  | RProgram c -> RProgram (mapping_constr sigma s c)
  | REmpty (i, sp) ->
      try match nth (pi2 s) (pred i) with
      | PRel i' -> REmpty (i', sp)
      | _ -> assert false
      with Not_found -> assert false

let map_rhs f g = function
  | RProgram c -> RProgram (f c)
  | REmpty (i, sp) -> REmpty (g i, sp)
