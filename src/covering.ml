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
open Reductionops
open Pp
open List
open Evarutil
open Termops
open Equations_common
open Syntax
open Context_map
open Splitting

open EConstr
open EConstr.Vars   

type int_data = {
  rec_info : rec_type option;
  fixdecls : rel_context;
  flags : flags;
  intenv : Constrintern.internalization_env;
  notations : (Names.lstring * Constrexpr.constr_expr *
               Notation_term.scope_name option) list
}

exception Conflict
exception Stuck

type 'a unif_result = UnifSuccess of 'a | UnifFailure | UnifStuck
type unification_result =
  (context_map * int * constr * pat) option

let rec unify env evd flex g x y =
  if eq_constr evd x y then id_subst g
  else
    match kind evd x with
    | Rel i -> 
      if Int.Set.mem i flex then
        single_subst env evd i (PInac y) g
      else raise Stuck
    | _ ->
      match kind evd y with
      | Rel i ->
        if Int.Set.mem i flex then
          single_subst env evd i (PInac x) g
        else raise Stuck
      | _ ->
        let (c, l) = decompose_app evd x 
        and (c', l') = decompose_app evd y in
        if isConstruct evd c && isConstruct evd c' then
          if eq_constr evd c c' then
            unify_constrs env evd flex g l l'
          else raise Conflict
        else raise Stuck

and unify_constrs env evd flex g l l' = 
  match l, l' with
  | [], [] -> id_subst g
  | hd :: tl, hd' :: tl' ->
    (try
       let (d,s,_ as hdunif) = unify env evd flex g hd hd' in
       let specrest = List.map (specialize_constr evd s) in
       let tl = specrest tl and tl' = specrest tl' in
       let tlunif = unify_constrs env evd flex d tl tl' in
       compose_subst env ~sigma:evd tlunif hdunif
     with Stuck ->
       let tlunif = unify_constrs env evd flex g tl tl' in
       let spec = specialize_constr evd (pi2 tlunif) in
       let hd = spec hd and hd' = spec hd' in
       let (d, s, _) as hdunif = unify env evd flex (pi1 tlunif) hd hd' in
       compose_subst env ~sigma:evd hdunif tlunif)
  | _, _ -> raise Conflict

let flexible pats gamma =
  let (_, flex) =
    fold_left2 (fun (k,flex) pat decl ->
        match pat with
        | PInac _ -> (succ k, Int.Set.add k flex)
        | p -> (succ k, flex))
      (1, Int.Set.empty) pats gamma
  in flex

let rec accessible = function
  | PRel i -> Int.Set.singleton i
  | PCstr (c, l) -> accessibles l
  | PInac _ | PHide _ -> Int.Set.empty

and accessibles l =
  fold_left (fun acc p -> Int.Set.union acc (accessible p)) 
    Int.Set.empty l

let hidden = function PHide _ -> true | _ -> false

let rec match_pattern p c =
  match DAst.get p, c with
  | PUVar (i,gen), (PCstr _ | PRel _ | PHide _) -> [(i, gen), c], [], []
  | PUCstr (c, i, pl), PCstr ((c',u), pl') -> 
    if eq_constructor c c' then
      let params, args = List.chop i pl' in
      match_patterns pl args
    else raise Conflict
  | PUInac t, t' ->
    [], [t, t'], []
  | _, PInac t -> [], [], [p, t]
  | _, _ -> raise Stuck

and match_patterns pl l =
  match pl, l with
  | [], [] -> [], [], []
  | hd :: tl, hd' :: tl' -> 
    let l = 
      try Some (match_pattern hd hd')
      with Stuck -> None
    in
    let l' = 
      try Some (match_patterns tl tl')
      with Stuck -> None
    in
    (match l, l' with
     | Some (l, li, ri), Some (l', li', ri') -> l @ l', li @ li', ri @ ri'
     | _, _ -> raise Stuck)
  | _ -> raise Conflict

open Constrintern

let matches (p : user_pats) ((phi,p',g') : context_map) = 
  try
    let p' = filter (fun x -> not (hidden x)) (rev p') in
    UnifSuccess (match_patterns p p')
  with Conflict -> UnifFailure | Stuck -> UnifStuck

let rec match_user_pattern p c =
  match p, DAst.get c with
  | PRel i, t -> [i, t], []
  | PCstr ((c',_), pl'), PUCstr (c, i, pl) -> 
    if eq_constructor c c' then
      let params, args = List.chop i pl' in
      match_user_patterns args pl
    else raise Conflict
  | PCstr _, PUVar (n,gen) -> [], [n, p]
  | PInac _, _ -> [], []
  | _, _ -> raise Stuck

and match_user_patterns pl l =
  match pl, l with
  | [], [] -> [], []
  | hd :: tl, hd' :: tl' -> 
    let l = 
      try Some (match_user_pattern hd hd')
      with Stuck -> None
    in
    let l' = 
      try Some (match_user_patterns tl tl')
      with Stuck -> None
    in
    (match l, l' with
     | Some (l1, l2), Some (l1', l2') -> l1 @ l1', l2 @ l2'
     | _, _ -> raise Stuck)
  | _ -> raise Conflict

let matches_user ((phi,p',g') : context_map) (p : user_pats) = 
  try UnifSuccess (match_user_patterns (filter (fun x -> not (hidden x)) (rev p')) p)
  with Conflict -> UnifFailure | Stuck -> UnifStuck

let adjust_sign_arity env evars p clauses =
  let max_args =
    List.fold_left (fun acc (_, lhs, rhs) ->
        let len = List.length lhs in
        max acc len) 0 clauses
  in
  let fullty = it_mkProd_or_subst env evars p.program_arity p.program_sign in
  let evars, sign, ty =
    let rec aux evars args sign ty =
      match args with
      | 0 -> evars, sign, ty
      | n ->
        match EConstr.kind evars (whd_all env evars ty) with
        | Prod (na, t, b) -> aux evars (n - 1) (Context.Rel.Declaration.LocalAssum (na, t) :: sign) b
        | Evar e -> let evars', t = Evardefine.define_evar_as_product evars e in
          aux evars' args sign t
        | _ ->
          user_err_loc (None, "covering", str "Too many patterns in clauses for this type")
    in aux evars max_args [] fullty
  in
  let check_clause (loc, lhs, rhs) =
    if List.length lhs < max_args then user_err_loc (loc, "covering", str "This clause has not enough arguments")
    else ()
  in List.iter check_clause clauses;
  let sign = do_renamings env evars sign in
  let p = { p with program_sign = sign; program_arity = ty } in
  evars, p

let lets_of_ctx env ctx evars s =
  let envctx = push_rel_context ctx env in
  let ctxs, pats, varsubst, len, ids = 
    fold_left (fun (ctx', cs, varsubst, k, ids) (id, pat) -> 
        let c = pat_constr pat in
        match pat with
        | PRel i -> (ctx', cs, (i, id) :: varsubst, k, Id.Set.add id ids)
        | _ -> 
          let ty = e_type_of envctx evars c in
          (make_def (Name id) (Some (lift k c)) (lift k ty) :: ctx', (c :: cs),
           varsubst, succ k, Id.Set.add id ids))
      ([],[],[],0,Id.Set.empty) s
  in
  let _, _, ctx' = List.fold_right (fun decl (ids, i, ctx') ->
      let (n, b, t) = to_tuple decl in
      try ids, pred i, (make_def (Name (List.assoc i varsubst)) b t :: ctx')
      with Not_found -> 
        let id' = Namegen.next_name_away n ids in
        Id.Set.add id' ids, pred i, (make_def (Name id') b t :: ctx')) ctx (ids, List.length ctx, [])
  in pats, ctxs, ctx'

let env_of_rhs evars ctx env s lets = 
  let envctx = push_rel_context ctx env in
  let patslets, letslen = 
    fold_right (fun decl (acc, len) -> 
        let (_, b, _) = to_tuple decl in
        (lift (-len) (Option.get b) :: acc, succ len)) lets ([], 0) 
  in
  let pats, ctx, len = 
    let (pats, x, y) = lets_of_ctx env (lets @ ctx) evars 
        (List.map (fun (id, pat) -> id, lift_pat letslen pat) s) 
    in
    pats, x @ y, List.length x 
  in
  let pats = List.map (lift (-letslen)) pats @ patslets in
  ctx, envctx, len + letslen, pats

(* let _rename_prob_subst env ctx s =
 *   let _avoid = List.fold_left (fun avoid decl ->
 *       match get_name decl with
 *       | Anonymous -> avoid
 *       | Name id -> Id.Set.add id avoid) Id.Set.empty ctx
 *   in
 *   let varsubst, rest =
 *     fold_left (fun (varsubst, rest) ((id, gen), pat) ->
 *         match pat with
 *         | PRel i when gen = false -> ((i, id) :: varsubst, rest)
 *         | _ -> (varsubst, (id, pat) :: rest))
 *       ([], []) s
 *   in
 *   let ctx' =
 *     List.fold_left_i (fun i acc decl ->
 *         try let id = List.assoc i varsubst in
 *           Context.Rel.Declaration.set_name (Name id) decl :: acc
 *         with Not_found -> decl :: acc)
 *       1 [] ctx
 *   in
 *   (List.rev ctx', id_pats ctx, ctx) *)

let interp_program_body env sigma ctx impls body ty =
  match body with
  | ConstrExpr c ->
    let env = push_rel_context ctx env in
    let sigma, (c, _) =
      match ty with
      | None -> interp_constr_evars_impls env sigma ~impls c
      | Some ty -> interp_casted_constr_evars_impls env sigma ~impls c ty
    in
    sigma, c
  | Constr c ->
    let env = Environ.reset_with_named_context (Environ.named_context_val env) env in
    let env = push_rel_context ctx env in
    let subst =
      List.fold_left_i (fun i subst decl ->
          match get_name decl with
          | Name na -> (na, mkRel i) :: subst
          | _ -> subst) 1 [] ctx
    in
    let c = Vars.replace_vars subst c in
    let sigma =
      match ty with
      | None -> fst (Typing.type_of env sigma c)
      | Some ty -> Typing.check env sigma c ty
    in
    sigma, c

let interp_program_body env evars ctx intenv c ty =
 interp_program_body env evars ctx intenv c ty
  (* try  with PretypeError (env, evm, e) ->
   *   user_err_loc (dummy_loc, "interp_program_body",
   *                 str "Typechecking failed: " ++  Himsg.explain_pretype_error env evm e) *)
     (* | e ->
      *   user_err_loc (dummy_loc, "interp_program_body",
      *                 str "Unexpected exception raised while typing body: " ++
      *                 (match c with ConstrExpr c -> Ppconstr.pr_constr_expr c
      *                             | Constr c -> Printer.pr_econstr_env env evars c) ++
      *                 str " in environment " ++ Printer.pr_rel_context_of (push_rel_context ctx env) evars ++
      *                 str ":" ++
      *                 str (Printexc.to_string e)) *)

let interp_constr_in_rhs_env env evars data (ctx, envctx, liftn, subst) c ty =
  match ty with
  | None ->
    let sigma, c = interp_program_body env !evars ctx data.intenv c None in
    let c' = substnl subst 0 c in
    let sigma = Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars env sigma in
    let c' = nf_evar sigma c' in
    evars := sigma; c', Retyping.get_type_of envctx sigma c'

  | Some ty -> 
    let ty' = lift liftn ty in
    let ty' = nf_evar !evars ty' in
    let sigma, c = interp_program_body env !evars ctx data.intenv c (Some ty') in
    evars := Typeclasses.resolve_typeclasses 
        ~filter:Typeclasses.all_evars env sigma;
    let c' = nf_evar !evars (substnl subst 0 c) in
    c', nf_evar !evars (substnl subst 0 ty')

let interp_constr_in_rhs env ctx evars data ty s lets c =
  try
    let env' = env_of_rhs evars ctx env s lets in
    interp_constr_in_rhs_env env evars data env' c ty
  with Evarsolve.IllTypedInstance (env, t, u) ->
    anomaly (str"Ill-typed instance in interp_constr_in_rhs")

let unify_type env evars before id ty after =
  try
    let next_ident_away = 
      let ctxids = ref (ids_of_rel_context before @ ids_of_rel_context after) in
      let avoid = 
        fun id -> is_global id || List.mem id !ctxids
      in 
      function id -> 
        let id' = Namegen.next_ident_away_from id avoid in 
        ctxids := id' :: !ctxids; id'
    in
    let envb = push_rel_context before env in
    let ty = nf_evar !evars ty in
    let (indf, args) = find_rectype envb !evars ty in
    let ind, params = dest_ind_family indf in
    let vs = List.map (Tacred.whd_simpl envb !evars) args in
    let params = List.map (Tacred.whd_simpl envb !evars) params in
    let newty = applist (mkIndU ind, params @ vs) in
    let cstrs = Inductiveops.type_of_constructors envb (from_peuniverses !evars ind) in
    let cstrs = 
      Array.mapi (fun i ty ->
          let ty = of_constr ty in
          let ty = prod_applist !evars ty params in
          let ctx, ty = decompose_prod_assum !evars ty in
          let ctx = 
            fold_right (fun decl acc ->
                let (n, b, t) = to_tuple decl in
                match n with
                | Name id -> let id' = next_ident_away id in
                  (make_def (Name id') b t :: acc)
                | Anonymous ->
                  let x = Namegen.id_of_name_using_hdchar
                      (push_rel_context acc envb) !evars t Anonymous in
                  let id = next_ident_away x in
                  (make_def (Name id) b t :: acc))
              ctx []
          in
          let env' = push_rel_context ctx env in
          let (indf, args) = find_rectype env' !evars ty in
          let ind, params = dest_ind_family indf in
          let constr = applist (mkConstructUi (ind, succ i), params @ rels_of_tele ctx) in
          let q = inaccs_of_constrs (rels_of_tele ctx) in	
          let constrpat = PCstr (((fst ind, succ i), snd ind), 
                                 inaccs_of_constrs params @ patvars_of_tele ctx) in
          env', ctx, constr, constrpat, q, args)
        cstrs
    in
    let res = 
      Array.map (fun (env', ctxc, c, cpat, q, us) -> 
          let _beforelen = length before and ctxclen = length ctxc in
          let fullctx = ctxc @ before in
          try
            let vs' = List.map (lift ctxclen) vs in
            let p1 = lift_pats ctxclen (inaccs_of_constrs (rels_of_tele before)) in
            let flex = flexible (p1 @ q) fullctx in
            let s = unify_constrs env !evars flex fullctx vs' us in
            UnifSuccess (s, ctxclen, c, cpat)
          with Conflict -> UnifFailure | Stuck -> UnifStuck) cstrs
    in Some (newty, res)
  with Not_found -> (* not an inductive type *)
    None

let blockers curpats ((_, patcs, _) : context_map) =
  let rec pattern_blockers p c =
    match DAst.get p, c with
    | PUVar (i, _), t -> []
    | PUCstr (c, i, pl), PCstr ((c',_), pl') -> 
      if eq_constructor c c' then patterns_blockers pl (snd (List.chop i pl'))
      else []
    | PUInac _, _ -> []
    | _, PRel i -> [i]
    | _, _ -> []

  and patterns_blockers pl l =
    match pl, l with
    | [], [] -> []
    | hd :: tl, PHide _ :: tl' -> patterns_blockers pl tl'
    | hd :: tl, hd' :: tl' -> 
      (pattern_blockers hd hd') @ (patterns_blockers tl tl')
    | _ -> []

  in patterns_blockers curpats (rev patcs)

let subst_matches_constr sigma k s c = 
  let rec aux depth c =
    match kind sigma c with
    | Rel n -> 
      let k = n - depth in 
      if k >= 0 then 
        try lift depth (assoc k s)
        with Not_found -> c
      else c
    | _ -> map_with_binders sigma succ aux depth c
  in aux k c

let is_all_variables (delta, pats, gamma) =
  List.for_all (function PInac _ | PHide _ -> true | PRel _ -> true | PCstr _ -> false) pats

type 'a split_var_result =
  | Splitted of 'a
  | CannotSplit of Names.Name.t * rel_context * constr

let split_var (env,evars) var delta =
  (* delta = before; id; after |- curpats : gamma *)	    
  let before, decl, after = split_tele (pred var) delta in
  let (id, b, ty) = to_tuple decl in
  let unify = unify_type env evars before id ty after in
  let branch = function
    | UnifFailure -> None
    | UnifStuck -> assert false
    | UnifSuccess ((ctx',s,ctx), ctxlen, cstr, cstrpat) ->
      (* ctx' |- s : before ; ctxc *)
      (* ctx' |- cpat : ty *)
      let cpat = specialize !evars s cstrpat in
      let ctx' = do_renamings env !evars ctx' in
      (* ctx' |- spat : before ; id *)
      let spat =
        let ctxcsubst, beforesubst = List.chop ctxlen s in
        check_ctx_map env !evars (ctx', cpat :: beforesubst, decl :: before)
      in
      (* ctx' ; after |- safter : before ; id ; after = delta *)
      Some (lift_subst env !evars spat after)
  in
  match unify with
  | None -> None
  | Some (newty, unify) ->
    (* Some constructor's type is not refined enough to match ty *)
    if Array.exists (fun x -> x == UnifStuck) unify then
      Some (CannotSplit (id, before, newty))
    else
      let newdelta = after @ (make_def id b newty :: before) in
      Some (Splitted (var, do_renamings env !evars newdelta, Array.map branch unify))

let prove_empty env delta v =
  match split_var env v delta with
  | None -> None
  | Some (CannotSplit _) -> None
  | Some (Splitted (v, i, r)) ->
    if CArray.for_all (fun x -> x == None) r then
      Some (v, i, CArray.map (fun _ -> None) r)
    else None

let find_empty env delta =
  let r = List.map_filter (fun v -> prove_empty env delta v)
      (CList.init (List.length delta) succ)
  in match r with x :: _ -> Some x | _ -> None

(* The list of variables appearing in a list of patterns,
   ordered increasingly. *)
let variables_of_pats pats = 
  let rec aux acc pats = 
    List.fold_right (fun p acc ->
        match p with
        | PRel i -> (i, false) :: acc
        | PCstr (c, ps) -> aux [] (rev ps) @ acc
        | PInac c -> acc
        | PHide i -> (i, true) :: acc)
      pats acc
  in List.sort (fun (i, _) (i', _) -> i - i') (aux [] pats)

let pats_of_variables = List.map (fun (i, hide) ->
    if hide then PHide i else PRel i)

let lift_rel_declaration k decl = map_rel_declaration (lift k) decl

let lookup_named_i id =
  let rec aux i = function
    | decl :: _ when Id.equal id (get_id decl) -> i, decl
    | _ :: sign -> aux (succ i) sign
    | [] -> raise Not_found
  in aux 1

let instance_of_pats env evars (ctx : rel_context) (pats : (int * bool) list) =
  let subst, _, nctx = named_of_rel_context (fun () -> raise (Invalid_argument "named_of_rel_context")) ctx in
  let subst = List.map (destVar evars) subst in
  let ctx' =
    List.fold_right (fun (i, hide) ctx' ->
        let decl =
          let id = List.nth subst (pred i) in
          let i, decl = lookup_named_i id nctx in
          decl
        in decl :: ctx')
      pats []
  in
  let pats' =
    List.map_i (fun i id ->
        let i', _ = lookup_named_i id ctx' in
        CList.find_map (fun (i'', hide) ->
            if i'' == i then Some (if hide then PHide i' else PRel i')
            else None) pats)
      1 subst
  in
  let pats'' =
    List.map_i (fun i decl ->
        let (id, b, t) = to_named_tuple decl in
        let i', _ = lookup_named_i id nctx in
        CList.find_map (fun (i'', hide) ->
            if i'' == i' then Some (if hide then PHide i else PRel i)
            else None) pats)
      1 ctx'
  in fst (rel_of_named_context ctx'), pats', pats''

let push_rel_context_eos ctx env evars =
  if named_context env <> [] then
    let env' =
      push_named (make_named_def coq_end_of_section_id
                    (Some (get_efresh coq_the_end_of_the_section evars))
                    (get_efresh coq_end_of_section evars)) env
    in push_rel_context ctx env'
  else push_rel_context ctx env

let split_at_eos sigma ctx =
  List.split_when (fun decl ->
      is_lglobal coq_end_of_section (to_constr sigma (get_named_type decl))) ctx

let pr_problem p env sigma (delta, patcs, _) =
  let env' = push_rel_context delta env in
  let ctx = pr_context env sigma delta in
  Id.print p.program_id ++ str" " ++ pr_pats env' sigma patcs ++
  (if List.is_empty delta then ctx else 
     fnl () ++ str "In context: " ++ fnl () ++ ctx)

let rel_id ctx n = 
  Nameops.Name.get_id (pi1 (List.nth ctx (pred n)))

let push_named_context = List.fold_right push_named

let check_unused_clauses env cl =
  let unused = List.filter (fun (_, (_, used)) -> used = 0) cl in
  match unused with
  | ((loc, lhs, _) as cl, _) :: cls ->
    user_err_loc (loc, "covering", str "Unused clause " ++ pr_preclause env cl)
  | [] -> ()


let compute_recinfo programs =
  if List.for_all (fun p -> match p.program_rec with
      | None -> true
      | Some _ -> false) programs then None
  else if List.for_all (fun p -> match p.program_rec with
      | Some (Structural _)
      | None -> true
      | _ -> false) programs then
    let recids =
      List.map (fun p -> p.program_id,
                         match p.program_rec with
                         | Some (Structural ann) -> ann
                         | None -> NestedOn None
                         | _ -> assert false) programs
    in Some (Guarded recids)
  else begin
    if List.length programs != 1 then
      user_err_loc (None, "equations", Pp.str "Mutual well-founded definitions are not supported");
    let p = List.hd programs in
    match p.program_rec with
    | Some (WellFounded (_, _, info)) -> Some (Logical info)
    | _ -> assert false
  end

let print_recinfo programs =
  let open Pp in
  if !Equations_common.debug then
    Feedback.msg_debug (str "Programs: " ++ prlist_with_sep fnl pr_rec_info programs)

let compute_fixdecls_data env evd ?data programs =
  let protos = List.map (fun p ->
            let ty = it_mkProd_or_LetIn p.program_arity p.program_sign in
            (p.program_id, ty, p.program_impls)) programs
  in
  let names, tys, impls = List.split3 protos in
  let data =
    Constrintern.compute_internalization_env ?impls:data
    env !evd Constrintern.Recursive names tys impls
  in
  let fixprots =
    List.map (fun ty ->
        let fixproto = get_efresh coq_fix_proto evd in
        mkLetIn (Anonymous, fixproto,
                 Retyping.get_type_of env !evd fixproto, ty)) tys in
  let fixdecls =
    List.map2 (fun i fixprot -> of_tuple (Name i, None, fixprot)) names fixprots in
  data, List.rev fixdecls, fixprots

let interp_arity env evd ~poly ~is_rec ~with_evars (((loc,i),rec_annot,l,t,by),clauses as ieqs) =
  let ienv, ((env', sign), impls) = Equations_common.evd_comb1 (interp_context_evars env) evd l in
  let (arity, impls') =
    let ty = match t with
      | Some ty -> ty
      | None -> CAst.make ~loc (Constrexpr.CHole (None, Namegen.IntroAnonymous, None))
    in
    Equations_common.evd_comb1 (interp_type_evars_impls env' ?impls:None) evd ty
  in
  let impls = impls @ impls' in
  let sign = nf_rel_context_evar ( !evd) sign in
  let arity = nf_evar ( !evd) arity in
  let interp_reca k i =
    match k with
    | None | Some Mutual -> MutualOn i
    | Some Nested -> NestedOn i
  in
  let rec_annot =
    match by with
    | None ->
      (match is_rec with
       | None -> None
       | Some false ->
         if rec_annot = Some Syntax.Nested && Option.is_empty (is_recursive i [ieqs]) then
           (* Nested but not recursive in in its own body *)
           Some (Structural (NestedOn None))
         else Some (Structural (interp_reca rec_annot None))
       | Some true -> assert false)
    | Some (Structural lid) ->
      (try
         let k, _, _ = lookup_rel_id (snd lid) sign in
         Some (Structural (interp_reca rec_annot (Some (List.length sign - k, Some lid))))
       with Not_found ->
         user_err_loc (Some (fst lid), "struct_index",
                       Pp.(str"No argument named " ++ Id.print (snd lid) ++ str" found")))
    | Some (WellFounded (c, r)) -> Some (WellFounded (c, r))
  in
  let body = it_mkLambda_or_LetIn arity sign in
  let _ = if not with_evars then Pretyping.check_evars env Evd.empty !evd body in
  let () = evd := Evd.minimize_universes !evd in
  match rec_annot with
  | None ->
    { program_loc = loc;
      program_id = i;
      program_sign = sign;
      program_arity = arity;
      program_rec = None;
      program_impls = impls }
  | Some (Structural ann) ->
    { program_loc = loc;
      program_id = i;
      program_sign = sign;
      program_arity = arity;
      program_rec = Some (Structural ann);
      program_impls = impls }
  | Some (WellFounded (c, r)) ->
    let compinfo = (loc, i) in
    { program_loc = loc;
      program_id = i;
      program_sign = sign;
      program_arity = arity;
      program_rec = Some (WellFounded (c, r, compinfo));
      program_impls = impls }

let recursive_patterns env progid rec_info =
  match rec_info with
  | Some (Guarded l) ->
    let addpat (id, k) =
      match k with
      | NestedOn None when Id.equal id progid -> None
      | _ -> Some (DAst.make (PUVar (id, false)))
    in
    let structpats = List.map_filter addpat l in
    structpats
  | _ -> []

let pats_of_sign sign =
  List.rev_map (fun decl ->
      DAst.make (PUVar (Name.get_id (Context.Rel.Declaration.get_name decl), false))) sign

let wf_fix env evars sign arity term rel =
  let tele, telety = Sigma_types.telescope_of_context env evars sign in
  let envsign = push_rel_context sign env in
  let sigma, cterm = interp_constr_evars envsign !evars term in
  let carrier =
    let ty = Retyping.get_type_of envsign sigma cterm in
    let ty = nf_all envsign sigma ty in
    if noccur_between sigma 1 (length sign) ty then
      lift (- length sign) ty
    else
      user_err_loc (Constrexpr_ops.constr_loc term, "wf_fix",
                    str"The carrier type of the recursion order cannot depend on the arguments")
  in
  let cterm = it_mkLambda_or_LetIn cterm sign in
  let concl = it_mkLambda_or_LetIn arity sign in
  let sigma, crel =
    let relty =
      (mkProd (Anonymous, carrier, mkProd (Anonymous, lift 1 carrier, mkProp)))
    in
    match rel with
    | Some rel -> interp_casted_constr_evars env sigma rel relty
    | None -> new_evar env sigma relty
  in
  let () = evars := sigma in
  let crel = mkapp env evars logic_tele_measure [| tele; carrier; cterm; crel |] in
  let wfty = mkapp env evars logic_wellfounded_class [| telety; crel |] in
  let sigma, wf = new_evar env !evars wfty in
  let sigma = Typeclasses.resolve_typeclasses env sigma in
  let () = evars := sigma in
  let fix = mkapp env evars logic_tele_fix [| tele; crel; wf; concl |] in
  let sigma, fixty = Typing.type_of env !evars fix in
  let () = evars := sigma in
  let reds =
    let flags = CClosure.betaiotazeta in
    let csts =
      let ts = TransparentState.empty in
      let cst = Names.Cpred.add (Projection.constant (Lazy.force coq_pr1)) Names.Cpred.empty in
      let cst = Names.Cpred.add (Projection.constant (Lazy.force coq_pr2)) cst in
      let add_ts cst t = Names.Cpred.add (Globnames.destConstRef (Lazy.force t)) cst in
      let tr_cst = List.fold_left add_ts cst
          [logic_tele_interp;
           logic_tele_measure;
           logic_tele_fix;
           logic_tele_MR;
           logic_tele_fix_functional_type;
           logic_tele_type_app;
           logic_tele_forall_type_app;
           logic_tele_forall_uncurry;
           logic_tele_forall;
           logic_tele_forall_pack;
           logic_tele_forall_unpack]
      in { ts with TransparentState.tr_cst }
    in CClosure.RedFlags.red_add_transparent flags csts
  in
  let norm env =
    let infos = Cbv.create_cbv_infos reds env !evars in
    Cbv.cbv_norm infos
  in
  let fixty = norm env fixty in
  (* let prc = Printer.pr_econstr_env env !evars in *)
  (* Feedback.msg_debug (str" fix ty" ++ prc fixty); *)
  let functional_type, concl =
    match kind !evars fixty with
    | Prod (na, fnty, concl) ->
      let concl = subst1 mkProp concl in
      fnty, concl
    | _ -> assert false
  in
  let fix = norm env fix in
  let functional_type, full_functional_type =
    let ctx, rest = Reductionops.splay_prod_n env !evars (Context.Rel.nhyps sign) functional_type in
    match kind !evars (whd_all (push_rel_context ctx env) !evars rest) with
    | Prod (na, b, concl) ->
      let ctx', rest = Reductionops.splay_prod_assum (push_rel_context ctx env) !evars b in
      let infos = Cbv.create_cbv_infos reds (push_rel_context ctx env) !evars in
      let norm = Cbv.cbv_norm infos in
      let fn_type = it_mkProd_or_LetIn rest ctx' in
      let fn_type = norm fn_type in
      fn_type, it_mkProd_or_LetIn (mkProd (na, fn_type, concl)) ctx
    | _ -> assert false
  in
  (* let sigma, functional_evar = new_evar env !evars functional_type in *)
  (* let fix = mkApp (fix, [| functional_evar |]) in *)
  (* Feedback.msg_debug (str" rec definition" ++
   *                     str" fix: " ++ prc fix ++
   *                     str " functional type : " ++ prc functional_type ++
   *                     str " full functional type : " ++ prc full_functional_type ++
   *                     str " conclusion type : " ++ prc concl); *)
  functional_type, full_functional_type, fix

let compute_rec_data env evars data lets p =
  match p.program_rec with
  | Some (Structural ann) ->
    let reclen, sign =
      match ann with
      | NestedOn None -> (* Actually the definition is not self-recursive *)
        let fixdecls =
          List.filter (fun decl ->
              let na = Context.Rel.Declaration.get_name decl in
              let id = Nameops.Name.get_id na in
              not (Id.equal id p.program_id)) data.fixdecls
        in
        let len = length fixdecls in
        len, lift_rel_context len p.program_sign @ fixdecls
      | _ ->
        let len = length data.fixdecls in
        len, lift_rel_context len p.program_sign @ data.fixdecls
    in
    let extpats = recursive_patterns env p.program_id data.rec_info in
    let sign, ctxpats =
      let sign = sign @ lets in
      let extpats' = pats_of_sign lets in
      sign, extpats' @ extpats
    in
    let rec_node =
      let info =
        { struct_rec_arg = ann;
          struct_rec_intro = List.length p.program_sign;
          struct_rec_protos = List.length extpats }
      in StructRec info
    in
    let p =
      { p with program_sign = sign;
               program_arity = liftn reclen (succ (length p.program_sign)) p.program_arity }
    in
    p, id_subst p.program_sign, ctxpats, (Some rec_node)

  | Some (WellFounded (term, rel, _)) ->
    let envlets = push_rel_context lets env in
    let functional_type, _full_functional_type, fix = wf_fix envlets evars p.program_sign p.program_arity term rel in
    let decl = make_def (Name p.program_id) None functional_type in
    let ctxpats = pats_of_sign lets in
    let wf_rec_intro = List.length p.program_sign in
    let p = { p with program_sign = p.program_sign @ lets } in
    let lhs = decl :: p.program_sign in
    let pats = PHide 1 :: lift_pats 1 (id_pats p.program_sign) in
    let prob = (lhs, pats, lhs) in
    let rec_node =
      (* id_subst lets *)
      { wf_rec_term = fix;
        wf_rec_arg = term;
        wf_rec_rel = rel;
        wf_rec_intro = wf_rec_intro;
        wf_rec_newprob = prob }
    in
    let p = { p with program_arity = lift 1 p.program_arity } in
    p, prob, ctxpats, Some (WfRec rec_node)

  | _ ->
    let p = { p with program_sign = p.program_sign @ lets } in
    p, id_subst p.program_sign, pats_of_sign lets, None

let rec covering_aux env evars p data prev (clauses : (pre_clause * (int * int)) list) path
    (ctx,pats,ctx' as prob) extpats lets ty =
  if !Equations_common.debug then
    Feedback.msg_debug Pp.(str"Launching covering on "++ pr_preclauses env (List.map fst clauses) ++
                           str " with problem " ++ pr_problem p env !evars prob ++
                           str " extpats " ++ pr_user_pats env extpats);
  match clauses with
  | ((loc, lhs, rhs), (idx, cnt) as clause) :: clauses' ->
    if !Equations_common.debug then
      Feedback.msg_debug (str "Matching " ++ pr_user_pats env (extpats @ lhs) ++ str " with " ++
                          pr_problem p env !evars prob);
    (match matches (extpats @ lhs) prob with
     | UnifSuccess s ->
       if !Equations_common.debug then Feedback.msg_debug (str "succeeded");
       (* let renaming = rename_prob_subst env ctx (pi1 s) in *)
       let s = (List.map (fun ((x, gen), y) -> x, y) (pi1 s), pi2 s, pi3 s) in
       (* let prob = compose_subst env ~sigma:!evars renaming prob in *)
       let clauseid = Id.of_string ("clause_" ^ string_of_int idx ^ (if cnt = 0 then "" else "_" ^ string_of_int cnt)) in
       let interp =
         interp_clause env evars p data prev clauses' ((clauseid, false) :: path) prob
           extpats lets ty ((loc,lhs,rhs), cnt) s
       in
       (match interp with
        | None ->
           user_err_loc
            (dummy_loc, "split_var",
             str"Clause " ++ pr_preclause env (loc, lhs, rhs) ++ str" matched but its interpretation failed")
        | Some s -> Some (List.rev prev @ ((loc,lhs,rhs),(idx, cnt+1)) :: clauses', s))

     | UnifFailure ->
       if !Equations_common.debug then Feedback.msg_debug (str "failed");
       covering_aux env evars p data (clause :: prev) clauses' path prob extpats lets ty

     | UnifStuck -> 
       if !Equations_common.debug then Feedback.msg_debug (str "got stuck");
       let blocks = blockers (extpats @ lhs) prob in
       let try_split acc var =
         match acc with
         | None
         | Some (CannotSplit _) ->
           (match split_var (env,evars) var (pi1 prob) with
            | Some (Splitted (var, newctx, s)) ->
              let prob' = (newctx, pats, ctx') in
              let coverrec clauses s =
                covering_aux env evars p data []
                  clauses path 
                  (compose_subst env ~sigma:!evars s prob')
                  extpats
                  (specialize_rel_context !evars (pi2 s) lets)
                  (specialize_constr !evars (pi2 s) ty)
              in
              (try
                 let rec_call clauses x =
                   match x with
                   | Some s ->
                     (match coverrec clauses s with
                      | None -> raise Not_found
                      | Some (clauses, s) -> clauses, Some s)
                   | None -> clauses, None
                 in
                 let clauses, rest = Array.fold_left_map rec_call (List.rev prev @ clauses) s in
                 Some (Splitted (clauses, Split (prob', var, ty, rest)))
               with Not_found -> acc)
            | Some (CannotSplit _) as x ->
              begin match acc with
                | None -> x
                | _ -> acc
              end
            | None -> None)
         | _ -> acc
       in
       let result = fold_left try_split None blocks in
       (match result with
       | Some (Splitted (clauses, s)) -> Some (clauses, s)
       | Some (CannotSplit (id, before, newty)) ->
           user_err_loc
            (loc, "split_var",
             str"Unable to split variable " ++ Name.print id ++ str" of (reduced) type " ++
             Printer.pr_econstr_env (push_rel_context before env) !evars newty ++ str" to match a user pattern."
             ++ fnl () ++ str "Maybe unification is stuck as it cannot refine a context/section variable.")
       | None -> None))
           (* user_err_loc
            *  (loc, "split_var",
            *   str"Unable to split any variable to match the user patterns: " ++ pr_preclause env (loc, lhs, rhs) ++
            *   fnl () ++ str "Maybe unification is stuck as it cannot refine a context/section variable."))) *)
  | [] -> (* Every clause failed for the problem, it's either uninhabited or
             the clauses are not exhaustive *)
    match find_empty (env,evars) (pi1 prob) with
    | Some (i, ctx, s) ->
      Some (List.rev prev @ clauses, (* Split (prob, i, ty, s)) *)
            Compute (prob, [], ty, REmpty (i, s)))
    | None ->
      user_err_loc (Some p.program_loc, "deppat",
        (str "Non-exhaustive pattern-matching, no clause found for:" ++ fnl () ++
         pr_problem p env !evars prob))

and interp_clause env evars p data prev clauses' path (ctx,pats,ctx' as prob)
    extpats lets ty
    ((loc,lhs,rhs), used) (s, uinnacs, innacs) =
  let env' = push_rel_context_eos ctx env evars in
  let get_var loc i s =
    match assoc i s with
    | PRel i -> i
    | _ -> user_err_loc (Some loc, "equations", str"Unbound variable " ++ Id.print i)
  in
  let () = (* Check innaccessibles are correct *)
    let check_uinnac (user, t) =
      let userc, usercty = interp_constr_in_rhs env ctx evars data None s lets (ConstrExpr user) in
      match t with
      | PInac t ->
        begin match Reductionops.infer_conv env' !evars userc t with
          | Some evars' -> evars := evars'
          | None ->
            CErrors.user_err ?loc:(Constrexpr_ops.constr_loc user) ~hdr:"covering"
              (str "Incompatible innaccessible pattern " ++
               Printer.pr_econstr_env env' !evars userc ++
               spc () ++ str "should be convertible to " ++
               Printer.pr_econstr_env env' !evars t)
        end
      | _ ->
        let t = pat_constr t in
        CErrors.user_err ?loc:(Constrexpr_ops.constr_loc user) ~hdr:"covering"
          (str "Pattern " ++
           Printer.pr_econstr_env env' !evars userc ++
           spc () ++ str "is not inaccessible, but should refine pattern " ++
           Printer.pr_econstr_env env' !evars t)
    in
    let check_innac (user, forced) =
      DAst.with_loc_val (fun ?loc user ->
      (* Allow patterns not written by the user to be forced innaccessible silently *)
      if Option.is_empty loc then ()
      else
        match user with
        | PUVar (i, true) ->
          (* If the pattern comes from a wildcard, allow forcing innaccessibles too *)
          ()
        | _ ->
          let ctx, envctx, liftn, subst = env_of_rhs evars ctx env s lets in
          let forcedsubst = substnl subst 0 forced in
          CErrors.user_err ?loc ~hdr:"covering"
            (str "This pattern must be innaccessible and equal to " ++
             Printer.pr_econstr_env (push_rel_context ctx env) !evars forcedsubst)) user
    in
    List.iter check_uinnac uinnacs;
    List.iter check_innac innacs
  in
  match rhs with
  | Program (c,w) -> 
    let data,envctx,lets,env',coverings,lift,subst =
      interp_wheres env ctx evars path data s lets w in
    let c', ty' = 
      interp_constr_in_rhs_env env evars data
        (lets, envctx, lift, subst) c (Some (Vars.lift (List.length w) ty)) in
    (* Compute the coverings using type information from the term using
       the where clauses *)
    let coverings = List.map (fun c -> Lazy.force c) coverings in
    let res = Compute (prob, coverings, ty', RProgram c') in
    Some res

  | Empty (loc,i) ->
    (match prove_empty (env, evars) (pi1 prob) (get_var loc i s) with
     | None -> user_err_loc (Some loc, "covering", str"Cannot show that " ++ Id.print i ++ str"'s type is empty")
     | Some (i, ctx, s) ->
       Some (Compute (prob, [], ty, REmpty (i, s))))

  | Refine (c, cls) -> 
    (* The refined term and its type *)
    let cconstr, cty = interp_constr_in_rhs env ctx evars data None s lets (ConstrExpr c) in

    let vars = variables_of_pats pats in
    let newctx, pats', pats'' = instance_of_pats env !evars ctx vars in
    (* revctx is a variable substitution from a reordered context to the
       current context. Needed for ?? *)
    let revctx = check_ctx_map env !evars (newctx, pats', ctx) in
    let idref = Namegen.next_ident_away (Id.of_string "refine") (Id.Set.of_list (ids_of_rel_context newctx)) in
    let decl = make_assum (Name idref) (mapping_constr !evars revctx cty) in
    let extnewctx = decl :: newctx in
    (* cmap : Δ -> ctx, cty,
       strinv associates to indexes in the strenghtened context to
       variables in the original context.
    *)
    let refterm = lift 1 (mapping_constr !evars revctx cconstr) in
    let cmap, strinv = strengthen ~full:false ~abstract:true env !evars extnewctx 1 refterm in
    let (idx_of_refined, _) = List.find (fun (i, j) -> j = 1) strinv in
    let newprob_to_lhs =
      let inst_refctx = set_in_ctx idx_of_refined (mapping_constr !evars cmap refterm) (pi1 cmap) in
      let str_to_new =
        inst_refctx, (specialize_pats !evars (pi2 cmap) (lift_pats 1 pats')), newctx
      in
      compose_subst env ~sigma:!evars str_to_new revctx
    in	
    let newprob = 
      let ctx = pi1 cmap in
      let pats = 
        rev_map (fun c -> 
            let idx = destRel !evars c in
            (* find out if idx in ctx should be hidden depending
               on its use in newprob_to_lhs *)
            if List.exists (function PHide idx' -> idx == idx' | _ -> false)
                (pi2 newprob_to_lhs) then
              PHide idx
            else PRel idx) (rels_of_tele ctx) in
      (ctx, pats, ctx)
    in
    let newty =
      let env' = push_rel_context extnewctx env in
      subst_term !evars refterm
        (Tacred.simpl env'
           !evars (lift 1 (mapping_constr !evars revctx ty)))
    in
    let newty = mapping_constr !evars cmap newty in
    (* The new problem forces a reordering of patterns under the refinement
       to make them match up to the context map. *)
    let sortinv = List.sort (fun (i, _) (i', _) -> i' - i) strinv in
    let vars' = List.rev_map snd sortinv in
    let rec cls' n cls =
      let next_unknown =
        let str = Id.of_string "unknown" in
        let i = ref (-1) in fun () ->
          incr i; add_suffix str (string_of_int !i)
      in
      List.map_filter (fun (loc, lhs, rhs) ->
        let oldpats, newpats = List.chop (List.length lhs - n) lhs in
        let newref, nextrefs =
          match newpats with hd :: tl -> hd, tl | [] -> assert false
        in
        match matches_user prob (extpats @ oldpats) with
        | UnifSuccess (s, alias) ->
          (* A substitution from the problem variables to user patterns and
             from user pattern variables to patterns instantiating problem variables. *)
          let newlhs =
            List.map_filter
              (fun i ->
                 if i == 1 then Some newref
                 else
                 if List.exists (fun (i', b) -> i' == pred i && b) vars then None
                 else
                   try Some (DAst.make (List.assoc (pred i) s))
                   with Not_found -> (* The problem is more refined than the user vars*)
                     Some (DAst.make (PUVar (next_unknown (), true))))
              vars'
          in
          let newrhs = match rhs with
            | Refine (c, cls) -> Refine (c, cls' (succ n) cls)
            | _ -> rhs
          in
          Some (loc, rev newlhs @ nextrefs, newrhs)
        | _ ->
          CErrors.user_err ~hdr:"covering" ?loc
            (str "Non-matching clause in with subprogram:" ++ fnl () ++ int n ++
             str"Problem is " ++ spc () ++ pr_context_map env !evars prob ++ fnl () ++
             str"And the user patterns are: " ++ spc () ++
             pr_user_pats env lhs)) cls
    in
    let cls' = cls' 1 cls in
    let strength_app, refarg =
      let sortinv = List.sort (fun (i, _) (i', _) -> i' - i) strinv in
      let argref = ref 0 in
      let args = 
        List.map (fun (i, j) (* i variable in strengthened context, 
                                j variable in the original one *) -> 
                   if j == 1 then (argref := (List.length strinv - i); 
                                   cconstr)
                   else let (var, _) = List.nth vars (pred (pred j)) in
                     mkRel var) sortinv
      in args, !argref
    in
    (* Don't forget section variables. *)
    let secvars =
      let named_context = Environ.named_context env in
      List.map (fun decl ->
          let id = Context.Named.Declaration.get_id decl in
          mkVar id) named_context
    in
    let _secvars = Array.of_list secvars in
    let _evar = new_untyped_evar () in
    let path' = (idref, false) :: path in
    let lets' =
      let letslen = length lets in
      let _, ctxs, _ = lets_of_ctx env ctx evars s in
      let newlets = (lift_rel_context (succ letslen) ctxs)
                    @ (lift_rel_context 1 lets)
      in specialize_rel_context !evars (pi2 cmap) newlets
    in
    let clauses' = List.mapi (fun i x -> x, (succ i, 0)) cls' in
    match covering_aux env evars p data [] clauses' path' newprob [] lets' newty with
    | None ->
      errorlabstrm "deppat"
        (str "Unable to build a covering for with subprogram:" ++ fnl () ++
         pr_problem p env !evars newprob ++ fnl () ++
         str "And clauses: " ++ pr_preclauses env cls')
    | Some (clauses, s) ->
      let () = check_unused_clauses env clauses in
      let term, _ = term_of_tree evars env s in
      let info =
        { refined_obj = (idref, cconstr, cty);
          refined_rettyp = ty;
          refined_arg = refarg;
          refined_path = path';
          refined_term = term;
          refined_args = strength_app;
          (* refined_args = (mkEvar (evar, secvars), strength_app); *)
          refined_revctx = revctx;
          refined_newprob = newprob;
          refined_newprob_to_lhs = newprob_to_lhs;
          refined_newty = newty }
      in  Some (Refined (prob, info, s))
(* else  *)
(*   anomaly ~label:"covering" *)
(*     (str "Found overlapping clauses:" ++ fnl () ++ pr_clauses env (map fst prevmatch) ++ *)
(*        spc () ++ str"refining" ++ spc () ++ pr_context_map env prob) *)

and interp_wheres env0 ctx evars path data s lets (w : (pre_prototype * pre_equation list) list) =
  let (ctx, envctx, liftn, subst) = env_of_rhs evars ctx env0 s lets in
  let aux (data,lets,nlets,coverings,env)
      (((loc,id),nested,b,t,reca),clauses as eqs) =

    let is_rec = is_recursive id [eqs] in
    let p = interp_arity env evars ~poly:false ~is_rec ~with_evars:true eqs in
    let clauses = Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation env data.intenv) data.notations;
      List.map (interp_eqn env p) clauses) ()
    in
    let sigma, p = adjust_sign_arity env !evars p clauses in
    let () = evars := sigma in

    let pre_type = Syntax.program_type p in
    let fixdecls = [Context.Rel.Declaration.LocalAssum (Name id, pre_type)] in
    let p, problem, extpats, rec_node =
      compute_rec_data env evars {data with rec_info = compute_recinfo [p];
                                      fixdecls = fixdecls} lets p in
    let intenv = Constrintern.compute_internalization_env ~impls:data.intenv
        env !evars Constrintern.Recursive [id] [pre_type] [p.program_impls]
    in
    let data = { data with intenv; } in
    let path = (id, false) :: path in
    let where_args = extended_rel_list 0 lets in
    let w' program =
      {where_program = program; where_program_orig = p;
       where_program_args = where_args;
       where_path = path;
       where_orig = path;
       where_context_length = List.length extpats;
       where_type = pre_type }
    in
    let program, term =
      match t with
      | Some ty (* non-delayed where clause, compute term right away *) ->
        let splitting = covering env0 evars p data clauses path problem extpats p.program_arity in
        let program = make_program evars env0 lets p problem splitting rec_node in
        Lazy.from_val (w' program), program.program_term
      | None ->
        let relty = Syntax.program_type p in
        let src = (Some loc, Evar_kinds.(QuestionMark {
            qm_obligation=Define false;
            qm_name=Name id;
            qm_record_field=None;
          })) in
        let sigma, term = Equations_common.new_evar env0 !evars ~src relty in
        let () = evars := sigma in
        let ev = destEvar !evars term in
        let cover () =
          let splitting = covering env0 evars p data clauses path problem extpats p.program_arity in
          let program = make_program evars env0 lets p problem splitting rec_node in
          evars := Evd.define (fst ev) program.program_term !evars; w' program
        in
        Lazy.from_fun cover, term
    in
    let decl = make_def (Name id) (Some (applistc term where_args)) pre_type in
    (data, decl :: lets, succ nlets, program :: coverings,
     push_rel decl envctx)
  in
  let (data, lets, nlets, coverings, envctx') =
    List.fold_left aux (data, ctx, 0, [], push_rel_context ctx env0) w
  in (data, envctx, lets, push_rel_context ctx env0, coverings, liftn, subst)

and covering ?(check_unused=true) env evars p data (clauses : pre_clause list)
    path prob extpats ty =
  let clauses = (List.mapi (fun i x -> (x,(succ i,0))) clauses) in
  (*TODO eta-expand clauses or type *)
  match covering_aux env evars p data [] clauses path prob extpats [] ty with
  | Some (clauses, cov) ->
    let () = if check_unused then check_unused_clauses env clauses in
    cov
  | None ->
    errorlabstrm "deppat"
      (str "Unable to build a covering for:" ++ fnl () ++
       pr_problem p env !evars prob)

let program_covering env evd data p clauses =
  let clauses = Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation env data.intenv) data.notations;
      List.map (interp_eqn env p) clauses) ()
  in
  let sigma, p = adjust_sign_arity env !evd p clauses in
  let () = evd := sigma in
  let p', prob, extpats, rec_node = compute_rec_data env evd data [] p in
  let _arity = nf_evar !evd p.program_arity in
  let splitting =
    covering env evd p data clauses [p.program_id, false] prob extpats p'.program_arity
  in
  make_program evd env [] p' prob splitting rec_node

let coverings env evd data programs equations =
  List.map2 (program_covering env evd data) programs equations
