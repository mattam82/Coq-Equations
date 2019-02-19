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
open Reductionops
open Pp
open List
open Equations_common
open EConstr
open EConstr.Vars

(** Abstract syntax for dependent pattern-matching. *)

type peconstructor = Names.constructor peuniverses

type pat =
  | PRel of int
  | PCstr of peconstructor * pat list
  | PInac of constr
  | PHide of int

type context_map = rel_context * pat list * rel_context


let type_of_refresh env evdref c =
  let ty = Retyping.get_type_of env !evdref c in
  let sigma, ty =
    Evarsolve.refresh_universes ~status:Evd.univ_flexible ~onlyalg:true (Some false)
      env !evdref ty
  in evdref := sigma; ty

let mkInac env evdref c =
  mkApp (e_new_global evdref (Lazy.force coq_inacc),
         [| type_of_refresh env evdref c ; c |])

let mkHide env evdref c =
  mkApp (e_new_global evdref (Lazy.force coq_hide),
         [| type_of_refresh env evdref c ; c |])

let rec pat_constr = function
  | PRel i -> mkRel i
  | PCstr (c, p) ->
    let c' = mkConstructU c in
    mkApp (c', Array.of_list (List.map pat_constr p))
  | PInac r -> r
  | PHide c -> mkRel c

let rec constr_of_pat inacc_and_hide env evdref = function
  | PRel i -> mkRel i
  | PCstr (c, p) ->
    let c' = mkConstructU c in
    mkApp (c', Array.of_list (constrs_of_pats inacc_and_hide env evdref p))
  | PInac r ->
    if inacc_and_hide then try mkInac env evdref r with _ -> r else r
  | PHide i -> if inacc_and_hide then mkHide env evdref (mkRel i) else mkRel i

and constrs_of_pats inacc_and_hide env evdref l =
  List.map (constr_of_pat inacc_and_hide env evdref) l

let constr_of_pat ?(inacc_and_hide=true) env sigma p =
  let evdref = ref sigma in
  let pc = constr_of_pat inacc_and_hide env evdref p in
  !evdref, pc

let constrs_of_pats ?(inacc_and_hide=true) env sigma ps =
  let evdref = ref sigma in
  let pcs = constrs_of_pats inacc_and_hide env evdref ps in
  !evdref, pcs

let rec pat_vars = function
  | PRel i -> Int.Set.singleton i
  | PCstr (c, p) -> pats_vars p
  | PInac _ -> Int.Set.empty
  | PHide _ -> Int.Set.empty

and pats_vars l =
  fold_left (fun vars p ->
      let pvars = pat_vars p in
      let inter = Int.Set.inter pvars vars in
      if Int.Set.is_empty inter then
        Int.Set.union pvars vars
      else error ("Non-linear pattern: variable " ^
                  string_of_int (Int.Set.choose inter) ^ " appears twice"))
    Int.Set.empty l

let inaccs_of_constrs l = List.map (fun x -> PInac x) l

let rec pats_of_constrs sigma l = List.map (pat_of_constr sigma) l
and pat_of_constr sigma c =
  match kind sigma c with
  | Rel i -> PRel i
  | App (f, [| a ; c |]) when is_global sigma (Lazy.force coq_inacc) f ->
    PInac c
  | App (f, [| a ; c |]) when is_global sigma (Lazy.force coq_hide) f ->
    PHide (destRel sigma c)
  | App (f, args) when isConstruct sigma f ->
    let ((ind,_),_ as cstr) = destConstruct sigma f in
    let nparams = Inductiveops.inductive_nparams ind in
    let params, args = Array.chop nparams args in
    PCstr (cstr, inaccs_of_constrs (Array.to_list params) @
                 pats_of_constrs sigma (Array.to_list args))
  | Construct f -> PCstr (f, [])
  | _ -> PInac c


let rec pat_to_user_pat ?(avoid = ref Id.Set.empty) ?loc ctx = function
  | PRel i ->
    let decl = List.nth ctx (pred i) in
    let name = Context.Rel.Declaration.get_name decl in
    let id = Namegen.next_name_away name !avoid in
    avoid := Id.Set.add id !avoid;
    Some (DAst.make ?loc (Syntax.PUVar (id, false)))
  | PCstr (((ind, _ as cstr), _), pats) ->
    let n = Inductiveops.inductive_nparams ind in
    let _, pats = List.chop n pats in
    Some (DAst.make ?loc (Syntax.PUCstr (cstr, n, pats_to_lhs ~avoid ?loc ctx pats)))
  | PInac c ->
    let id = Namegen.next_ident_away (Id.of_string "wildcard") !avoid in
    avoid := Id.Set.add id !avoid;
    Some (DAst.make ?loc (Syntax.PUVar (id, true)))
  | PHide i -> None
and pats_to_lhs ?(avoid = ref Id.Set.empty) ?loc ctx pats =
  List.map_filter (pat_to_user_pat ~avoid ?loc ctx) pats

let context_map_to_lhs ?(avoid = Id.Set.empty) ?loc (ctx, pats, _) =
  let avoid = ref avoid in
  List.rev (pats_to_lhs ~avoid ?loc ctx pats)

let do_renamings env sigma ctx =
  let avoid, ctx' =
    List.fold_right (fun decl (ids, acc) ->
        let (n, b, t) = to_tuple decl in
        match n with
        | Name id ->
          let id' = Namegen.next_ident_away id ids in
          let decl' = make_def (Name id') b t in
          (Id.Set.add id' ids, decl' :: acc)
        | Anonymous ->
          let id' = Namegen.id_of_name_using_hdchar (push_rel_context acc env) sigma t n in
          let id' = Namegen.next_ident_away id' ids in
          let decl' = make_def (Name id') b t in
          (Id.Set.add id' ids, decl' :: acc))
      ctx (Id.Set.empty, [])
  in ctx'

(** Pretty-printing *)

let pr_constr_pat env sigma c =
  Printer.pr_econstr_env env sigma c
  (* match kind sigma c with
   * | App _ -> str "(" ++ pr ++ str ")"
   * | _ -> pr *)

let pr_pat env sigma c =
  let sigma, patc = constr_of_pat env sigma c in
  pr_constr_pat env sigma patc

let pr_context env sigma c =
  let pr_decl env decl =
    let (id,b,t) = to_tuple decl in
    let bstr = match b with Some b ->
      str ":=" ++ spc () ++ Printer.pr_econstr_env env sigma b | None -> mt() in
    let idstr = match id with Name id -> Id.print id | Anonymous -> str"_" in
    idstr ++ bstr ++ str " : " ++ Printer.pr_econstr_env env sigma t
  in
  let (_, pp) =
    match List.rev c with
    | decl :: decls ->
      List.fold_left (fun (env, pp) decl ->
          (push_rel decl env, pp ++ str "; " ++ pr_decl env decl))
        (push_rel decl env, pr_decl env decl) decls
    | [] -> env, mt ()
  in pp

let ppcontext env sigma c = pp (pr_context env sigma c)

let pr_pats env sigma patcs = prlist_with_sep (fun _ -> str " ") (pr_pat env sigma) (List.rev patcs)

let pr_context_map env sigma (delta, patcs, gamma) =
  let env' = push_rel_context delta env in
  let ctx = pr_context env sigma delta in
  let ctx' = pr_context env sigma gamma in
  (if List.is_empty delta then ctx else ctx ++ str" ") ++ str "|-" ++ str" "
  ++ pr_pats env' sigma patcs ++ str " : "  ++ ctx'

let ppcontext_map env sigma context_map = pp (pr_context_map env sigma context_map)

let ppcontext_map_empty context_map =
  let env = Global.env () in
  ppcontext_map env (Evd.from_env env) context_map

(** Debugging functions *)

let typecheck_map env evars (ctx, subst, ctx') =
  typecheck_rel_context env evars ctx;
  typecheck_rel_context env evars ctx';
  let env = push_rel_context ctx env in
  let _ =
    List.fold_right2
      (fun decl p (evars, subst) ->
         let (na, b, t) = to_tuple decl in
         let evars, c = constr_of_pat ~inacc_and_hide:false env evars p in
         check_term env evars c (substl subst t);
         (evars, c :: subst))
      ctx' subst (evars, [])
  in ()

let check_ctx_map ?(unsafe = false) env evars map =
  if !Equations_common.debug && not unsafe then
    try typecheck_map env evars map; map
    with Pretype_errors.PretypeError (env, sigma, Pretype_errors.TypingError e) ->
      errorlabstrm "equations"
        (str"Type error while building context map: " ++ pr_context_map env evars map ++
         spc () ++ Himsg.explain_type_error env evars e)
       | Invalid_argument s ->
         errorlabstrm "equations"
           (str"Type error while building context map: " ++ pr_context_map env evars map ++
            spc () ++ str"Invalid_argument: " ++ str s)
       | e when is_anomaly e ->
         errorlabstrm "equations"
           (str"Type error while building context map: " ++ pr_context_map env evars map ++
            spc () ++ str"Anomaly: " ++ CErrors.print e)
  else map

let mk_ctx_map ?(unsafe = false) env evars ctx subst ctx' =
  let map = (ctx, subst, ctx') in check_ctx_map ~unsafe env evars map

let rec map_patterns f ps =
  List.map (function
      | PCstr (c, pl) ->
        let c' = destConstruct Evd.empty (f (mkConstructU c)) in
        PCstr (c', map_patterns f pl)
      | PInac c -> PInac (f c)
      | x -> x)
    ps

let map_ctx_map f (g, p, d) =
  map_rel_context f g, map_patterns f p, map_rel_context f d

(** Specialize by a substitution. *)

let subst_pats_constr sigma k s c =
  let rec aux depth c =
    match kind sigma c with
    | Rel n ->
      let k = n - depth in
      if k > 0 then
        try lift depth (pat_constr (nth s (pred k)))
        with Failure _ (* "nth"*) -> c
      else c
    | _ -> map_with_binders sigma succ aux depth c
  in aux k c

let subst_context sigma s ctx =
  let (_, ctx') = fold_right
      (fun decl (k, ctx') ->
         (succ k, map_rel_declaration (subst_pats_constr sigma k s) decl :: ctx'))
      ctx (0, [])
  in ctx'

let rec specialize sigma s p =
  match p with
  | PRel i -> (try nth s (pred i) with Failure _ (* "nth" *) -> p)
  | PCstr(c, pl) -> PCstr (c, specialize_pats sigma s pl)
  | PInac r -> PInac (specialize_constr sigma s r)
  | PHide i ->
    (match nth s (pred i) (* FIXME *) with
     | PRel i -> PHide i
     | PHide i -> PHide i
     | PInac r -> PInac r
     | _ -> assert(false))

and specialize_constr sigma s c = subst_pats_constr sigma 0 s c
and specialize_pats sigma s = List.map (specialize sigma s)

let specialize_rel_context sigma s ctx =
  let subst, res = List.fold_right
      (fun decl (k, acc) ->
         let decl = map_rel_declaration (subst_pats_constr sigma k s) decl in
         (succ k, decl :: acc))
      ctx (0, [])
  in res

let mapping_constr sigma (s : context_map) c = specialize_constr sigma (pi2 s) c

(* Substitute a Constr.t in a pattern. *)

let rec subst_constr_pat sigma k t p =
  match p with
  | PRel i ->
    if i == k then PInac t
    else if i > k then PRel (pred i)
    else p
  | PCstr(c, pl) ->
    PCstr (c, subst_constr_pats sigma k t pl)
  | PInac r -> PInac (substnl [t] (pred k) r)
  | PHide i -> PHide (destRel sigma (substnl [t] (pred k) (mkRel i)))

and subst_constr_pats sigma k t = List.map (subst_constr_pat sigma k t)

(* Lifting patterns. *)

let rec lift_patn n k p =
  match p with
  | PRel i ->
    if i >= k then PRel (i + n)
    else p
  | PCstr(c, pl) -> PCstr (c, lift_patns n k pl)
  | PInac r -> PInac (liftn n (succ k) r)
  | PHide r -> PHide (destRel Evd.empty (liftn n (succ k) (mkRel r)))

and lift_patns n k = List.map (lift_patn n k)

let lift_pat n p = lift_patn n 0 p
let lift_pats n p = lift_patns n 0 p

let rec eq_pat sigma p1 p2 =
  match p1, p2 with
  | PRel i, PRel i' -> i = i'
  | PHide i, PHide i' -> i = i'
  | PCstr (c, pl), PCstr (c', pl') -> eq_constructor (fst c) (fst c') && List.for_all2 (eq_pat sigma) pl pl'
  | PInac c, PInac c' -> EConstr.eq_constr sigma c c'
  | _, _ -> false

let make_permutation ?(env = Global.env ()) (sigma : Evd.evar_map)
    ((ctx1, pats1, _) : context_map) ((ctx2, pats2, _) : context_map) : context_map =
  let len = List.length ctx1 in
  let perm = Array.make len None in
  let merge_rels i1 i2 =
    match perm.(pred i2) with
    | None -> perm.(pred i2) <- Some i1
    | Some j when Int.equal i1 j -> ()
    | Some k ->
      let rel_id i ctx =
        Pp.int i ++ str " = " ++
        Names.Name.print (Equations_common.(get_name (lookup_rel i ctx))) in
      failwith
        (Pp.string_of_ppcmds
           (str "Could not generate a permutation: two different instances:" ++
              rel_id i2 ctx2 ++ str" in ctx2 is invertible to " ++
              rel_id k ctx1 ++ str" and " ++ rel_id i1 ctx1))
  in
  let reduce env sigma c =
    let flags = CClosure.RedFlags.red_sub CClosure.all CClosure.RedFlags.fDELTA in
    let c' = Reductionops.clos_whd_flags flags env sigma c in
    c'
  in
  let env1 = push_rel_context ctx1 env in
  let rec merge_pats p1 p2 =
    match p1, p2 with
    | _, PInac p2 -> ()
    | PCstr (p, ps), PCstr (_, ps') -> List.iter2 (fun p1 p2 -> merge_pats p1 p2) ps ps'
    | PHide i, _ -> merge_pats (PRel i) p2
    | _, PHide i -> merge_pats p1 (PRel i)
    | PRel i1, PRel i2 ->
      if i1 <= len then
        try merge_rels i1 i2
        with Invalid_argument _ -> failwith "Could not generate a permutation: different variables"
      else ()
    | PInac c, _ ->
      let p1' = pat_of_constr sigma (reduce env1 sigma c) in
      if eq_pat sigma p1 p1' then
        failwith "Could not generate a permutation: irreducible inaccessible"
      else merge_pats p1' p2
    | _, _ ->
      failwith (Pp.string_of_ppcmds (str"Could not generate a permutation, patterns differ: "
                  ++ pr_pat env sigma p1 ++ str " and " ++ pr_pat env sigma p2))
  in
  (* FIXME This function could also check that constructors are the same and
   * so on. It also need better error handling. *)
  List.iter2 merge_pats pats1 pats2;
  let pats = Array.map (function
      | None -> failwith "Could not generate a permutation"
      | Some i -> PRel i) perm in
  let pats = Array.to_list pats in
  mk_ctx_map env sigma ctx1 pats ctx2


let specialize_mapping_constr sigma (m : context_map) c =
  specialize_constr sigma (pi2 m) c

let rels_of_tele tele = Termops.rel_list 0 (List.length tele)

let patvars_of_tele tele =
  let len = List.length tele in
  CList.init len (fun c -> PRel (len - c))

let pat_vars_list n = CList.init n (fun i -> PRel (succ i))

let intset_of_list =
  fold_left (fun s x -> Int.Set.add x s) Int.Set.empty

let split_context n c =
  let after, before = List.chop n c in
  match before with
  | hd :: tl -> after, hd, tl
  | [] -> raise (Invalid_argument "split_context")

let split_tele n (ctx : rel_context) =
  let rec aux after n l =
    match n, l with
    | 0, decl :: before -> before, decl, List.rev after
    | n, decl :: before -> aux (decl :: after) (pred n) before
    | _ -> raise (Invalid_argument "split_tele")
  in aux [] n ctx

(* Compute the transitive closure of the dependency relation for a term in a context *)

let rels_above ctx x =
  let len = List.length ctx in
  intset_of_list (CList.init (len - x) (fun i -> x + succ i))



let is_fix_proto sigma t =
  match kind sigma t with
  | LetIn (_, f, _, _) -> is_global sigma (Lazy.force coq_fix_proto) f
  | _ -> false

let fix_rels sigma ctx =
  List.fold_left_i (fun i acc decl ->
      if is_fix_proto sigma (get_type decl) then Int.Set.add i acc else acc)
    1 Int.Set.empty ctx

let rec dependencies_of_rel ~with_red env evd ctx k x =
  let (n,b,t) = to_tuple (nth ctx (pred k)) in
  let b = Option.map (lift k) b and t = lift k t in
  let bdeps = match b with Some b -> dependencies_of_term ~with_red env evd ctx b x | None -> Int.Set.empty in
  Int.Set.union (Int.Set.singleton k) (Int.Set.union bdeps (dependencies_of_term ~with_red env evd ctx t x))

and dependencies_of_term ~with_red env evd ctx t x =
  (* First we get the syntactic dependencies of t. *)
  let rels = Termops.free_rels evd t in
  let rels =
    (* We check if it mentions x. If it does, we reduce t because
       we know it should not. *)
    if with_red && Int.Set.mem x rels then
      Termops.free_rels evd (nf_betadeltaiota env evd t)
    else rels
  in Int.Set.fold (fun i -> Int.Set.union (dependencies_of_rel ~with_red env evd ctx i x)) rels Int.Set.empty

let non_dependent evd ctx c =
  List.fold_left_i (fun i acc (_, _, t) ->
      if not (Termops.dependent evd (lift (-i) c) t) then Int.Set.add i acc else acc)
    1 Int.Set.empty ctx

let subst_term_in_context sigma t ctx =
  let (term, rel, newctx) =
    List.fold_right
      (fun decl (term, rel, newctx) ->
         let (n, b, t) = to_tuple decl in
         let decl' = make_def n b (Termops.replace_term sigma term (mkRel rel) t) in
         (lift 1 term, succ rel, decl' :: newctx))
      ctx (t, 1, [])
  in newctx

let strengthen ?(full=true) ?(abstract=false) env evd (ctx : rel_context) x (t : constr) =
  let rels = Int.Set.union (if full then rels_above ctx x else Int.Set.singleton x)
      (* (Int.Set.union *) (Int.Set.union (dependencies_of_term ~with_red:true env evd ctx t x) (fix_rels evd ctx))
  (* (non_dependent ctx t)) *)
  in
  (* For each variable that we need to push under x, we check
     if its type or body mentions x syntactically. If it does, we normalize
     it. *)
  let maybe_reduce k t =
    if Int.Set.mem k (Termops.free_rels evd t) then
      nf_betadeltaiota env evd t
    else t
  in
  let ctx = List.map_i (fun k decl ->
      if Int.Set.mem k rels && k < x then
        map_rel_declaration (maybe_reduce (x - k)) decl
      else decl) 1 ctx in
  let len = length ctx in
  let nbdeps = Int.Set.cardinal rels in
  let lifting = len - nbdeps in (* Number of variables not linked to t *)
  let rec aux k n acc m rest s = function
    | decl :: ctx' ->
      if Int.Set.mem k rels then
        let rest' = subst_telescope (mkRel (nbdeps + lifting - pred m)) rest in
        aux (succ k) (succ n) (decl :: acc) m rest' (Inl n :: s) ctx'
      else aux (succ k) n (subst_telescope mkProp acc) (succ m) (decl :: rest) (Inr m :: s) ctx'
    | [] -> rev acc, rev rest, s
  in
  let (min, rest, subst) = aux 1 1 [] 1 [] [] ctx in
  let lenrest = length rest in
  let subst = rev subst in
  let reorder = List.map_i (fun i -> function Inl x -> (x + lenrest, i) | Inr x -> (x, i)) 1 subst in
  let subst = List.map (function Inl x -> PRel (x + lenrest) | Inr x -> PRel x) subst in
  let ctx' =
    if abstract then
      subst_term_in_context evd (lift (-lenrest) (specialize_constr evd subst t)) rest @ min
    else rest @ min
  in
  (ctx', subst, ctx), reorder

(* TODO Merge both strengthening functions. Bottom one might be better. *)
(* Return a substitution (and its inverse) which is just a permutation
 * of the variables in the context which is well-typed, and such that
 * all variables in [t] (and their own dependencies) are now declared
 * before [x] in the context. *)
let new_strengthen (env : Environ.env) (evd : Evd.evar_map) (ctx : rel_context)
    (x : int) ?(rels : Int.Set.t = rels_above ctx x) (t : constr) :
  context_map * context_map =
  let rels = Int.Set.union rels (dependencies_of_term ~with_red:true env evd ctx t x) in
  let maybe_reduce k t =
    if Int.Set.mem k (Termops.free_rels evd t) then
      Equations_common.nf_betadeltaiota env evd t
    else t
  in
  (* We may have to normalize some declarations in the context if they
   * mention [x] syntactically when they shouldn't. *)
  let ctx = CList.map_i (fun k decl ->
      if Int.Set.mem k rels && k < x then
        Equations_common.map_rel_declaration (maybe_reduce (x - k)) decl
      else decl) 1 ctx in
  (* Now we want to put everything in [rels] as the oldest part of the context,
   * and everything else after. *)
  let len_ctx = Context.Rel.length ctx in
  let lifting = len_ctx - Int.Set.cardinal rels in
  let rev_subst = Array.make len_ctx (PRel 0) in
  (* [k] is the current rel in [ctx].
   * [n] is the position of the next rel that should be in the newer part of [ctx'].
   * [lifting] is the number of rels that will end in this newer part.
   * [before] and [after] are the older and newer parts of [ctx']. *)
  let rec aux k before after n subst = function
    | decl :: ctx ->
      (* We just lift the declaration so that it is typed under the whole
       * context [ctx]. We will perform the proper substitution right after. *)
      let decl = Equations_common.map_rel_declaration (Vars.lift k) decl in
      if Int.Set.mem k rels then
        (* [k - n + 1] is the position of this rel in the older part of [ctx'], which
         * is shifted by [lifting]. *)
        let subst = PRel (lifting + k - n + 1) :: subst in
        rev_subst.(k + lifting - n) <- PRel k;
        aux (succ k) (decl :: before) after n subst ctx
      else
        let subst = PRel n :: subst in
        rev_subst.(n - 1) <- PRel k;
        aux (succ k) before (decl :: after) (succ n) subst ctx
    | [] -> CList.rev (before @ after), CList.rev subst
  in
  (* Now [subst] is a list of indices which represents the substitution
   * that we must apply. *)
  (* Right now, [ctx'] is an ill-typed rel_context, we need to apply [subst]. *)
  let (ctx', subst) = aux 1 [] [] 1 [] ctx in
  let rev_subst = Array.to_list rev_subst in
  (* Fix the context [ctx'] by using [subst]. *)
  (* Currently, each declaration in [ctx'] is actually typed under [ctx]. *)
  (* We can apply the substitution to get a declaration typed under [ctx'],
   * and lift it back to its place in [ctx']. *)
  let do_subst k c = Vars.lift (-k) (specialize_constr evd subst c) in
  let ctx' = CList.map_i (fun k decl ->
      Equations_common.map_rel_declaration (do_subst k) decl) 1 ctx' in
  (* Now we have everything need to build the two substitutions. *)
  let s = mk_ctx_map env evd ctx' subst ctx in
  let rev_s = mk_ctx_map env evd ctx rev_subst ctx' in
  s, rev_s


let id_pats g = List.rev (patvars_of_tele g)
let id_subst g = (g, id_pats g, g)

let eq_context_nolet env sigma (g : rel_context) (d : rel_context) =
  try
    snd
      (List.fold_right2 (fun decl decl' (env, acc) ->
           if acc then
             let t = get_type decl and t' = get_type decl' in
             let res = (eq_constr sigma t t' ||
                        (* FIXME: is_conv is not respecting some universe equalities in sigma *)
                        let t = Evarutil.nf_evar sigma t in
                        let t' = Evarutil.nf_evar sigma t' in
                        is_conv env sigma t t') in
             if res = false then
               Printf.eprintf
                 "While comparing contexts: %s and %s : %s\n"
                 (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma (EConstr.Unsafe.to_constr t)))
                 (Pp.string_of_ppcmds (Printer.pr_constr_env env sigma (EConstr.Unsafe.to_constr t')))
                 (* (Pp.string_of_ppcmds (UGraph.pr_universes Univ.Level.pr (Evd.universes sigma))); *)
                 (Pp.string_of_ppcmds (Termops.pr_evar_map ~with_univs:true None sigma));
             (push_rel decl env, res)
           else env, acc) g d (env, true))
  with Invalid_argument _ (* "List.fold_right2" *) -> false
     | e ->
       Printf.eprintf
         "Exception while comparing contexts %s and %s : %s\n"
         (Pp.string_of_ppcmds (Termops.Internal.print_rel_context (push_rel_context g env)))
         (Pp.string_of_ppcmds (Termops.Internal.print_rel_context (push_rel_context d env)))
         (Printexc.to_string e);
       raise e

let check_eq_context_nolet env sigma (_, _, g as snd) (d, _, _ as fst) =
  if eq_context_nolet env sigma g d then ()
  else errorlabstrm "check_eq_context_nolet"
      (str "Contexts do not agree for composition: "
       ++ pr_context_map env sigma snd ++ str " and " ++ pr_context_map env sigma fst)

let compose_subst ?(unsafe = false) env ?(sigma=Evd.empty) ((g',p',d') as snd) ((g,p,d) as fst) =
  if !Equations_common.debug && not unsafe then check_eq_context_nolet env sigma snd fst;
  mk_ctx_map ~unsafe env sigma g' (specialize_pats sigma p' p) d
(*     (g', (specialize_pats p' p), d) *)

let push_mapping_context sigma decl (g,p,d) =
  let decl' = map_rel_declaration (specialize_constr sigma p) decl in
  (decl' :: g, (PRel 1 :: List.map (lift_pat 1) p), decl :: d)

let lift_subst env evd (ctx : context_map) (g : rel_context) =
  let map = List.fold_right (fun decl acc -> push_mapping_context evd decl acc) g ctx in
  check_ctx_map env evd map

let single_subst ?(unsafe = false) env evd x p g =
  let t = pat_constr p in
  if eq_constr evd t (mkRel x) then
    id_subst g
  else if noccur_between evd 1 x t then
    (* The term to substitute refers only to previous variables. *)
    let substctx = subst_in_ctx x t g in
    let pats = CList.init (List.length g)
        (fun i -> let k = succ i in
          if k == x then (lift_pat (-1) p)
          else if k > x then PRel (pred k)
          else PRel k)
        (* let substctx = set_in_ctx x t g in *)
        (* let pats = list_tabulate  *)
        (* 	(fun i -> let k = succ i in if k = x then p else PRel k) *)
        (* 	(List.length g) *)
    in mk_ctx_map ~unsafe env evd substctx pats g
  else
    let (ctx, s, g), _ = strengthen env evd g x t in
    let x' = match nth s (pred x) with PRel i -> i | _ -> error "Occurs check singleton subst"
    and t' = specialize_constr evd s t in
    (* t' is in ctx. Do the substitution of [x'] by [t] now
       in the context and the patterns. *)
    let substctx = subst_in_ctx x' t' ctx in
    let pats = List.map_i (fun i p -> subst_constr_pat evd x' (lift (-1) t') p) 1 s in
    mk_ctx_map ~unsafe env evd substctx pats g


let pr_rel_name env i =
  Name.print (get_name (lookup_rel i env))

let is_local_def i ctx =
  let decl = List.nth ctx (pred i) in
  Context.Rel.Declaration.is_local_def decl

let filter_def_pats (ctx, pats, _) =
  CList.map_filter (function
      | PRel i when is_local_def i ctx -> None
      | PHide i when is_local_def i ctx -> None
      | p -> Some p) pats
