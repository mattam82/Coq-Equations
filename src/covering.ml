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
open Environ
open Reductionops
open Pp
open Pretype_errors
open List
open Tacmach
open Evarutil
open Evar_kinds
open Termops
open Equations_common
open Syntax

open EConstr
open EConstr.Vars   

open Ltac_plugin
open Extraction_plugin

(** Abstract syntax for dependent pattern-matching. *)

type peconstructor = Names.constructor peuniverses

type pat =
  | PRel of int
  | PCstr of peconstructor * pat list
  | PInac of constr
  | PHide of int

type context_map = rel_context * pat list * rel_context

(** Splitting trees *)

type path_component =
  | Evar of Evar.t
  | Ident of Id.t

type path = path_component list

type splitting = 
  | Compute of context_map * where_clause list * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Valid of context_map * types * identifier list * tactic *
             (Proofview.entry * Proofview.proofview) *
             (Goal.goal * constr list * context_map * context_map option * splitting) list
  | Mapping of context_map * splitting (* Mapping Γ |- p : Γ' and splitting Γ' |- p : Δ *)
  | RecValid of identifier * splitting
  | Refined of context_map * refined_node * splitting

and where_clause =
  { where_program : program_info;
    where_path : path;
    where_orig : path;
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

type int_data = {
  rec_info : rec_type option;
  fixdecls : rel_context;
  intenv : Constrintern.internalization_env;
  notations : (Names.lstring * Constrexpr.constr_expr *
               Notation_term.scope_name option) list
}

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

let debug = true

let check_ctx_map ?(unsafe = false) env evars map =
  if debug && not unsafe then
    try typecheck_map env evars map; map
    with Pretype_errors.PretypeError (env, sigma, TypingError e) ->
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
  let rec collect_rels k acc c =
    if isRel sigma c then
      let x = destRel sigma c in
      if k < x && x <= len + k then x - k :: acc
      else acc
    else Termops.fold_constr_with_binders sigma succ collect_rels k acc c
  in
  let merge_constrs c1 c2 =
    let rels1 = collect_rels 0 [] c1 in
    let rels2 = collect_rels 0 [] c2 in
    try List.iter2 merge_rels rels1 rels2
    with Invalid_argument _ -> failwith "Could not generate a permutation: different variables"
  in
  (* FIXME This function could also check that constructors are the same and
   * so on. It also need better error handling. *)
  let env1 = push_rel_context ctx1 env in
  let env2 = push_rel_context ctx2 env in
  let reduce env sigma c =
    let flags = CClosure.RedFlags.red_sub CClosure.all CClosure.RedFlags.fDELTA in
    Reductionops.clos_norm_flags flags env sigma c
  in
  let merge_pats pat1 pat2 =
    let sigma, c1 = constr_of_pat ~inacc_and_hide:false env1 sigma pat1 in
    let sigma, c2 = constr_of_pat ~inacc_and_hide:false env2 sigma pat2 in
    let c1 = reduce env1 sigma c1 in
    let c2 = reduce env2 sigma c2 in
    merge_constrs c1 c2
  in
  List.iter2 merge_pats pats1 pats2;
  let pats = Array.map (function
      | None -> failwith "Could not generate a permutation"
      | Some i -> PRel i) perm in
  let pats = Array.to_list pats in
  mk_ctx_map env sigma ctx1 pats ctx2

type unification_result = 
  (context_map * int * constr * pat) option

let rec context_map_of_splitting : splitting -> context_map = function
  | Compute (subst, _, _, _) -> subst
  | Split (subst, _, _, _) -> subst
  | Valid (subst, _, _, _, _, _) -> subst
  | Mapping (subst, _) -> subst
  | RecValid (_, s) -> context_map_of_splitting s
  | Refined (subst, _, _) -> subst

let specialize_mapping_constr sigma (m : context_map) c = 
  specialize_constr sigma (pi2 m) c

let rels_of_tele tele = rel_list 0 (List.length tele)

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
  let rels = free_rels evd t in
  let rels =
    (* We check if it mentions x. If it does, we reduce t because
       we know it should not. *)
    if with_red && Int.Set.mem x rels then
      free_rels evd (nf_betadeltaiota env evd t)
    else rels
  in Int.Set.fold (fun i -> Int.Set.union (dependencies_of_rel ~with_red env evd ctx i x)) rels Int.Set.empty

let non_dependent evd ctx c =
  List.fold_left_i (fun i acc (_, _, t) -> 
      if not (dependent evd (lift (-i) c) t) then Int.Set.add i acc else acc)
    1 Int.Set.empty ctx

let subst_term_in_context sigma t ctx =
  let (term, rel, newctx) = 
    List.fold_right 
      (fun decl (term, rel, newctx) ->
         let (n, b, t) = to_tuple decl in
         let decl' = make_def n b (replace_term sigma term (mkRel rel) t) in
         (lift 1 term, succ rel, decl' :: newctx))
      ctx (t, 1, [])
  in newctx

let strengthen ?(full=true) ?(abstract=false) env evd (ctx : rel_context) x (t : constr) =
  let _rels = dependencies_of_term env evd ctx t x in
  let rels = Int.Set.union (if full then rels_above ctx x else Int.Set.singleton x)
      (* (Int.Set.union *) (Int.Set.union (dependencies_of_term ~with_red:true env evd ctx t x) (fix_rels evd ctx))
  (* (non_dependent ctx t)) *)
  in
  (* For each variable that we need to push under x, we check
     if its type or body mentions x syntactically. If it does, we normalize
     it. *)
  let maybe_reduce k t =
    if Int.Set.mem k (free_rels evd t) then
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
             (push_rel decl env,
              (eq_constr sigma t t' || is_conv env sigma t t'))
           else env, acc) g d (env, true))
  with Invalid_argument _ (* "List.fold_right2" *) -> false
     | e ->
       Printf.eprintf
         "Exception while comparing contexts %s and %s : %s\n"
         (Pp.string_of_ppcmds (Internal.print_rel_context (push_rel_context g env)))
         (Pp.string_of_ppcmds (Internal.print_rel_context (push_rel_context d env)))
         (Printexc.to_string e);
       raise e

let check_eq_context_nolet env sigma (_, _, g as snd) (d, _, _ as fst) =
  if eq_context_nolet env sigma g d then ()
  else errorlabstrm "check_eq_context_nolet"
      (str "Contexts do not agree for composition: "
       ++ pr_context_map env sigma snd ++ str " and " ++ pr_context_map env sigma fst)

let compose_subst ?(unsafe = false) env ?(sigma=Evd.empty) ((g',p',d') as snd) ((g,p,d) as fst) =
  if debug && not unsafe then check_eq_context_nolet env sigma snd fst;
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

exception Conflict
exception Stuck

type 'a unif_result = UnifSuccess of 'a | UnifFailure | UnifStuck

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

let _rename_prob_subst env ctx s =
  let _avoid = List.fold_left (fun avoid decl ->
      match get_name decl with
      | Anonymous -> avoid
      | Name id -> Id.Set.add id avoid) Id.Set.empty ctx
  in
  let varsubst, rest =
    fold_left (fun (varsubst, rest) ((id, gen), pat) ->
        match pat with
        | PRel i when gen = false -> ((i, id) :: varsubst, rest)
        | _ -> (varsubst, (id, pat) :: rest))
      ([], []) s
  in
  let ctx' =
    List.fold_left_i (fun i acc decl ->
        try let id = List.assoc i varsubst in
          Context.Rel.Declaration.set_name (Name id) decl :: acc
        with Not_found -> decl :: acc)
      1 [] ctx
  in
  (List.rev ctx', id_pats ctx, ctx)

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
  try interp_program_body env evars ctx intenv c ty
  with PretypeError (env, evm, e) ->
    user_err_loc (dummy_loc, "interp_program_body",
                  str "Typechecking failed: " ++  Himsg.explain_pretype_error env evm e)
     | e ->
       user_err_loc (dummy_loc, "interp_program_body",
                     str "Unexpected exception raised while typing body: " ++
                     (match c with ConstrExpr c -> Ppconstr.pr_constr_expr c
                                 | Constr c -> Printer.pr_econstr_env env evars c) ++
                     str " in environment " ++ Printer.pr_rel_context_of (push_rel_context ctx env) evars ++
                     str ":" ++
                     str (Printexc.to_string e))

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

let pr_rel_name env i =
  Name.print (get_name (lookup_rel i env))

let pr_path_component evd = function
  | Evar ev -> pr_existential_key evd ev
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

let pr_splitting env sigma ?(verbose=false) split =
  let verbose pp = if verbose then pp else mt () in
  let pplhs env sigma lhs = pr_pats env sigma (pi2 lhs) in
  let rec aux = function
    | Compute (lhs, wheres, ty, c) -> 
      let env' = push_rel_context (pi1 lhs) env in
      let ppwhere w =
        hov 2 (str"where " ++ Id.print (where_id w) ++ str " : " ++
               (try Printer.pr_econstr_env env'  sigma w.where_type ++
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

let find_empty env delta =
  let r = List.filter (fun v -> 
      match split_var env v delta with
      | None -> false
      | Some (CannotSplit _) -> false
      | Some (Splitted (v, _, r)) -> CArray.for_all (fun x -> x == None) r)
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
  let unused = List.filter (fun (_, used) -> not used) cl in
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
  let pr_rec p =
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
  in
  if !Equations_common.debug then
    Feedback.msg_debug (str "Programs: " ++ prlist_with_sep fnl pr_rec programs)

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

let interp_arity env evd ctx ~poly ~is_rec ~with_evars (((loc,i),rec_annot,l,t,by),clauses as ieqs) =
  let ienv, ((env', sign), impls) = Equations_common.evd_comb1 (interp_context_evars env) evd l in
  let (arity, impls') = Equations_common.evd_comb1 (interp_type_evars_impls env' ?impls:None) evd t in
  let impls = impls @ impls' in
  let sign = nf_rel_context_evar ( !evd) sign in
  let arity = nf_evar ( !evd) arity in
  let default_recarg () =
    let idx = List.length sign - 1 in
    (idx, None)
  in
  let interp_reca k i =
    match k with
    | None | Some Mutual -> MutualOn i
    | Some Nested -> NestedOn (Some i)
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
         else Some (Structural (interp_reca rec_annot (default_recarg ())))
       | Some true -> assert false)
    | Some (Structural lid) ->
      (try
         let k, _, _ = lookup_rel_id (snd lid) sign in
         Some (Structural (interp_reca rec_annot (List.length sign - k, Some lid)))
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
    (* let wfenv = push_rel_context sign env in
     * let evars, c = interp_constr_evars wfenv !evd c in
     * let evars, r =
     *   match r with
     *   | Some r ->
     *     (\* let ty = Retyping.get_type_of env evars c in *\)
     *     (\* TODO use [relation ty] constraint *\)
     *     let evars, r = interp_constr_evars env evars r in
     *     evars, Some r
     *   | None -> evars, None
     * in *)
    let projid = add_suffix i "_comp_proj" in
    let compproj =
      let body =
        it_mkLambda_or_LetIn (mkRel 1)
          (of_tuple (Name (Id.of_string "comp"), None, arity) :: sign @ ctx)
      in
      let _ty = e_type_of (Global.env ()) evd body in
      let univs = Evd.const_univ_entry ~poly !evd in
      let ce =
        Declare.definition_entry (* ~fix_exn: FIXME needed ? *)
          ~univs
          (to_constr !evd body)
      in
      Declare.declare_constant projid
        Entries.(DefinitionEntry ce, Decl_kinds.(IsDefinition Definition))
    in
    Impargs.declare_manual_implicits true (GlobRef.ConstRef compproj) [impls];
    Table.extraction_inline true [Libnames.qualid_of_ident projid];
    let compinfo = LogicalProj { comp_app = to_constr !evd arity;
                                 comp_proj = compproj; comp_recarg = succ (length (sign @ ctx)) } in
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

let compute_rec_data env data p clauses =
  match p.program_rec with
  | Some (Structural ann) ->
    let sign =
      match ann with
      | NestedOn None -> (** Actually the definition is not self-recursive *)
        let fixdecls =
          List.filter (fun decl ->
              let na = Context.Rel.Declaration.get_name decl in
              let id = Nameops.Name.get_id na in
              not (Id.equal id p.program_id)) data.fixdecls
        in lift_rel_context (length fixdecls) p.program_sign @ fixdecls
      | _ -> lift_rel_context (length data.fixdecls) p.program_sign @ data.fixdecls
    in
    let pats = recursive_patterns env p.program_id data.rec_info in
    sign, pats, clauses
  | Some (WellFounded (term, rel, l)) ->
    let pats = pats_of_sign p.program_sign in
    let clause =
      [None, pats, Rec (term, rel, Some (p.program_loc, p.program_id), clauses)]
    in
    p.program_sign, [], clause
  | _ -> p.program_sign, [], clauses

(* let user_pats_of pats =
 *   List.map (fun p -> PUVar (Id.of_string "pat", true)) pats *)

let rec covering_aux env evars p data prev (clauses : (pre_clause * bool) list) path
    (ctx,pats,ctx' as prob) extpats lets ty =
  if !Equations_common.debug then
    Feedback.msg_debug Pp.(str"Launching covering on "++ pr_preclauses env (List.map fst clauses) ++
                           str " with problem " ++ pr_problem p env !evars prob ++
                           str " extpats " ++ pr_user_pats env extpats);
  match clauses with
  | ((loc, lhs, rhs), used as clause) :: clauses' ->
    if !Equations_common.debug then
      Feedback.msg_debug (str "Matching " ++ pr_user_pats env (extpats @ lhs) ++ str " with " ++
                          pr_problem p env !evars prob);
    (match matches (extpats @ lhs) prob with
     | UnifSuccess s ->
       if !Equations_common.debug then Feedback.msg_debug (str "succeeded");
       (* let renaming = rename_prob_subst env ctx (pi1 s) in *)
       let s = (List.map (fun ((x, gen), y) -> x, y) (pi1 s), pi2 s, pi3 s) in
       (* let prob = compose_subst env ~sigma:!evars renaming prob in *)
       let interp =
         interp_clause env evars p data prev clauses' path prob
           extpats lets ty ((loc,lhs,rhs), used) s
       in
       (match interp with
        | None ->
           user_err_loc
            (dummy_loc, "split_var",
             str"Clause " ++ pr_preclause env (loc, lhs, rhs) ++ str" matched but its interpretation failed")
        | Some s -> Some (List.rev prev @ ((loc,lhs,rhs),true) :: clauses', s))

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
                  clauses path (compose_subst env ~sigma:!evars s prob')
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
    | Some i -> Some (List.rev prev @ clauses, Compute (prob, [], ty, REmpty i))
    | None ->
      errorlabstrm "deppat"
        (str "Non-exhaustive pattern-matching, no clause found for:" ++ fnl () ++
         pr_problem p env !evars prob)

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
      if Option.is_empty loc then
        () (** Allow patterns not written by the user to be forced innaccessible silently *)
      else
        match user with
        | PUVar (i, true) ->
          (** If the pattern comes from a wildcard, allow forcing innaccessibles too *)
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
    let () = List.iter (fun c -> ignore (Lazy.force c.where_splitting)) coverings in
    let res = Compute (prob, coverings, ty', RProgram c') in
    Some res

  | Empty (loc,i) ->
    Some (Compute (prob, [], ty, REmpty (get_var loc i s)))

  | Rec (term, rel, name, spl) ->
    let name =
      match name with Some (loc, id) -> id
                    | None -> p.program_id
    in
    let tac = 
      match rel with
      | None -> rec_tac term name
      | Some r ->
        let _rel_check = interp_constr_evars env (!evars) r in
        rec_wf_tac term name r
    in
    let rhs = By (Inl tac, spl) in
    (match covering_aux env evars p data [] [(loc,lhs,rhs),false] (Ident name :: path) prob extpats lets ty with
     | None -> None
     | Some (clauses, split) -> Some (RecValid (p.program_id, split)))

  | By (tac, s) ->
    let () =
      if !Equations_common.debug then begin
      Feedback.msg_debug (str"solve_goal named context: " ++
                          Printer.pr_named_context env !evars
                          (EConstr.Unsafe.to_named_context (named_context env')));
      Feedback.msg_debug (str"solve_goal rel context: " ++
                          Printer.pr_rel_context_of env' !evars)
      end
    in
    let sign, t', rels, _ = push_rel_context_to_named_context ~hypnaming:KeepExistingNames env' !evars ty in
    let sign = named_context_of_val sign in
    let () =
      if !Equations_common.debug then
        Feedback.msg_debug (str"solve_goal named context: " ++
                            Printer.pr_named_context env !evars (EConstr.Unsafe.to_named_context sign))
    in
    let sign', secsign = split_at_eos !evars sign in
    let ids = List.map get_id sign in
    let ids = Names.Id.Set.of_list ids in
    let tac = match tac with
      | Inl tac -> 
        Tacinterp.interp_tac_gen Names.Id.Map.empty ids Tactic_debug.DebugOff tac
      | Inr tac -> Tacinterp.eval_tactic tac
    in
    let env' = reset_with_named_context (val_of_named_context sign) env in
    let entry, proof = Proofview.init !evars [(env', t')] in
    let _, res, _, _ = Proofview.apply env' tac proof in
    let gls, sigma = Proofview.proofview res in
    evars := sigma;
    if Proofview.finished res then
      let c = List.hd (Proofview.partial_proof entry res) in
      Some (Compute (prob, [], ty, RProgram c))
    else
      let solve_goal gl =
        let nctx = named_context_of_val (Goal.V82.hyps !evars gl) in
        let concl = Goal.V82.concl !evars gl in
        let nctx, secctx = split_at_eos !evars nctx in
        let rctx, subst = rel_of_named_context nctx in
        let ty' = subst_vars subst concl in
        let ty', prob, subst, invsubst = match kind !evars ty' with
          | App (f, args) -> 
            if Equations_common.is_global !evars (Lazy.force coq_add_pattern) f then
              let comp = args.(1) and newpattern = pat_of_constr !evars args.(2) in
              let pats =
                let l = pat_vars_list (List.length rctx) in
                newpattern :: List.tl l
              in
              let newprob = rctx, pats, rctx in
              let subst = (rctx, List.tl pats, List.tl rctx) in
              comp, newprob, subst, None
            else
              let pats = rev_map (pat_of_constr !evars) (Array.to_list args) in
              let newprob = rctx, pats, ctx' in
              ty', newprob, id_subst ctx', None
          | _ -> raise (Invalid_argument "covering_aux: unexpected output of tactic call")
        in
        match covering_aux env evars p data [] (List.map (fun x -> x, false) s) path prob extpats lets ty' with
        | None ->
          anomaly ~label:"covering"
            (str "Unable to find a covering for the result of a by clause:" 
             ++ fnl () ++ pr_preclause env (loc, lhs, rhs) ++
             str" refining " ++ pr_context_map env !evars prob)
        | Some (clauses, s) ->
          let args = rev (List.map_filter (fun decl ->
              if get_named_value decl == None then Some (mkVar (get_id decl)) else None) nctx)
          in
          let () = check_unused_clauses env clauses in
          (gl, args, subst, invsubst, s)
      in
      let goals = List.map solve_goal gls in
      Some (Valid (prob, ty, List.map get_id sign', Proofview.V82.of_tactic tac,
                   (entry, res), goals))

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
            | Rec (v, rel, id, s) -> Rec (v, rel, id, cls' n s)
            | By (v, s) -> By (v, cls' n s)
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
    let secvars = Array.of_list secvars in
    let evar = new_untyped_evar () in
    let path' = Evar evar :: path in
    let lets' =
      let letslen = length lets in
      let _, ctxs, _ = lets_of_ctx env ctx evars s in
      let newlets = (lift_rel_context (succ letslen) ctxs)
                    @ (lift_rel_context 1 lets)
      in specialize_rel_context !evars (pi2 cmap) newlets
    in
    let clauses' = List.map (fun x -> x, false) cls' in
    match covering_aux env evars p data [] clauses' path' newprob [] lets' newty with
    | None ->
      errorlabstrm "deppat"
        (str "Unable to build a covering for with subprogram:" ++ fnl () ++
         pr_problem p env !evars newprob ++ fnl () ++
         str "And clauses: " ++ pr_preclauses env cls')
    | Some (clauses, s) ->
      let () = check_unused_clauses env clauses in
      let info =
        { refined_obj = (idref, cconstr, cty);
          refined_rettyp = ty;
          refined_arg = refarg;
          refined_path = path';
          refined_ex = evar;
          refined_app = (mkEvar (evar, secvars), strength_app);
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

    let p = interp_arity env evars ctx ~poly:false ~is_rec:None ~with_evars:true eqs in
    let env0 = Global.env () in (* To get the comp_proj constant *)
    let clauses = Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation env data.intenv) data.notations;
      List.map (interp_eqn env p) clauses) ()
    in
    let sigma, p = adjust_sign_arity env !evars p clauses in
    let () = evars := sigma in

    let pre_type = program_type p in
    let sign, extpats, clauses = compute_rec_data env data p clauses in
    let p, ctxpats =
      let sign = sign @ ctx in
      let extpats = pats_of_sign ctx in
      { p with program_sign = sign }, extpats
    in
    let problem = id_subst p.program_sign in
    let intenv = Constrintern.compute_internalization_env ~impls:data.intenv
        env !evars Constrintern.Recursive [id] [pre_type] [p.program_impls]
    in
    let data = { data with intenv; } in
    let relty = (* subst_vars (List.map (destVar !evars) inst) *) (program_type p) in
    let src = (Some loc, QuestionMark {
        qm_obligation=Define false;
        qm_name=Name id;
        qm_record_field=None;
      }) in
    let sigma, term = Equations_common.new_evar env0 !evars ~src relty in
    let () = evars := sigma in
    let ev = destEvar !evars term in
    let path = Evar (fst ev) :: path in
    let splitting = lazy (covering env0 evars p data clauses path problem (extpats @ ctxpats) p.program_arity) in
    let termapp = mkApp (term, extended_rel_vect 0 ctx) in
    let decl = make_def (Name id) (Some termapp) pre_type in
    (* let nadecl = make_named_def id (Some (substl inst term)) (program_type p) in *)
    let covering =
      {where_program = p; where_path = path;
       where_orig = path;
       where_prob = problem;
       where_arity = p.program_arity;
       where_term = termapp;
       where_type = pre_type;
       where_splitting = splitting }
    in
    (data, decl :: lets, succ nlets, covering :: coverings,
     push_rel decl envctx)
  in
  let (data, lets, nlets, coverings, envctx') =
    List.fold_left aux (data, ctx, 0, [], push_rel_context ctx env0) w
  in (data, envctx, lets, push_rel_context ctx env0, coverings, liftn, subst)

and covering ?(check_unused=true) env evars p data (clauses : pre_clause list)
    path prob extpats ty =
  let clauses = (List.map (fun x -> (x,false)) clauses) in
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
  let sign, extpats, clauses = compute_rec_data env data p clauses in
  let prob = id_subst sign in
  let arity = nf_evar !evd p.program_arity in
  p, covering env evd p data clauses [Ident p.program_id] prob extpats arity

let coverings env evd data programs equations =
  List.map2 (program_covering env evd data) programs equations
