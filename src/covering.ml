(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Cases
open Util
open Errors
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
open Errors
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
open Termops
open Syntax

(** Abstract syntax for dependent pattern-matching. *)

type pat =
  | PRel of int
  | PCstr of pconstructor * pat list
  | PInac of constr
  | PHide of int

type context_map = rel_context * pat list * rel_context

(** Splitting trees *)
type path = Evd.evar list

type splitting = 
  | Compute of context_map * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Valid of context_map * types * identifier list * tactic *
      (Proofview.entry * Proofview.proofview) *
      (goal * constr list * context_map * splitting) list
  | RecValid of identifier * splitting
  | Refined of context_map * refined_node * splitting

and refined_node = 
  { refined_obj : identifier * constr * types;
    refined_rettyp : types; 
    refined_arg : int;
    refined_path : path;
    refined_ex : existential_key;
    refined_app : constr * constr list;
    refined_revctx : context_map;
    refined_newprob : context_map;
    refined_newprob_to_lhs : context_map;
    refined_newty : types }

and splitting_rhs = 
  | RProgram of constr
  | REmpty of int

let mkInac env c =
  mkApp (Lazy.force coq_inacc, [| Typing.type_of env Evd.empty c ; c |])

let mkHide env c =
  mkApp (Lazy.force coq_hide, [| Typing.type_of env Evd.empty c ; c |])

let rec pat_constr = function
  | PRel i -> mkRel i
  | PCstr (c, p) -> 
      let c' = mkConstructU c in
	mkApp (c', Array.of_list (map pat_constr p))
  | PInac r -> r
  | PHide c -> mkRel c
    
let rec constr_of_pat ?(inacc=true) env = function
  | PRel i -> mkRel i
  | PCstr (c, p) ->
      let c' = mkConstructU c in
	mkApp (c', Array.of_list (constrs_of_pats ~inacc env p))
  | PInac r ->
      if inacc then try mkInac env r with _ -> r else r
  | PHide i -> mkHide env (mkRel i)

and constrs_of_pats ?(inacc=true) env l = map (constr_of_pat ~inacc env) l

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

let inaccs_of_constrs l = map (fun x -> PInac x) l

let rec pats_of_constrs l = map pat_of_constr l
and pat_of_constr c =
  match kind_of_term c with
  | Rel i -> PRel i
  | App (f, [| a ; c |]) when eq_constr f (Lazy.force coq_inacc) ->
      PInac c
  | App (f, [| a ; c |]) when eq_constr f (Lazy.force coq_hide) ->
      PHide (destRel c)
  | App (f, args) when isConstruct f ->
      let ((ind,_),_ as cstr) = destConstruct f in
      let nparams = Inductiveops.inductive_nparams ind in
      let params, args = Array.chop nparams args in
      PCstr (cstr, inaccs_of_constrs (Array.to_list params) @ pats_of_constrs (Array.to_list args))
  | Construct f -> PCstr (f, [])
  | _ -> PInac c


(** Pretty-printing *)

let pr_constr_pat env c =
  let pr = print_constr_env env c in
    match kind_of_term c with
    | App _ -> str "(" ++ pr ++ str ")"
    | _ -> pr

let pr_pat env c =
  let patc = constr_of_pat env c in
    pr_constr_pat env patc

let pr_context env c =
  let pr_decl env (id,b,t) = 
    let bstr = match b with Some b -> str ":=" ++ spc () ++ print_constr_env env b | None -> mt() in
    let idstr = match id with Name id -> pr_id id | Anonymous -> str"_" in
      idstr ++ bstr ++ str " : " ++ print_constr_env env t
  in
  let (_, pp) =
    match List.rev c with
    | decl :: decls -> 
	List.fold_left (fun (env, pp) decl ->
	  (push_rel decl env, pp ++ str ";" ++ spc () ++ pr_decl env decl))
	  (push_rel decl env, pr_decl env decl) decls
    | [] -> env, mt ()
  in pp

let ppcontext c = pp (pr_context (Global.env ()) c)

let pr_context_map env (delta, patcs, gamma) =
  let env' = push_rel_context delta env in
  let ctx = pr_context env delta in
  let ctx' = pr_context env gamma in
    (if List.is_empty delta then ctx else ctx ++ spc ()) ++ str "|-" ++ spc ()
    ++ prlist_with_sep spc (pr_pat env') (List.rev patcs) ++
      str " : "  ++ ctx'

let ppcontext_map context_map = pp (pr_context_map (Global.env ()) context_map)

(** Debugging functions *)

let typecheck_map evars (ctx, subst, ctx') =
  typecheck_rel_context evars ctx;
  typecheck_rel_context evars ctx';
  let env = push_rel_context ctx (Global.env ()) in
  let _ = 
    List.fold_right2 
      (fun (na, b, t) p subst ->
	 let c = constr_of_pat env p in
	   check_term env evars c (substl subst t);
	   (c :: subst))
      ctx' subst []
  in ()

let check_ctx_map evars map =
  if debug then
    try typecheck_map evars map; map
    with Type_errors.TypeError (env, e) ->
      errorlabstrm "equations"
	(str"Type error while building context map: " ++ pr_context_map (Global.env ()) map ++
	   spc () ++ Himsg.explain_type_error env evars e)
  else map
    
let mk_ctx_map evars ctx subst ctx' =
  let map = (ctx, subst, ctx') in check_ctx_map evars map

let map_ctx_map f (g, p, d) =
  map_rel_context f g, p, map_rel_context f d

(** Specialize by a substitution. *)

let subst_pats_constr k s c = 
  let rec aux depth c =
    match kind_of_term c with
    | Rel n -> 
	let k = n - depth in 
	  if k > 0 then
	    try lift depth (pat_constr (nth s (pred k)))
	    with Failure "nth" -> c
	  else c
    | _ -> map_constr_with_binders succ aux depth c
  in aux k c

let subst_context s ctx =
  let (_, ctx') = fold_right
    (fun (id, b, t) (k, ctx') ->
      (succ k, (id, Option.map (subst_pats_constr k s) b, subst_pats_constr k s t) :: ctx'))
    ctx (0, [])
  in ctx'

let rec specialize s p = 
  match p with
  | PRel i -> (try nth s (pred i) with Failure "nth" -> p)
  | PCstr(c, pl) -> PCstr (c, specialize_pats s pl)
  | PInac r -> PInac (specialize_constr s r)
  | PHide i -> 
      (match nth s (pred i) (* FIXME *) with
      | PRel i -> PHide i
      | PHide i -> PHide i
      | PInac r -> PInac r
      | _ -> assert(false))

and specialize_constr s c = subst_pats_constr 0 s c
and specialize_pats s = map (specialize s)

let specialize_rel_context s ctx =
  let subst, res = List.fold_right
    (fun decl (k, acc) ->
      let decl = map_rel_declaration (subst_pats_constr k s) decl in
	(succ k, decl :: acc))
    ctx (0, [])
  in res

let mapping_constr (s : context_map) c = specialize_constr (pi2 s) c

(* Substitute a constr in a pattern. *)

let rec subst_constr_pat k t p = 
  match p with
  | PRel i -> 
      if i == k then PInac t
      else if i > k then PRel (pred i)
      else p
  | PCstr(c, pl) ->
      PCstr (c, subst_constr_pats k t pl)
  | PInac r -> PInac (substnl [t] (pred k) r)
  | PHide i -> PHide (destRel (substnl [t] (pred k) (mkRel i)))

and subst_constr_pats k t = map (subst_constr_pat k t)

(* Substitute a constr [cstr] in rel_context [ctx] for variable [k]. *)

let subst_rel_context k cstr ctx = 
  let (_, ctx') = fold_right 
    (fun (id, b, t) (k, ctx') ->
      (succ k, (id, Option.map (substnl [cstr] k) b, substnl [cstr] k t) :: ctx'))
    ctx (k, [])
  in ctx'

(* A telescope is a reversed rel_context *)

let subst_telescope cstr ctx = 
  let (_, ctx') = fold_left
    (fun (k, ctx') (id, b, t) ->
      (succ k, (id, Option.map (substnl [cstr] k) b, substnl [cstr] k t) :: ctx'))
    (0, []) ctx
  in rev ctx'

(* Substitute rel [n] by [c] in [ctx]
   Precondition: [c] is typable in [ctx] using variables 
   above [n] *)
    
let subst_in_ctx (n : int) (c : constr) (ctx : rel_context) : rel_context =
  let rec aux k after = function
    | [] -> []
    | (name, b, t as decl) :: before ->
	if k == n then (subst_rel_context 0 (lift (-k) c) (rev after)) @ before
	else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

let set_in_ctx (n : int) (c : constr) (ctx : rel_context) : rel_context =
  let rec aux k after = function
    | [] -> []
    | (name, b, t as decl) :: before ->
	if k == n then (rev after) @ (name, Some (lift (-k) c), t) :: before
	else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

(* Lifting patterns. *)

let rec lift_patn n k p = 
  match p with
  | PRel i ->
      if i >= k then PRel (i + n)
      else p
  | PCstr(c, pl) -> PCstr (c, lift_patns n k pl)
  | PInac r -> PInac (liftn n (succ k) r)
  | PHide r -> PHide (destRel (liftn n (succ k) (mkRel r)))
      
and lift_patns n k = map (lift_patn n k)

let lift_pat n p = lift_patn n 0 p
let lift_pats n p = lift_patns n 0 p

type unification_result = 
  (context_map * int * constr * pat) option

let specialize_mapping_constr (m : context_map) c = 
  specialize_constr (pi2 m) c
    
let rels_of_tele tele = rel_list 0 (List.length tele)

let patvars_of_tele tele = map (fun c -> PRel (destRel c)) (rels_of_tele tele)

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



let is_fix_proto t =
  match kind_of_term t with
  | App (f, args) when is_global (Lazy.force coq_fix_proto) f ->
      true
  | _ -> false

let fix_rels ctx =
  List.fold_left_i (fun i acc (_, _, t) -> 
    if is_fix_proto t then Int.Set.add i acc else acc)
    1 Int.Set.empty ctx

let rec dependencies_of_rel ctx k =
  let (n,b,t) = nth ctx (pred k) in
  let b = Option.map (lift k) b and t = lift k t in
  let bdeps = match b with Some b -> dependencies_of_term ctx b | None -> Int.Set.empty in
    Int.Set.union (Int.Set.singleton k) (Int.Set.union bdeps (dependencies_of_term ctx t))

and dependencies_of_term ctx t =
  let rels = free_rels t in
    Int.Set.fold (fun i -> Int.Set.union (dependencies_of_rel ctx i)) rels Int.Set.empty

let non_dependent ctx c =
  List.fold_left_i (fun i acc (_, _, t) -> 
    if not (dependent (lift (-i) c) t) then Int.Set.add i acc else acc)
    1 Int.Set.empty ctx

let subst_term_in_context t ctx =
  let (term, rel, newctx) = 
    List.fold_right 
      (fun (n, b, t) (term, rel, newctx) -> 
	 let decl' = (n, b, replace_term term (mkRel rel) t) in
	   (lift 1 term, succ rel, decl' :: newctx))
      ctx (t, 1, [])
  in newctx

let strengthen ?(full=true) ?(abstract=false) (ctx : rel_context) x (t : constr) =
  let rels = Int.Set.union (if full then rels_above ctx x else Int.Set.singleton x)
    (* (Int.Set.union *) (Int.Set.union (dependencies_of_term ctx t) (fix_rels ctx))
    (* (non_dependent ctx t)) *)
  in
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
  let subst = map (function Inl x -> PRel (x + lenrest) | Inr x -> PRel x) subst in
  let ctx' = 
    if abstract then 
      subst_term_in_context (lift (-lenrest) (specialize_constr subst t)) rest @ min
    else rest @ min 
  in
    (ctx', subst, ctx), reorder

let id_subst g = (g, rev (patvars_of_tele g), g)
	
let eq_context_nolet env sigma (g : rel_context) (d : rel_context) =
  try 
    snd 
      (List.fold_right2 (fun (na,_,t as decl) (na',_,t') (env, acc) ->
	if acc then 
	  (push_rel decl env,
	  (eq_constr t t' || is_conv env sigma t t'))
	else env, acc) g d (env, true))
  with Invalid_argument "List.fold_right2" -> false

let check_eq_context_nolet env sigma (_, _, g as snd) (d, _, _ as fst) =
  if eq_context_nolet env sigma g d then ()
  else errorlabstrm "check_eq_context_nolet"
    (str "Contexts do not agree for composition: "
       ++ pr_context_map env snd ++ str " and " ++ pr_context_map env fst)

let compose_subst ?(sigma=Evd.empty) ((g',p',d') as snd) ((g,p,d) as fst) =
  if debug then check_eq_context_nolet (Global.env ()) sigma snd fst;
  mk_ctx_map sigma g' (specialize_pats p' p) d
(*     (g', (specialize_pats p' p), d) *)

let push_mapping_context (n, b, t as decl) (g,p,d) =
  ((n, Option.map (specialize_constr p) b, specialize_constr p t) :: g,
   (PRel 1 :: map (lift_pat 1) p), decl :: d)
    
let lift_subst evd (ctx : context_map) (g : rel_context) = 
  let map = List.fold_right (fun decl acc -> push_mapping_context decl acc) g ctx in
    check_ctx_map evd map
    
let single_subst evd x p g =
  let t = pat_constr p in
    if eq_constr t (mkRel x) then
      id_subst g
    else if noccur_between 1 x t then
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
      in mk_ctx_map evd substctx pats g
    else
      let (ctx, s, g), _ = strengthen g x t in
      let x' = match nth s (pred x) with PRel i -> i | _ -> error "Occurs check singleton subst"
      and t' = specialize_constr s t in
	(* t' is in ctx. Do the substitution of [x'] by [t] now 
	   in the context and the patterns. *)
      let substctx = subst_in_ctx x' t' ctx in
      let pats = List.map_i (fun i p -> subst_constr_pat x' (lift (-1) t') p) 1 s in
	mk_ctx_map evd substctx pats g
    
exception Conflict
exception Stuck

type 'a unif_result = UnifSuccess of 'a | UnifFailure | UnifStuck
      
let rec unify evd flex g x y =
  if eq_constr x y then id_subst g
  else
    match kind_of_term x with
    | Rel i -> 
      if Int.Set.mem i flex then
	single_subst evd i (PInac y) g
      else raise Stuck
    | _ ->
      match kind_of_term y with
      | Rel i ->
	if Int.Set.mem i flex then
	  single_subst evd i (PInac x) g
	else raise Stuck
      | _ ->
	let (c, l) = decompose_app x 
	and (c', l') = decompose_app y in
	  if isConstruct c && isConstruct c' then
	    if eq_constr c c' then
	      unify_constrs evd flex g l l'
	    else raise Conflict
	  else raise Stuck

and unify_constrs evd flex g l l' = 
  match l, l' with
  | [], [] -> id_subst g
  | hd :: tl, hd' :: tl' ->
    let (d,s,_ as hdunif) = unify evd flex g hd hd' in
    let specrest = map (specialize_constr s) in
    let tl = specrest tl and tl' = specrest tl' in
    let tlunif = unify_constrs evd flex d tl tl' in
      compose_subst ~sigma:evd tlunif hdunif
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
  match p, c with
  | PUVar i, t -> [i, t]
  | PUCstr (c, i, pl), PCstr ((c',u), pl') -> 
      if eq_constructor c c' then
	let params, args = List.chop i pl' in
	  match_patterns pl args
      else raise Conflict
  | PUInac _, _ -> []
  | _, _ -> raise Stuck

and match_patterns pl l =
  match pl, l with
  | [], [] -> []
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
	| Some l, Some l' -> l @ l'
	| _, _ -> raise Stuck)
  | _ -> raise Conflict
      

open Constrintern

let matches (p : user_pats) ((phi,p',g') : context_map) = 
  try
    let p' = filter (fun x -> not (hidden x)) (rev p') in
      UnifSuccess (match_patterns p p')
  with Conflict -> UnifFailure | Stuck -> UnifStuck

let rec match_user_pattern p c =
  match p, c with
  | PRel i, t -> [i, t], []
  | PCstr ((c',_), pl'), PUCstr (c, i, pl) -> 
    if eq_constructor c c' then
      let params, args = List.chop i pl' in
	match_user_patterns args pl
    else raise Conflict
  | PCstr _, PUVar n -> [], [n, p]
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

let lets_of_ctx env ctx evars s =
  let envctx = push_rel_context ctx env in
  let ctxs, pats, varsubst, len, ids = fold_left (fun (ctx', cs, varsubst, k, ids) (id, pat) -> 
    let c = pat_constr pat in
      match pat with
      | PRel i -> (ctx', cs, (i, id) :: varsubst, k, id :: ids)
      | _ -> 
	  let evars', ty = Typing.e_type_of envctx !evars c in
	    (evars := evars';
	     ((Name id, Some (lift k c), lift k ty) :: ctx', (c :: cs), varsubst, succ k, id :: ids)))
    ([],[],[],0,[]) s
  in
  let _, _, ctx' = List.fold_right (fun (n, b, t) (ids, i, ctx') ->
    try ids, pred i, ((Name (List.assoc i varsubst), b, t) :: ctx')
    with Not_found -> 
      let id' = Namegen.next_name_away n ids in
	id' :: ids, pred i, ((Name id', b, t) :: ctx')) ctx (ids, List.length ctx, [])
  in pats, ctxs, ctx'
      
let interp_constr_in_rhs env ctx evars (i,comp,impls) ty s lets c =
  let envctx = push_rel_context ctx env in
  let patslets, letslen = 
    fold_right (fun (n, b, t) (acc, len) -> 
      (lift (-len) (Option.get b) :: acc, succ len)) lets ([], 0) 
  in
  let pats, ctx, len = 
    let (pats, x, y) = lets_of_ctx env (lets @ ctx) evars 
      (map (fun (id, pat) -> id, lift_pat letslen pat) s) 
    in
      pats, x @ y, List.length x 
  in
  let pats = List.map (lift (-letslen)) pats @ map (lift len) patslets in
    match ty with
    | None ->
	let c, _ = interp_constr_evars_impls (push_rel_context ctx env) evars ~impls c 
	in
	let c' = substnl pats 0 c in
	  evars := Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars env !evars;
	  let c' = nf_evar !evars c' in
	    c', Typing.type_of envctx !evars c'
	    
    | Some ty -> 
	let ty' = lift (len + letslen) ty in
	let ty' = nf_evar !evars ty' in
	let c, _ = interp_casted_constr_evars_impls 
	  (push_rel_context ctx env) evars ~impls c ty'
	in
	  evars := Typeclasses.resolve_typeclasses ~filter:Typeclasses.all_evars env !evars;
	  let c' = nf_evar !evars (substnl pats 0 c) in
	    c', nf_evar !evars (substnl pats 0 ty')
	  
let unify_type evars before id ty after =
  try
    let envids = ids_of_rel_context before @ ids_of_rel_context after in
    let envb = push_rel_context before (Global.env()) in
    let IndType (indf, args) = find_rectype envb !evars ty in
    let ind, params = dest_ind_family indf in
    let vs = map (Tacred.whd_simpl envb !evars) args in
    let params = map (Tacred.whd_simpl envb !evars) params in
    let newty = applistc (mkIndU ind) (params @ vs) in
    let cstrs = Inductiveops.type_of_constructors envb ind in
    let cstrs = 
      Array.mapi (fun i ty ->
	let ty = prod_applist ty params in
	let ctx, ty = decompose_prod_assum ty in
	let ctx, ids = 
	  fold_right (fun (n, b, t) (acc, ids) ->
	    match n with
	    | Name id -> let id' = Namegen.next_ident_away id ids in
		((Name id', b, t) :: acc), (id' :: ids)
	    | Anonymous ->
		let x = Namegen.id_of_name_using_hdchar
		  (push_rel_context acc envb) t Anonymous in
		let id = Namegen.next_name_away (Name x) ids in
		  ((Name id, b, t) :: acc), (id :: ids))
	    ctx ([], envids)
	in
	let env' = push_rel_context ctx (Global.env ()) in
	let IndType (indf, args) = find_rectype env' !evars ty in
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
	    let vs' = map (lift ctxclen) vs in
	    let p1 = lift_pats ctxclen (inaccs_of_constrs (rels_of_tele before)) in
	    let flex = flexible (p1 @ q) fullctx in
	    let s = unify_constrs !evars flex fullctx vs' us in
	      UnifSuccess (s, ctxclen, c, cpat)
	  with Conflict -> UnifFailure | Stuck -> UnifStuck) cstrs
    in Some (newty, res)
  with Not_found -> (* not an inductive type *)
    None

let blockers curpats ((_, patcs, _) : context_map) =
  let rec pattern_blockers p c =
    match p, c with
    | PUVar i, t -> []
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
  pr_name (pi1 (lookup_rel i env))


let pr_path evd = prlist_with_sep (fun () -> str":") (pr_existential_key evd)

let eq_path path path' =
  let rec aux path path' =
    match path, path' with
    | [], [] -> true
    | hd :: tl, hd' :: tl' -> Evar.equal hd hd' && aux tl tl'
    | _, _ -> false
  in 
    aux path path'

let pr_splitting env split =
  let rec aux = function
    | Compute (lhs, ty, c) -> 
	let env' = push_rel_context (pi1 lhs) env in
	  hov 2 
	    ((match c with
	     | RProgram c -> str":=" ++ spc () ++
		 print_constr_env env' c ++ str " : " ++
		 print_constr_env env' ty
	     | REmpty i -> str":=!" ++ spc () ++ pr_rel_name (rel_context env') i)
	     ++ spc () ++ str " in context " ++  pr_context_map env lhs)
    | Split (lhs, var, ty, cs) ->
	let env' = push_rel_context (pi1 lhs) env in
	  hov 2
	  (str "Split: " ++ spc () ++ 
	    pr_rel_name (rel_context env') var ++ str" : " ++
	    print_constr_env env' ty ++ spc () ++ 
	    str " in context " ++ pr_context_map env lhs ++ spc () ++ spc () ++
	    Array.fold_left 
	      (fun acc so -> acc ++ 
		 match so with
		 | None -> str "*impossible case*"
		 | Some s -> aux s)
	      (mt ()) cs) ++ spc ()
    | RecValid (id, c) -> 
	hov 2 (str "RecValid " ++ pr_id id ++ aux c)
    | Valid (lhs, ty, ids, ev, tac, cs) ->
	let _env' = push_rel_context (pi1 lhs) env in
	  hov 2 (str "Valid " ++ str " in context " ++ pr_context_map env lhs ++ spc () ++
		   List.fold_left 
		   (fun acc (gl, cl, subst, s) -> acc ++ aux s) (mt ()) cs)
    | Refined (lhs, info, s) -> 
	let (id, c, cty), ty, arg, path, ev, (scf, scargs), revctx, newprob, newty =
	  info.refined_obj, info.refined_rettyp,
	  info.refined_arg, info.refined_path,
	  info.refined_ex, info.refined_app,
	  info.refined_revctx, info.refined_newprob, info.refined_newty
	in
	let env' = push_rel_context (pi1 lhs) env in
	  hov 2 (str "Refined " ++ pr_id id ++ spc () ++ 
	      print_constr_env env' (mapping_constr revctx c) ++ str " : " ++ print_constr_env env' cty ++ spc () ++
	      print_constr_env env' ty ++ spc () ++
	      str " in " ++ pr_context_map env lhs ++ spc () ++
	      str "New problem: " ++ pr_context_map env newprob ++ str " for type " ++
	      print_constr_env (push_rel_context (pi1 newprob) env) newty ++ spc () ++
	      spc () ++ str" eliminating " ++ pr_rel_name (pi1 newprob) arg ++ spc () ++
	      str "Revctx is: " ++ pr_context_map env revctx ++ spc () ++
	      str "New problem to problem substitution is: " ++ 
	      pr_context_map env info.refined_newprob_to_lhs ++ spc () ++
	      aux s)
  in aux split

let ppsplit s =
  pp (pr_splitting (Global.env ()) s)
    
let subst_matches_constr k s c = 
  let rec aux depth c =
    match kind_of_term c with
    | Rel n -> 
 	let k = n - depth in 
	  if k >= 0 then 
	    try lift depth (assoc k s)
	    with Not_found -> c
	  else c
    | _ -> map_constr_with_binders succ aux depth c
  in aux k c

let is_all_variables (delta, pats, gamma) =
  List.for_all (function PInac _ | PHide _ -> true | PRel _ -> true | PCstr _ -> false) pats

let do_renamings ctx =
  let avoid, ctx' =
    List.fold_right (fun (n, b, t) (ids, acc) ->
      match n with
      | Name id -> 
	  let id' = Namegen.next_ident_away id ids in
	  let decl' = (Name id', b, t) in
	    (id' :: ids, decl' :: acc)
      | Anonymous -> assert false)
      ctx ([], [])
  in ctx'

let split_var (env,evars) var delta =
  (* delta = before; id; after |- curpats : gamma *)	    
  let before, (id, b, ty as decl), after = split_tele (pred var) delta in
  let unify = unify_type evars before id ty after in
  let branch = function
    | UnifFailure -> None
    | UnifStuck -> assert false
    | UnifSuccess ((ctx',s,ctx), ctxlen, cstr, cstrpat) ->
	(* ctx' |- s : before ; ctxc *)
	(* ctx' |- cpat : ty *)
	let cpat = specialize s cstrpat in
	let ctx' = do_renamings ctx' in
	(* ctx' |- spat : before ; id *)
	let spat =
	  let ctxcsubst, beforesubst = List.chop ctxlen s in
	    check_ctx_map !evars (ctx', cpat :: beforesubst, decl :: before)
	in
	  (* ctx' ; after |- safter : before ; id ; after = delta *)
	  Some (lift_subst !evars spat after)
  in
    match unify with
    | None -> None
    | Some (newty, unify) ->
	(* Some constructor's type is not refined enough to match ty *)
	if Array.exists (fun x -> x == UnifStuck) unify then
	  None
(* 	  user_err_loc (dummy_loc, "split_var",  *)
(* 		       str"Unable to split variable " ++ pr_name id ++ str" of (reduced) type " ++ *)
(* 			 print_constr_env (push_rel_context before env) newty  *)
(* 		       ++ str" to match a user pattern") *)
	else 
	  let newdelta = after @ ((id, b, newty) :: before) in
	    Some (var, do_renamings newdelta, Array.map branch unify)

let find_empty env delta =
  let r = List.filter (fun v -> 
    match split_var env v delta with
    | None -> false
    | Some (v, _, r) -> Array.for_all (fun x -> x == None) r)
    (CList.init (List.length delta) succ)
  in match r with x :: _ -> Some x | _ -> None
    
open Evd
open Refiner

let rel_of_named_context ctx = 
  List.fold_right (fun (n,b,t) (ctx',subst) ->
    let decl = (Name n, Option.map (subst_vars subst) b, subst_vars subst t) in 
      (decl :: ctx', n :: subst)) ctx ([],[])
    
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

let pats_of_variables = map (fun (i, hide) ->
  if hide then PHide i else PRel i)

let lift_rel_declaration k (n, b, t) =
  (n, Option.map (lift k) b, lift k t)

let named_of_rel_context l =
  let (subst, _, ctx) = 
    List.fold_right
      (fun (na, b, t) (subst, ids, ctx) ->
	 let id = match na with
	   | Anonymous -> raise (Invalid_argument "named_of_rel_context") 
	   | Name id -> Namegen.next_ident_away id ids
	 in
	 let d = (id, Option.map (substl subst) b, substl subst t) in
	   (mkVar id :: subst, id :: ids, d :: ctx))
      l ([], [], [])
  in subst, ctx
    
let lookup_named_i id =
  let rec aux i = function
    | (id',_,_ as decl) :: _ when Id.equal id id' -> i, decl
    | _ :: sign -> aux (succ i) sign
    | [] -> raise Not_found
  in aux 1
	
let instance_of_pats env evars (ctx : rel_context) (pats : (int * bool) list) =
  let subst, nctx = named_of_rel_context ctx in
  let subst = map destVar subst in
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
    List.map_i (fun i (id, b, t) ->
      let i', _ = lookup_named_i id nctx in
	CList.find_map (fun (i'', hide) ->
	  if i'' == i' then Some (if hide then PHide i else PRel i)
	  else None) pats)
      1 ctx'
  in fst (rel_of_named_context ctx'), pats', pats''

let push_rel_context_eos ctx env =
  if named_context env <> [] then
    let env' =
      push_named (id_of_string "eos", Some (Lazy.force coq_end_of_section_constr), 
		 Lazy.force coq_end_of_section) env
    in push_rel_context ctx env'
  else push_rel_context ctx env
    
let split_at_eos ctx =
  List.split_when (fun (id, b, t) ->
		   eq_constr t (Lazy.force coq_end_of_section)) ctx

let pr_problem (id, _, _) env (delta, patcs, _) =
  let env' = push_rel_context delta env in
  let ctx = pr_context env delta in
  pr_id id ++ spc () ++ 
    prlist_with_sep spc (pr_pat env') (List.rev patcs) ++
    (if List.is_empty delta then ctx else fnl () ++ str "In context: " ++ fnl () ++ ctx)

let rel_id ctx n = 
  out_name (pi1 (List.nth ctx (pred n)))

let push_named_context = List.fold_right push_named
      
let rec covering_aux env evars data prev clauses path (ctx,pats,ctx' as prob) lets ty =
  match clauses with
  | ((lhs, rhs), used as clause) :: clauses' -> 
    (match matches lhs prob with
    | UnifSuccess s -> 
      let prevmatch = List.filter (fun ((lhs',rhs'),used) -> matches lhs' prob <> UnifFailure) prev in
	(* 	    if List.exists (fun (_, used) -> not used) prev then *)
	(* 	      user_err_loc (dummy_loc, "equations", str "Unused clause: " ++ pr_clause env (lhs, rhs)); *)
	if List.is_empty prevmatch then
	  let env' = push_rel_context_eos ctx env in
	  let get_var loc i s =
	    match assoc i s with
	    | PRel i -> i
	    | _ -> user_err_loc (loc, "equations", str"Unbound variable " ++ pr_id i)
	  in
	    match rhs with
	    | Program c -> 
	      let c', _ = interp_constr_in_rhs env ctx evars data (Some ty) s lets c in
		Some (Compute (prob, ty, RProgram c'))

	    | Empty (loc,i) ->
	      Some (Compute (prob, ty, REmpty (get_var loc i s)))

	    | Rec ((loc, i), rel, spl) ->
	      let var = rel_id ctx (get_var loc i s) in
	      let tac = 
		match rel with
		| None -> rec_tac var (pi1 data)
		| Some r -> rec_wf_tac var (pi1 data) r
	      in
	      let rhs = By (Inl tac, spl) in
		(match covering_aux env evars data [] [(lhs,rhs),false] path prob lets ty with
		| None -> None
		| Some split -> Some (RecValid (pi1 data, split)))
		  
	    | By (tac, s) ->
	      let sign, t', rels, _, _ = push_rel_context_to_named_context env' ty in
	      let sign = named_context_of_val sign in
	      let sign', secsign = split_at_eos sign in
	      let ids = List.map pi1 sign in
	      let tac = match tac with
		| Inl tac -> 
		  Tacinterp.interp_tac_gen Id.Map.empty ids Tactic_debug.DebugOff tac 
		| Inr tac -> Tacinterp.eval_tactic tac
	      in
	      let env' = reset_with_named_context (val_of_named_context sign) env in
	      let entry, proof = Proofview.init !evars [(env', t')] in
	      let _, res, _, _ = Proofview.apply env' tac proof in
	      let gls = Proofview.V82.goals res in
		evars := gls.sigma;
		if Proofview.finished res then
		  let c = List.hd (Proofview.partial_proof entry res) in
		    Some (Compute (prob, ty, RProgram c))
		else
		  let solve_goal gl =
		    let nctx = named_context_of_val (Goal.V82.hyps !evars gl) in
		    let concl = Goal.V82.concl !evars gl in
		    let nctx, secctx = split_at_eos nctx in
		    let rctx, subst = rel_of_named_context nctx in
		    let ty' = subst_vars subst concl in
		    let ty', prob, subst = match kind_of_term ty' with
		      | App (f, args) -> 
			if eq_constr f (Lazy.force coq_add_pattern) then
			  let comp = args.(1) and newpattern = pat_of_constr args.(2) in
			    if pi2 data (* with_comp *) then
			      let pats = rev_map pat_of_constr (snd (decompose_app comp)) in
			      let newprob = 
				rctx, (newpattern :: pats), rctx
				      (* ((newpatname, None, newpatty) :: ctx') *)
			      in 
			      let ty' = 
				match newpattern with
				| PHide _ -> comp
				| _ -> ty'
			      in ty', newprob, (rctx, pats, ctx)
			    else 
			      let pats =
				let l = pat_vars_list (List.length rctx) in
				  newpattern :: List.tl l
			      in
			      let newprob = rctx, pats, rctx in
				comp, newprob, (rctx, List.tl pats, List.tl rctx)
			else
			  let pats = rev_map pat_of_constr (Array.to_list args) in
			  let newprob = rctx, pats, ctx' in
			    ty', newprob, id_subst ctx'
		      | _ -> raise (Invalid_argument "covering_aux: unexpected output of tactic call")
		    in 
		      match covering_aux env evars data [] (map (fun x -> x, false) s) path prob lets ty' with
		      | None ->
			Errors.anomaly ~label:"covering"
			  (str "Unable to find a covering for the result of a by clause:" 
			   ++ fnl () ++ pr_clause env (lhs, rhs) ++
			     spc () ++ str"refining" ++ spc () ++ pr_context_map env prob)
		      | Some s ->
			let args = rev (List.map_filter (fun (id,b,t) ->
			  if b == None then Some (mkVar id) else None) nctx)
			in gl, args, subst, s
		  in Some (Valid (prob, ty, map pi1 sign', Proofview.V82.of_tactic tac, 
				  (entry, res), map solve_goal gls.it))

	    | Refine (c, cls) -> 
		    (* The refined term and its type *)
	      let cconstr, cty = interp_constr_in_rhs env ctx evars data None s lets c in

	      let vars = variables_of_pats pats in
	      let newctx, pats', pats'' = instance_of_pats env evars ctx vars in
		    (* 		    let _s' = (ctx, vars, newctx) in *)
		    (* revctx is a variable substitution from a reordered context to the
		       current context. Needed for ?? *)
	      let revctx = check_ctx_map !evars (newctx, pats', ctx) in
	      let idref = Namegen.next_ident_away (id_of_string "refine") (ids_of_rel_context newctx) in
	      let decl = (Name idref, None, mapping_constr revctx cty) in
	      let extnewctx = decl :: newctx in
		    (* cmap : Δ -> ctx, cty,
		       strinv associates to indexes in the strenghtened context to
		       variables in the original context.
		    *)
	      let refterm = lift 1 (mapping_constr revctx cconstr) in
	      let cmap, strinv = strengthen ~full:false ~abstract:true extnewctx 1 refterm in
	      let (idx_of_refined, _) = List.find (fun (i, j) -> j = 1) strinv in
	      let newprob_to_lhs =
		let inst_refctx = set_in_ctx idx_of_refined (mapping_constr cmap refterm) (pi1 cmap) in
		let str_to_new =
		  inst_refctx, (specialize_pats (pi2 cmap) (lift_pats 1 pats')), newctx
		in
		  (* 		      let extprob = check_ctx_map (extnewctx, PRel 1 :: lift_pats 1 pats'', extnewctx) in *)
		  (* 		      let ext_to_new = check_ctx_map (extnewctx, lift_pats 1 pats'', newctx) in *)
		  (* (compose_subst cmap extprob) (compose_subst ext_to_new *)
		  compose_subst ~sigma:!evars str_to_new revctx
	      in	
	      let newprob = 
		let ctx = pi1 cmap in
		let pats = 
		  rev_map (fun c -> 
		    let idx = destRel c in
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
		  subst_term refterm
		    (Tacred.simpl env'
		       !evars (lift 1 (mapping_constr revctx ty)))
	      in
	      let newty = mapping_constr cmap newty in
	      (* The new problem forces a reordering of patterns under the refinement
		 to make them match up to the context map. *)
	      let sortinv = List.sort (fun (i, _) (i', _) -> i' - i) strinv in
	      let vars' = List.rev_map snd sortinv in
	      let rec cls' n cls =
		let next_unknown =
		  let str = id_of_string "unknown" in
		  let i = ref (-1) in fun () ->
		    incr i; add_suffix str (string_of_int !i)
		in
		  List.map_filter (fun (lhs, rhs) -> 
		    let oldpats, newpats = List.chop (List.length lhs - n) lhs in
		    let newref, nextrefs = 
		      match newpats with hd :: tl -> hd, tl | [] -> assert false 
		    in
		      match matches_user prob oldpats with
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
				  try Some (List.assoc (pred i) s)
				  with Not_found -> (* The problem is more refined than the user vars*)
				    Some (PUVar (next_unknown ())))
			    vars'
			in
			let newrhs = match rhs with
			  | Refine (c, cls) -> Refine (c, cls' (succ n) cls)
			  | Rec (v, rel, s) -> Rec (v, rel, cls' n s)
			  | By (v, s) -> By (v, cls' n s)
			  | _ -> rhs
			in
			  Some (rev newlhs @ nextrefs, newrhs)
		      | _ -> 
			errorlabstrm "covering"
			  (str "Non-matching clause in with subprogram:" ++ fnl () ++
			     str"Problem is " ++ spc () ++ pr_context_map env prob ++ 
			     str"And the user patterns are: " ++ fnl () ++
			     pr_user_pats env oldpats)) cls
	      in
	      let cls' = cls' 1 cls in
	      let strength_app, refarg =
		let sortinv = List.sort (fun (i, _) (i', _) -> i' - i) strinv in
		let argref = ref 0 in
		let args = 
		  map (fun (i, j) (* i variable in strengthened context, 
				     j variable in the original one *) -> 
		    if j == 1 then (argref := (List.length strinv - i); 
				   cconstr)
		    else let (var, _) = List.nth vars (pred (pred j)) in
			   mkRel var) sortinv
		in args, !argref
	      in
	      let evar = new_untyped_evar () in
	      let path' = evar :: path in
	      let lets' =
		let letslen = length lets in
		let _, ctxs, _ = lets_of_ctx env ctx evars s in
		let newlets = (lift_rel_context (succ letslen) ctxs) 
		  @ (lift_rel_context 1 lets) 
		in specialize_rel_context (pi2 cmap) newlets
	      in
		match covering_aux env evars data [] (map (fun x -> x, false) cls') path' newprob lets' newty with
		| None -> None
		| Some s -> 
		  let info =
		    { refined_obj = (idref, cconstr, cty);
		      refined_rettyp = ty;
		      refined_arg = refarg;
		      refined_path = path';
		      refined_ex = evar;
		      refined_app = (mkEvar (evar, [||]), strength_app);
		      refined_revctx = revctx;
		      refined_newprob = newprob;
		      refined_newprob_to_lhs = newprob_to_lhs;
		      refined_newty = newty }
		  in  Some (Refined (prob, info, s))
	else 
	  anomaly ~label:"covering"
	    (str "Found overlapping clauses:" ++ fnl () ++ pr_clauses env (map fst prevmatch) ++
	       spc () ++ str"refining" ++ spc () ++ pr_context_map env prob)

    | UnifFailure -> covering_aux env evars data (clause :: prev) clauses' path prob lets ty
    | UnifStuck -> 
      let blocks = blockers lhs prob in
	fold_left (fun acc var ->
	  match acc with
	  | None -> 
	    (match split_var (env,evars) var (pi1 prob) with
	    | Some (var, newctx, s) ->
	      let prob' = (newctx, pats, ctx') in
	      let coverrec s = covering_aux env evars data []
		(List.rev prev @ clauses) path (compose_subst ~sigma:!evars s prob')
		(specialize_rel_context (pi2 s) lets)
		(specialize_constr (pi2 s) ty)
	      in
		(try 
		   let rest = Array.map (Option.map (fun x -> 
		     match coverrec x with
		     | None -> raise Not_found
		     | Some s -> s)) s 
		   in Some (Split (prob', var, ty, rest))
		 with Not_found -> None)
	    | None -> None) 
	  | _ -> acc) None blocks)
	    | [] -> (* Every clause failed for the problem, it's either uninhabited or
		       the clauses are not exhaustive *)
	      match find_empty (env,evars) (pi1 prob) with
	      | Some i -> Some (Compute (prob, ty, REmpty i))
	      | None ->
		errorlabstrm "deppat"
		  (str "Non-exhaustive pattern-matching, no clause found for:" ++ fnl () ++
		     pr_problem data env prob)

let covering env evars data (clauses : clause list) prob ty =
  match covering_aux env evars data [] (map (fun x -> (x,false)) clauses) [] prob [] ty with
  | Some cov -> cov
  | None ->
      errorlabstrm "deppat"
	(str "Unable to build a covering for:" ++ fnl () ++
	   pr_problem data env prob)
