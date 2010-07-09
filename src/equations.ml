(* -*- compile-command: "COQBIN=~/research/coq/trunk/bin/ make -k -C .. src/equations_plugin.cma src/equations_plugin.cmxs" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(* $Id: equations.ml4 11996 2009-03-20 01:22:58Z letouzey $ *)

open Cases
open Util
open Names
open Nameops
open Term
open Termops
open Declarations
open Inductiveops
open Environ
open Sign
open Reductionops
open Typeops
open Type_errors
open Pp
open Proof_type

open Rawterm
open Retyping
open Pretype_errors
open Evarutil
open Evarconv
open List
open Libnames
open Topconstr
open Entries

open Tacexpr
open Tactics
open Tacticals
open Tacmach

open Equations_common
open Depelim

let below_tactics_path =
  make_dirpath (List.map id_of_string ["Below";"Equations"])

let below_tac s =
  make_kn (MPfile below_tactics_path) (make_dirpath []) (mk_label s)

let rec_tac h h' = 
  TacArg(TacCall(dummy_loc, 
		Qualid (dummy_loc, qualid_of_string "Equations.Below.rec"),
		[IntroPattern (dummy_loc, Genarg.IntroIdentifier h);
		 IntroPattern (dummy_loc, Genarg.IntroIdentifier h')]))

let rec_wf_tac h h' rel = 
  TacArg(TacCall(dummy_loc, 
		Qualid (dummy_loc, qualid_of_string "Equations.Subterm.rec_wf_eqns_rel"),
		[IntroPattern (dummy_loc, Genarg.IntroIdentifier h);
		 IntroPattern (dummy_loc, Genarg.IntroIdentifier h');
		 ConstrMayEval (ConstrTerm rel)]))

let unfold_recursor_tac () = tac_of_string "Equations.Subterm.unfold_recursor" []

let equations_tac_expr () = 
  (TacArg(TacCall(dummy_loc, Qualid (dummy_loc, qualid_of_string "Equations.DepElim.equations"), [])))

let equations_tac () = tac_of_string "Equations.DepElim.equations" []

let set_eos_tac () = tac_of_string "Equations.DepElim.set_eos" []
    
let solve_rec_tac () = tac_of_string "Equations.Below.solve_rec" []


let pi_tac () = tac_of_string "Equations.Subterm.pi" []

let noconf_tac () = tac_of_string "Equations.NoConfusion.solve_noconf" []

let simpl_equations_tac () = tac_of_string "Equations.DepElim.simpl_equations" []

let solve_equation_tac c = tac_of_string "Equations.DepElim.solve_equation"
  [ConstrMayEval (ConstrTerm (CDynamic (dummy_loc, Pretyping.constr_in (constr_of_global c))))]

let impossible_call_tac c = Tacinterp.glob_tactic
  (TacArg(TacCall(dummy_loc, 
		 Qualid (dummy_loc, qualid_of_string "Equations.DepElim.impossible_call"),
		 [ConstrMayEval (ConstrTerm (CDynamic (dummy_loc, 
						      Pretyping.constr_in (constr_of_global c))))])))

let depelim_tac h = tac_of_string "Equations.DepElim.depelim"
  [IntroPattern (dummy_loc, Genarg.IntroIdentifier h)]

let do_empty_tac h = tac_of_string "Equations.DepElim.do_empty"
  [IntroPattern (dummy_loc, Genarg.IntroIdentifier h)]

let depelim_nosimpl_tac h = tac_of_string "Equations.DepElim.depelim_nosimpl"
  [IntroPattern (dummy_loc, Genarg.IntroIdentifier h)]

let simpl_dep_elim_tac () = tac_of_string "Equations.DepElim.simpl_dep_elim" []

let depind_tac h = tac_of_string "Equations.DepElim.depind"
  [IntroPattern (dummy_loc, Genarg.IntroIdentifier h)]
  
let mkEq t x y = 
  mkApp (Coqlib.build_coq_eq (), [| t; x; y |])

let mkNot t =
  mkApp (Coqlib.build_coq_not (), [| t |])

let mkNot t =
  mkApp (Coqlib.build_coq_not (), [| t |])
      
let mkProd_or_subst (na,body,t) c =
  match body with
    | None -> mkProd (na, t, c)
    | Some b -> subst1 b c

let mkProd_or_clear decl c =
  if not (dependent (mkRel 1) c) then
    subst1 mkProp c
  else mkProd_or_LetIn decl c

let it_mkProd_or_clear ty ctx = 
  fold_left (fun c d -> mkProd_or_clear d c) ty ctx
      
let mkLambda_or_subst (na,body,t) c =
  match body with
    | None -> mkLambda (na, t, c)
    | Some b -> subst1 b c

let mkLambda_or_subst_or_clear (na,body,t) c =
  match body with
  | None when dependent (mkRel 1) c -> mkLambda (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let mkProd_or_subst_or_clear (na,body,t) c =
  match body with
  | None when dependent (mkRel 1) c -> mkProd (na, t, c)
  | None -> subst1 mkProp c
  | Some b -> subst1 b c

let it_mkProd_or_subst ty ctx = 
  nf_beta Evd.empty (whd_betalet Evd.empty
    (List.fold_left (fun c d -> mkProd_or_LetIn d c) ty ctx))

let it_mkLambda_or_subst ty ctx = 
  whd_betalet Evd.empty
    (List.fold_left (fun c d -> mkLambda_or_LetIn d c) ty ctx)

let it_mkLambda_or_subst_or_clear ty ctx = 
  (List.fold_left (fun c d -> mkLambda_or_subst_or_clear d c) ty ctx)

let it_mkProd_or_subst_or_clear ty ctx = 
  (List.fold_left (fun c d -> mkProd_or_subst_or_clear d c) ty ctx)


type pat =
  | PRel of int
  | PCstr of constructor * pat list
  | PInac of constr
  | PHide of int

type user_pat =
  | PUVar of identifier
  | PUCstr of constructor * int * user_pat list
  | PUInac of constr_expr

type user_pats = user_pat list

type context_map = rel_context * pat list * rel_context

let mkInac env c =
  mkApp (Lazy.force coq_inacc, [| Typing.type_of env Evd.empty c ; c |])

let mkHide env c =
  mkApp (Lazy.force coq_hide, [| Typing.type_of env Evd.empty c ; c |])

let rec pat_constr = function
  | PRel i -> mkRel i
  | PCstr (c, p) -> 
      let c' = mkConstruct c in
	mkApp (c', Array.of_list (map pat_constr p))
  | PInac r -> r
  | PHide c -> mkRel c
    
let rec constr_of_pat ?(inacc=true) env = function
  | PRel i -> mkRel i
  | PCstr (c, p) ->
      let c' = mkConstruct c in
	mkApp (c', Array.of_list (constrs_of_pats ~inacc env p))
  | PInac r ->
      if inacc then try mkInac env r with _ -> r else r
  | PHide i -> mkHide env (mkRel i)

and constrs_of_pats ?(inacc=true) env l = map (constr_of_pat ~inacc env) l

let rec pat_vars = function
  | PRel i -> Intset.singleton i
  | PCstr (c, p) -> pats_vars p
  | PInac _ -> Intset.empty
  | PHide _ -> Intset.empty

and pats_vars l =
  fold_left (fun vars p ->
    let pvars = pat_vars p in
    let inter = Intset.inter pvars vars in
      if inter = Intset.empty then
	Intset.union pvars vars
      else error ("Non-linear pattern: variable " ^
		     string_of_int (Intset.choose inter) ^ " appears twice"))
    Intset.empty l

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
      let (ind,_ as cstr) = destConstruct f in
      let nparams, _ = inductive_nargs (Global.env ()) ind in
      let params, args = array_chop nparams args in
      PCstr (cstr, inaccs_of_constrs (Array.to_list params) @ pats_of_constrs (Array.to_list args))
  | Construct f -> PCstr (f, [])
  | _ -> PInac c

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
      if i = k then PInac t
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
	if k = n then (subst_rel_context 0 (lift (-k) c) (rev after)) @ before
	else aux (succ k) (decl :: after) before
  in aux 1 [] ctx

let set_in_ctx (n : int) (c : constr) (ctx : rel_context) : rel_context =
  let rec aux k after = function
    | [] -> []
    | (name, b, t as decl) :: before ->
	if k = n then (rev after) @ (name, Some (lift (-k) c), t) :: before
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

type program = 
  signature * clause list

and signature = identifier * rel_context * constr
  
and clause = lhs * clause rhs
  
and lhs = user_pats

and 'a rhs = 
  | Program of constr_expr
  | Empty of identifier located
  | Rec of identifier located * constr_expr option * 'a list
  | Refine of constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) union * 'a list

type path = int list

type splitting = 
  | Compute of context_map * types * splitting_rhs
  | Split of context_map * int * types * splitting option array
  | Valid of context_map * types * identifier list * tactic *
      (constr list * context_map * splitting) list
  | RecValid of identifier * splitting
  | Refined of context_map * (identifier * constr * types) * types * int *
      path * existential_key * (constr * constr list) * context_map * context_map * types *
      splitting

and splitting_rhs = 
  | RProgram of constr
  | REmpty of int
      
and unification_result = 
  (context_map * int * constr * pat) option

type problem = identifier * lhs

let specialize_mapping_constr (m : context_map) c = 
  specialize_constr (pi2 m) c

let rels_of_tele tele = rel_list 0 (List.length tele)

let patvars_of_tele tele = map (fun c -> PRel (destRel c)) (rels_of_tele tele)

let pat_vars_list n = list_tabulate (fun i -> PRel (succ i)) n

let intset_of_list =
  fold_left (fun s x -> Intset.add x s) Intset.empty

let split_context n c =
  let after, before = list_chop n c in
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
    intset_of_list (list_tabulate (fun i -> x + succ i) (len - x))

let is_fix_proto t =
  match kind_of_term t with
  | App (f, args) when eq_constr f (delayed_force Subtac_utils.fix_proto) ->
      true
  | _ -> false

let fix_rels ctx =
  list_fold_left_i (fun i acc (_, _, t) -> 
    if is_fix_proto t then Intset.add i acc else acc)
    1 Intset.empty ctx

let rec dependencies_of_rel ctx k =
  let (n,b,t) = nth ctx (pred k) in
  let b = Option.map (lift k) b and t = lift k t in
  let bdeps = match b with Some b -> dependencies_of_term ctx b | None -> Intset.empty in
    Intset.union (Intset.singleton k) (Intset.union bdeps (dependencies_of_term ctx t))

and dependencies_of_term ctx t =
  let rels = free_rels t in
    Intset.fold (fun i -> Intset.union (dependencies_of_rel ctx i)) rels Intset.empty

let non_dependent ctx c =
  list_fold_left_i (fun i acc (_, _, t) -> 
    if not (dependent (lift (-i) c) t) then Intset.add i acc else acc)
    1 Intset.empty ctx
        
let strengthen ?(full=true) (ctx : rel_context) x (t : constr) =
  let rels = Intset.union (if full then rels_above ctx x else Intset.singleton x)
    (* (Intset.union *) (Intset.union (dependencies_of_term ctx t) (fix_rels ctx))
    (* (non_dependent ctx t)) *)
  in
  let len = length ctx in
  let nbdeps = Intset.cardinal rels in
  let lifting = len - nbdeps in (* Number of variables not linked to t *)
  let rec aux k n acc m rest s = function
    | decl :: ctx' ->
	if Intset.mem k rels then
	  let rest' = subst_telescope (mkRel (nbdeps + lifting - pred m)) rest in
	    aux (succ k) (succ n) (decl :: acc) m rest' (Inl n :: s) ctx'
	else aux (succ k) n (subst_telescope mkProp acc) (succ m) (decl :: rest) (Inr m :: s) ctx'
    | [] -> rev acc, rev rest, s
  in
  let (min, rest, subst) = aux 1 1 [] 1 [] [] ctx in
  let ctx' = rest @ min in
  let lenrest = length rest in
  let subst = rev subst in
  let reorder = list_map_i (fun i -> function Inl x -> (x + lenrest, i) | Inr x -> (x, i)) 1 subst in
  let subst = map (function Inl x -> PRel (x + lenrest) | Inr x -> PRel x) subst in
    (ctx', subst, ctx), reorder

let id_subst g = (g, rev (patvars_of_tele g), g)
	
let eq_context_nolet env (g : rel_context) (d : rel_context) =
  try 
    snd 
      (List.fold_right2 (fun (na,_,t as decl) (na',_,t') (env, acc) ->
	if acc then 
	  (push_rel decl env,
	  (na = na' && (t = t' || is_conv env Evd.empty t t')))
	else env, acc) g d (env, true))
  with Invalid_argument "List.fold_left2" -> false

let compose_subst ((g',p',d') : context_map) ((g,p,d) : context_map) =
  assert (eq_context_nolet (Global.env ()) g d');
  g', specialize_pats p' p, d

let push_mapping_context (n, b, t as decl) (g,p,d) =
  ((n, Option.map (specialize_constr p) b, specialize_constr p t) :: g,
  (PRel 1 :: map (lift_pat 1) p), decl :: d)
    
let lift_subst (ctx : context_map) (g : rel_context) = 
  List.fold_right (fun decl acc -> push_mapping_context decl acc) g ctx
    
let single_subst x p g =
  let t = pat_constr p in
    if eq_constr t (mkRel x) then
      id_subst g
    else if noccur_between 1 x t then
      (* The term to substitute refers only to previous variables. *)
      let substctx = subst_in_ctx x t g in
      let pats = list_tabulate
      	(fun i -> let k = succ i in
      		    if k = x then (lift_pat (-1) p) else if k > x then PRel (pred k) else PRel k)
      	(List.length g)
      (* let substctx = set_in_ctx x t g in *)
      (* let pats = list_tabulate  *)
      (* 	(fun i -> let k = succ i in if k = x then p else PRel k) *)
      (* 	(List.length g) *)
      in substctx, pats, g
    else
      let (ctx, s, g), _ = strengthen g x t in
      let x' = match nth s (pred x) with PRel i -> i | _ -> error "Occurs check singleton subst"
      and t' = specialize_constr s t in
	(* t' is in ctx. Do the substitution of [x'] by [t] now 
	   in the context and the patterns. *)
      let substctx = subst_in_ctx x' t' ctx in
      let pats = list_map_i (fun i p -> subst_constr_pat x' (lift (-1) t') p) 1 s in
	substctx, pats, g
    
exception Conflict
exception Stuck

type 'a unif_result = UnifSuccess of 'a | UnifFailure | UnifStuck
      
let rec unify flex g x y =
  if eq_constr x y then id_subst g
  else
    match kind_of_term x with
    | Rel i -> 
	if Intset.mem i flex then
	  single_subst i (PInac y) g
	else raise Stuck
    | _ ->
	match kind_of_term y with
	| Rel i ->
	    if Intset.mem i flex then
	      single_subst i (PInac x) g
	    else raise Stuck
	| _ ->
	    let (c, l) = decompose_app x 
	    and (c', l') = decompose_app y in
	      if isConstruct c && isConstruct c' then
		if eq_constr c c' then
		  unify_constrs flex g l l'
		else raise Conflict
	      else raise Stuck

and unify_constrs flex g l l' = 
  match l, l' with
  | [], [] -> id_subst g
  | hd :: tl, hd' :: tl' ->
      let (d,s,_ as hdunif) = unify flex g hd hd' in
      let specrest = map (specialize_constr s) in
      let tl = specrest tl and tl' = specrest tl' in
      let tlunif = unify_constrs flex d tl tl' in
	compose_subst tlunif hdunif
  | _, _ -> raise Conflict

let flexible pats gamma =
  let (_, flex) =
    fold_left2 (fun (k,flex) pat decl ->
      match pat with
      | PInac _ -> (succ k, Intset.add k flex)
      | p -> (succ k, flex))
      (1, Intset.empty) pats gamma
  in flex

let rec accessible = function
  | PRel i -> Intset.singleton i
  | PCstr (c, l) -> accessibles l
  | PInac _ | PHide _ -> Intset.empty

and accessibles l =
  fold_left (fun acc p -> Intset.union acc (accessible p)) 
    Intset.empty l
  
let hidden = function PHide _ -> true | _ -> false

let rec match_pattern p c =
  match p, c with
  | PUVar i, t -> [i, t]
  | PUCstr (c, i, pl), PCstr (c', pl') -> 
      if c = c' then
	let params, args = list_chop i pl' in
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
  | PCstr (c', pl'), PUCstr (c, i, pl) -> 
      if c = c' then
	let params, args = list_chop i pl' in
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
  let ctxs, pats, varsubst, len = fold_left (fun (ctx', cs, varsubst, k) (id, pat) -> 
    let c = pat_constr pat in
      match pat with
      | PRel i -> (ctx', cs, (i, id) :: varsubst, k)
      | _ -> 
	  let ty = Typing.type_of envctx !evars c in
	    ((Name id, Some (lift k c), lift k ty) :: ctx', (c :: cs), varsubst, succ k))
    ([],[],[],0) s
  in
  let ctx' = list_map_i (fun i (n, b, t as decl) ->
    try (Name (List.assoc i varsubst), b, t)
    with Not_found -> decl) 1 ctx
  in pats, ctxs, ctx'
    
let interp_constr_in_rhs env ctx evars (i,comp,impls) ty s lets c =
  let envctx = push_rel_context ctx env in
  let patslets, letslen = 
    fold_right (fun (n, b, t) (acc, len) -> 
      (lift len (Option.get b) :: acc, succ len)) lets ([], 0)
  in
  let pats, ctx, len = 
    let (pats, x, y) = lets_of_ctx env (lets @ ctx) evars 
      (map (fun (id, pat) -> id, lift_pat letslen pat) s) in
      pats, x @ y, List.length x 
  in
  let pats = pats @ map (lift len) patslets in
    match ty with
    | None ->
	let c, _ = interp_constr_evars_impls ~evdref:evars ~fail_evar:false
	  (push_rel_context ctx env) ~impls c 
	in
	let c' = substnl pats 0 c in
	  evars := Typeclasses.resolve_typeclasses ~onlyargs:false env !evars;
	  let c' = nf_evar !evars c' in
	    c', Typing.type_of envctx !evars c'
	    
    | Some ty -> 
	let ty' = lift (len + letslen) ty in
	let ty' = nf_evar !evars ty' in
	let c, _ = interp_casted_constr_evars_impls ~evdref:evars ~fail_evar:false
	  (push_rel_context ctx env) ~impls c ty'
	in
	  evars := Typeclasses.resolve_typeclasses ~onlyargs:false env !evars;
	  let c' = nf_evar !evars (substnl pats 0 c) in
	    c', nf_evar !evars (substnl pats 0 ty')
	  
let unify_type evars before id ty after =
  try
    let envids = ids_of_rel_context before @ ids_of_rel_context after in
    let envb = push_rel_context before (Global.env()) in
    let IndType (indf, args) = find_rectype envb !evars ty in
    let ind, params = dest_ind_family indf in
    let vs = map (Tacred.hnf_constr envb !evars) args in
    let params = map (Tacred.hnf_constr envb !evars) params in
    let newty = applistc (mkInd ind) (params @ vs) in
    let cstrs = Inductiveops.type_of_constructors envb ind in
    let cstrs = 
      Array.mapi (fun i ty ->
	let ty = prod_applist ty params in
	let ctx, ty = decompose_prod_assum ty in
	let ctx, ids = 
	  fold_right (fun (n, b, t) (acc, ids) ->
	    match n with
	    | Name id -> ((n, b, t) :: acc), (id :: ids)
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
	let constr = applist (mkConstruct (ind, succ i), params @ rels_of_tele ctx) in
	let q = inaccs_of_constrs (rels_of_tele ctx) in	
	let constrpat = PCstr ((ind, succ i), inaccs_of_constrs params @ patvars_of_tele ctx) in
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
	    let s = unify_constrs flex fullctx vs' us in
	      UnifSuccess (s, ctxclen, c, cpat)
	  with Conflict -> UnifFailure | Stuck -> UnifStuck) cstrs
    in Some (newty, res)
  with Not_found -> (* not an inductive type *)
    None

let blockers curpats ((_, patcs, _) : context_map) =
  let rec pattern_blockers p c =
    match p, c with
    | PUVar i, t -> []
    | PUCstr (c, i, pl), PCstr (c', pl') -> 
	if c = c' then patterns_blockers pl (snd (list_chop i pl'))
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
    
open Termops

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
    (if delta = [] then ctx else str "[" ++ ctx ++ str "]" ++ spc ())
    ++ prlist_with_sep spc (pr_pat env') (List.rev patcs) ++
      str ": ["  ++ ctx' ++ str "]"

let ppcontext_map context_map = pp (pr_context_map (Global.env ()) context_map)

open Printer
open Ppconstr

let rec pr_user_pat env = function
  | PUVar i -> pr_id i
  | PUCstr (c, i, f) -> 
      let pc = pr_constructor env c in
	if f <> [] then str "(" ++ pc ++ spc () ++ pr_user_pats env f ++ str ")"
	else pc
  | PUInac c -> str "?(" ++ pr_constr_expr c ++ str ")"

and pr_user_pats env pats =
  prlist_with_sep spc (pr_user_pat env) pats

let pr_lhs = pr_user_pats

let pplhs lhs = pp (pr_lhs (Global.env ()) lhs)

let rec pr_rhs env = function
  | Empty (loc, var) -> spc () ++ str ":=!" ++ spc () ++ pr_id var
  | Rec ((loc, var), rel, s) -> spc () ++ str "=>" ++ spc () ++ str"rec " ++ pr_id var ++ spc () ++
      hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | Program rhs -> spc () ++ str ":=" ++ spc () ++ pr_constr_expr rhs
  | Refine (rhs, s) -> spc () ++ str "<=" ++ spc () ++ pr_constr_expr rhs ++ 
      spc () ++ str "=>" ++ spc () ++
      hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inl tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_raw_tactic env tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inr tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_glob_tactic env tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")
      
and pr_clause env (lhs, rhs) =
  pr_lhs env lhs ++ pr_rhs env rhs

and pr_clauses env =
  prlist_with_sep fnl (pr_clause env)

let ppclause clause = pp(pr_clause (Global.env ()) clause)
    
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
	  let ctxcsubst, beforesubst = list_chop ctxlen s in
	    (ctx', cpat :: beforesubst, decl :: before)
	in
	  (* ctx' ; after |- safter : before ; id ; after = delta *)
	  Some (lift_subst spat after)
  in
    match unify with
    | None -> None
    | Some (newty, unify) ->
	(* Some constructor's type is not refined enough to match ty *)
	if array_exists (fun x -> x = UnifStuck) unify then
	  user_err_loc (dummy_loc, "split_var", 
		       str"Unable to split variable " ++ pr_name id ++ str" of (reduced) type " ++
			 print_constr_env (push_rel_context before env) newty 
		       ++ str" to match a user pattern")
	else 
	  let newdelta = after @ ((id, b, newty) :: before) in
	    Some (var, newdelta, Array.map branch unify)

let split env vars delta =
  let split = fold_left (fun acc var ->
    match acc with 
    | None -> split_var env var delta 
    | _ -> acc) None vars
  in split

let find_empty env delta =
  let r = List.filter (fun v -> 
    match split_var env v delta with
    | None -> false
    | Some (v, _, r) -> array_for_all (fun x -> x = None) r)
    (list_tabulate (fun i -> succ i) (List.length delta))
  in match r with x :: _ -> Some x | _ -> None
    
open Evd
open Refiner

let rel_of_named_context ctx = 
  List.fold_right (fun (n,b,t) (ctx',subst) ->
    let decl = (Name n, Option.map (subst_vars subst) b, subst_vars subst t) in 
      (decl :: ctx', n :: subst)) ctx ([],[])
    
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
  List.fold_right
    (fun (na, b, t) (subst, ctx) ->
      let id = match na with Anonymous -> raise (Invalid_argument "named_of_rel_context") | Name id -> id in
      let d = (id, Option.map (substl subst) b, substl subst t) in
	(mkVar id :: subst, d :: ctx))
    l ([], [])
    
let lookup_named_i id =
  let rec aux i = function
    | (id',_,_ as decl) :: _ when id=id' -> i, decl
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
    list_map_i (fun i id ->
      let i', _ = lookup_named_i id ctx' in
	list_try_find (fun (i'', hide) ->
	  if i'' = i then if hide then PHide i' else PRel i'
	  else failwith "") pats)
      1 subst
  in
  let pats'' =
    list_map_i (fun i (id, b, t) ->
      let i', _ = lookup_named_i id nctx in
	list_try_find (fun (i'', hide) ->
	  if i'' = i' then if hide then PHide i else PRel i
	  else failwith "") pats)
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
  fst (list_split_when (fun (id, b, t) ->
    eq_constr t (Lazy.force coq_end_of_section)) ctx)

let rec covering_aux env evars data prev (clauses : clause list) path (ctx,pats,ctx' as prob) lets ty =
  match clauses with
  | (lhs, rhs as clause) :: clauses' -> 
      (match matches lhs prob with
      | UnifSuccess s -> 
	  let prevmatch = List.filter (fun (lhs',rhs') -> matches lhs' prob <> UnifFailure) prev in
	    if prevmatch = [] then
	      let env' = push_rel_context_eos ctx env in
		match rhs with
		| Program c -> 
		    let c', _ = interp_constr_in_rhs env ctx evars data (Some ty) s lets c in
		      Some (Compute (prob, ty, RProgram c'))

		| Empty (loc,i) ->
		    (match assoc i s with
		    | PRel i -> Some (Compute (prob, ty, REmpty i))
		    | _ -> user_err_loc (loc, "equations", str"Unbound variable " ++ pr_id i))

		| Rec (v, rel, spl) ->
		    let tac = 
		      match rel with 
		      | None -> rec_tac (snd v) (pi1 data)
		      | Some r -> rec_wf_tac (snd v) (pi1 data) r
		    in
		    let rhs = By (Inl tac, spl) in
		      (match covering_aux env evars data [] [(lhs,rhs)] path prob lets ty with
		      | None -> None
		      | Some split -> Some (RecValid (pi1 data, split)))
					    
		| By (tac, s) ->
		    let sign, t', rels = push_rel_context_to_named_context env' ty in
		    let sign' = split_at_eos (named_context_of_val sign) in
		    let ids = List.map pi1 sign' in
		    let tac = match tac with
		      | Inl tac -> Tacinterp.interp_tac_gen [] ids Tactic_debug.DebugOff tac 
		      | Inr tac -> Tacinterp.eval_tactic tac
		    in
		      (* New trunk *)
(* 		    let goal = {it = make_evar sign t'; sigma = !evars } in *)
		    let goal, ev, evars' = Goal.V82.mk_goal !evars sign t' Store.empty in
		    let goals = {it = goal; sigma = evars'} in
		    let gls = tac goals in
		      if gls.it = [] then 
(* 			let pftree = valid [] in *)
(* 			let c, _ = extract_open_proof !evars pftree in *)
			let c = Evd.existential_value gls.sigma (destEvar ev) in
			  Some (Compute (prob, ty, RProgram c))
		      else
			let solve_goal evi =
(* 			  let nctx = named_context_of_val evi.evar_hyps in *)
(* 			  let concl = evi.evar_concl in *)
			  Goal.bind Goal.hyps (fun nctx -> Goal.bind Goal.concl (fun concl ->
			  let nctx = split_at_eos (named_context_of_val nctx) in
			  let rctx, subst = rel_of_named_context nctx in
			  let ty' = subst_vars subst concl in
			  let ty', prob, subst = match kind_of_term ty' with
			    | App (f, args) -> 
				if eq_constr f (Lazy.force coq_add_pattern) then
				  let comp = args.(1) and newpattern = pat_of_constr args.(2) in
				    if pi2 data then
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
			    match covering_aux env evars data [] s path prob lets ty' with
			      | None ->
				  anomalylabstrm "covering"
				    (str "Unable to find a covering for the result of a by clause:" 
				      ++ fnl () ++ pr_clause env clause ++
				      spc () ++ str"refining" ++ spc () ++ pr_context_map env prob)
			      | Some s ->
				  let args = rev (list_map_filter (fun (id,b,t) ->
				    if b = None then Some (mkVar id) else None) nctx) 
				  in Goal.return (args, subst, s)))
			in Some (Valid (prob, ty, ids, tac, 
					map (fun evi -> 
					       fst (Goal.eval (solve_goal evi) env evars' goal)) gls.it))


		| Refine (c, cls) -> 
		    let _, ctxs, _ = lets_of_ctx env ctx evars s in
		    let vars = variables_of_pats pats in
		    let newctx, pats', pats'' = instance_of_pats env evars ctx vars in
		    let _s' = (ctx, vars, newctx) in
		    let revctx = (newctx, pats', ctx) in
		    let cconstr, cty = interp_constr_in_rhs env ctx evars data None s lets c in
		    let idref = Namegen.next_ident_away (id_of_string "refine") (ids_of_rel_context newctx) in
		    let decl = (Name idref, None, mapping_constr revctx cty) in
		    let extnewctx = decl :: newctx in
		      (* cmap : Δ -> ctx, cty *)
		    let cmap, strinv = strengthen ~full:true extnewctx 1
		      (lift 1 (mapping_constr revctx cconstr)) 
		    in
 		    let cconstr' = mapping_constr cmap cconstr in
		    let cty' = mapping_constr cmap cty in
		    let newprob = (extnewctx, PRel 1 :: lift_pats 1 pats'', extnewctx) in
		    let newprob = compose_subst cmap newprob in
		    let refterm = lift 1 (mapping_constr revctx cconstr) in
		    let newty = subst_term_occ all_occurrences refterm
		      (Tacred.simpl (push_rel_context extnewctx env) !evars (lift 1 (mapping_constr revctx ty)))
		    in
		    let newty = mapping_constr cmap newty in
		    let rec cls' n cls =
		      list_map_filter (fun (lhs, rhs) -> 
			let oldpats, newpats = list_chop (List.length lhs - n) lhs in
			  match matches_user prob oldpats with
			  | UnifSuccess (s, alias) -> 
			      (* A substitution from the problem variables to user patterns and 
				 from user pattern variables to patterns *)
			      let newlhs = 
				list_map_filter 
				  (fun (i, hide) ->
				    if hide then None
				    else
				      try Some (List.assoc i s)
				      with Not_found -> (* The problem is more refined than the user vars*)
					Some (PUVar (id_of_string "unknown")))
				  vars
			      in
			      let newrhs = match rhs with
				| Refine (c, cls) -> Refine (c, cls' (succ n) cls)
				| Rec (v, rel, s) -> Rec (v, rel, cls' n s)
				| By (v, s) -> By (v, cls' n s)
				| _ -> rhs
			      in
				Some (rev (rev newpats @ newlhs), newrhs)
			  | _ -> 
			      errorlabstrm "covering"
				(str "Non-matching clause in with subprogram:" ++ fnl () ++
				    str"Problem is " ++ spc () ++ pr_context_map env prob ++ 
				    str"And the user patterns are: " ++ fnl () ++
				    pr_user_pats env lhs)) cls
		    in
		    let cls' = cls' 1 cls in
		    let strength_app, refarg =
		      let sortinv = List.sort (fun (i, _) (i', _) -> i' - i) strinv in
		      let argref = ref 0 in
		      let args = 
			map (fun (i, j) (* i variable in strengthened context, 
					   j variable in the original one *) -> 
			  if j = 1 then (argref := (List.length strinv - i); 
					 cconstr)
			  else let (var, _) = List.nth vars (pred (pred j)) in
				 mkRel var) sortinv
		      in args, !argref
		    in
		    let evar = new_untyped_evar () in
		    let path' = evar :: path in
		    let lets' =
		      let letslen = length lets in
		      let newlets = (lift_rel_context (succ letslen) ctxs) 
			@ (lift_rel_context 1 lets) 
		      in specialize_rel_context (pi2 cmap) newlets
		    in
		      match covering_aux env evars data [] cls' path' newprob lets' newty with
		      | None -> None
		      | Some s -> 
			  Some (Refined (prob, (idref, cconstr', cty'),
					ty, refarg, path', evar,
					(mkEvar (evar, [||]), strength_app),
					revctx, newprob, newty, s))
	    else 
	      anomalylabstrm "covering"
		(str "Found overlapping clauses:" ++ fnl () ++ pr_clauses env prevmatch ++
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
			(List.rev prev @ clauses) path (compose_subst s prob')
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
		pr_context_map env prob)

let covering env evars data (clauses : clause list) prob ty =
  match covering_aux env evars data [] clauses [] prob [] ty with
  | Some cov -> cov
  | None ->
      errorlabstrm "deppat"
	(str "Unable to build a covering for:" ++ fnl () ++
	    pr_context_map env prob)
    
open Evd
open Evarutil

let helper_evar isevar evar env typ src =
  let sign, typ', instance = push_rel_context_to_named_context env typ in
  let evm' = evar_declare sign evar typ' ~src !isevar in
    isevar := evm'; mkEvar (evar, Array.of_list instance)

let gen_constant dir s = Coqlib.gen_constant "equations" dir s

let coq_zero = lazy (gen_constant ["Init"; "Datatypes"] "O")
let coq_succ = lazy (gen_constant ["Init"; "Datatypes"] "S")
let coq_nat = lazy (gen_constant ["Init"; "Datatypes"] "nat")

let rec coq_nat_of_int = function
  | 0 -> Lazy.force coq_zero
  | n -> mkApp (Lazy.force coq_succ, [| coq_nat_of_int (pred n) |])

let term_of_tree status isevar env (i, delta, ty) ann tree =
  let oblevars = ref Intset.empty in
  let helpers = ref [] in
  let rec aux = function
    | Compute ((ctx, _, _), ty, RProgram rhs) -> 
	let body = it_mkLambda_or_LetIn rhs ctx and typ = it_mkProd_or_subst ty ctx in
	  body, typ

    | Compute ((ctx, _, _), ty, REmpty split) ->
	let split = (Name (id_of_string "split"), 
		    Some (coq_nat_of_int (succ (length ctx - split))),
		    Lazy.force coq_nat)
	in
	let ty' = it_mkProd_or_LetIn ty ctx in
	let let_ty' = mkLambda_or_LetIn split (lift 1 ty') in
	let term = e_new_evar isevar env ~src:(dummy_loc, QuestionMark (Define true)) let_ty' in
	let ev = fst (destEvar term) in
	  oblevars := Intset.add ev !oblevars;
	  term, ty'
	   
    | RecValid (id, rest) -> aux rest

    | Refined ((ctx, _, _), (id, c, _), ty, rarg, path, ev, (f, args), revctx, newprob, newty, rest) ->
	let sterm, sty = aux rest in
	let term, ty = 
	  let term = mkLetIn (Name (id_of_string "prog"), sterm, sty, lift 1 sty) in
	  let term = helper_evar isevar ev (Global.env ()) term (dummy_loc, QuestionMark (Define false)) in
	    oblevars := Intset.add ev !oblevars;
	    helpers := (ev, rarg) :: !helpers;
	    term, ty
	in
	let term = applist (f, args) in
	let term = it_mkLambda_or_LetIn term ctx in
	let ty = it_mkProd_or_subst ty ctx in
	  term, ty

    | Valid ((ctx, _, _), ty, substc, tac, rest) ->
(* 	let goal_of_rest goal args (term, ty) =  *)
(* 	  { open_subgoals = 0; *)
(* 	    goal = goal; *)
(* 	    ref = Some (Prim (Proof_type.Refine (applistc term args)), []) } *)
(* 	in *)
	let c, _ = assert false (* Goal.eval gl (Global.env ()) !isevar gl.it  *)in
(* 	  valid (map (fun (goal, gls) -> *)
(* 				   let (args, subst, x), isevar = Goal.eval gls (Global.env ()) !isevar goal in *)
(* 				     goal_of_rest goal args (aux x))  *)
(* 			      rest)  *)
(* 	in *)
(* 	let c, _ = extract_open_proof !isevar pftree in *)
	  it_mkLambda_or_LetIn (subst_vars substc c) ctx, it_mkProd_or_LetIn ty ctx

    | Split ((ctx, _, _), rel, ty, sp) -> 
	let before, decl, after = split_tele (pred rel) ctx in
	let branches = 
	  Array.map (fun split -> 
	    match split with
	    | Some s -> aux s
	    | None ->
		(* dead code, inversion will find a proof of False by splitting on the rel'th hyp *)
		coq_nat_of_int rel, Lazy.force coq_nat)
	    sp 
	in
	let branches_ctx =
	  Array.mapi (fun i (br, brt) -> (id_of_string ("m_" ^ string_of_int i), Some br, brt))
	    branches
	in
	let n, branches_lets =
	  Array.fold_left (fun (n, lets) (id, b, t) ->
	    (succ n, (Name id, Option.map (lift n) b, lift n t) :: lets))
	    (0, []) branches_ctx
	in
	let liftctx = lift_context (Array.length branches) ctx in
	let case =
	  let ty = it_mkProd_or_LetIn ty liftctx in
	  let ty = it_mkLambda_or_LetIn ty branches_lets in
	  let nbbranches = (Name (id_of_string "branches"),
			   Some (coq_nat_of_int (length branches_lets)),
			   Lazy.force coq_nat)
	  in
	  let nbdiscr = (Name (id_of_string "target"),
			Some (coq_nat_of_int (length before)),
			Lazy.force coq_nat)
	  in
	  let ty = it_mkLambda_or_LetIn (lift 2 ty) [nbbranches;nbdiscr] in
	  let term = e_new_evar isevar env ~src:(dummy_loc, QuestionMark status) ty in
	  let ev = fst (destEvar term) in
	    oblevars := Intset.add ev !oblevars;
	    term
	in       
	let casetyp = it_mkProd_or_subst ty ctx in
	  mkCast(case, DEFAULTcast, casetyp), casetyp
  in 
  let term, typ = aux tree in
    !helpers, !oblevars, term, typ

open Constrintern
open Decl_kinds

type pat_expr = 
  | PEApp of identifier located * pat_expr located list
  | PEWildcard
  | PEInac of constr_expr
  | PEPat of cases_pattern_expr

type user_pat_expr = pat_expr located

type user_pat_exprs = user_pat_expr located

type input_pats =
  | SignPats of user_pat_expr list
  | RefinePats of user_pat_expr list

type pre_equation = 
  identifier located option * input_pats * pre_equation rhs

let next_ident_away s ids =
  let n' = Namegen.next_ident_away s !ids in
    ids := n' :: !ids; n'

let rec ids_of_pats pats =
  fold_left (fun ids (_,p) ->
    match p with
    | PEApp ((loc,f), l) -> (f :: ids_of_pats l) @ ids
    | PEWildcard -> ids
    | PEInac _ -> ids
    | PEPat _ -> ids)
    [] pats
    
type rec_type = 
  | Structural
  | Logical of (constant * constr * constant) (* comp, comp applied to rels, comp projection *)

let lift_constrs n cs = map (lift n) cs

let list_try_find_i f i l =
  snd 
    (fold_left (fun (i, acc) x ->
      match acc with
      | None -> (succ i, f i x)
      | Some _ -> (i, acc))
	(i, None) l)
    
let array_remove_last a =
  Array.sub a 0 (Array.length a - 1)

let array_chop_last a =
  array_chop (Array.length a - 1) a

let abstract_rec_calls ?(do_subst=true) is_rec len protos c =
  let lenprotos = length protos in
  let proto_fs = map (fun (f, _, _, _) -> f) protos in
  let find_rec_call f =
    try Some (List.find (fun (f', alias, idx, arity) ->
      eq_constr (fst (decompose_app f')) f || alias = Some f) protos) 
    with Not_found -> None
  in
  let find_rec_call f args =
    match find_rec_call f with
    | Some (f', _, i, arity) -> 
	let args' = snd (array_chop (length (snd (decompose_app f'))) args) in
	Some (i, arity, args')
    | None -> 
	match is_rec with
	| Some (Logical (c, capp, proj)) when eq_constr (mkConst proj) f -> 
	    Some (lenprotos - 1, capp, array_remove_last args)
	| _ -> None
  in
  let rec aux n c =
    match kind_of_term c with
    | App (f', args) ->
	let (ctx, lenctx, args) = 
	  Array.fold_left (fun (ctx,len,c) arg -> 
	    let ctx', lenctx', arg' = aux n arg in
	    let len' = lenctx' + len in
	    let ctx'' = lift_context len ctx' in
	    let c' = (liftn len (succ lenctx') arg') :: map (lift lenctx') c in
	      (ctx''@ctx, len', c'))
	    ([],0,[]) args
	in
	let args = Array.of_list (List.rev args) in
	let f' = lift lenctx f' in
	  (match find_rec_call f' args with
	  | Some (i, arity, args') ->
	      let resty = substl (rev (Array.to_list args')) arity in
	      let result = (Name (id_of_string "recres"), Some (mkApp (f', args)), resty) in
	      let hypty = mkApp (mkApp (mkRel (i + len + lenctx + 2 + n), 
				       Array.map (lift 1) args'), [| mkRel 1 |]) 
	      in
	      let hyp = (Name (id_of_string "Hind"), None, hypty) in
		[hyp;result]@ctx, lenctx + 2, mkRel 2
	  | None -> (ctx, lenctx, mkApp (f', args)))

    (* | Cast (_, _, f) when is_comp f -> aux n f *)
	  
    | LetIn (na,b,t,c) ->
	let ctx',lenctx',b' = aux n b in
	let ctx'',lenctx'',c' = aux (succ n) c in
	let ctx'' = lift_rel_contextn 1 lenctx' ctx'' in
	let fullctx = ctx'' @ [na,Some b',lift lenctx' t] @ ctx' in
	  fullctx, lenctx'+lenctx''+1, liftn lenctx' (lenctx'' + 2) c'

    | Prod (na, d, c) when not (dependent (mkRel 1) c)  -> 
	let ctx',lenctx',d' = aux n d in
	let ctx'',lenctx'',c' = aux n (subst1 mkProp c) in
	  lift_context lenctx' ctx'' @ ctx', lenctx' + lenctx'', 
	mkProd (na, lift lenctx'' d', 
	       liftn lenctx' (lenctx'' + 2) 
		 (lift 1 c'))

    | Case (ci, p, c, br) ->
	let ctx', lenctx', c' = aux n c in
	let case' = mkCase (ci, lift lenctx' p, c', Array.map (lift lenctx') br) in
	  ctx', lenctx', substnl proto_fs (succ len + lenctx') case'

    | _ -> [], 0, if do_subst then (substnl proto_fs (len + n) c) else c
  in aux 0 c

let below_transparent_state () =
  Auto.Hint_db.transparent_state (Auto.searchtable_map "Below")

let simpl_star = 
  tclTHEN simpl_in_concl (onAllHyps (fun id -> simpl_in_hyp (id, InHyp)))

let eauto_with_below l =
  Class_tactics.typeclasses_eauto
    ~st:(below_transparent_state ()) (l@["subterm_relation"; "Below"])

let simp_eqns l =
  tclREPEAT (tclTHENLIST [Autorewrite.autorewrite tclIDTAC l;
			  (* simpl_star; Autorewrite.autorewrite tclIDTAC l; *)
			  tclTRY (eauto_with_below l)])

let simp_eqns_in clause l =
  tclREPEAT (tclTHENLIST 
		[Autorewrite.auto_multi_rewrite l clause;
		 tclTRY (eauto_with_below l)])

let autorewrites b = tclREPEAT (Autorewrite.autorewrite tclIDTAC [b])

let autorewrite_one b = Rewrite.cl_rewrite_clause_strat 
  (Rewrite.one_subterm (Rewrite.Strategies.hints b))
  None

type term_info = {
  base_id : string;
  helpers_info : (existential_key * int * identifier) list }

let find_helper_info info f =
  try List.find (fun (ev', arg', id') ->
    eq_constr (global_reference id') f) info.helpers_info
  with Not_found -> anomaly "Helper not found while proving induction lemma."

let find_helper_arg info f args =
  let (ev, arg, id) = find_helper_info info f in
    ev, args.(arg)
      
let find_splitting_var pats var constrs =
  let rec find_pat_var p c =
    match p, decompose_app c with
    | PRel i, (c, l) when i = var -> Some (destVar c)
    | PCstr (c, ps), (f,l) -> aux ps l
    | _, _ -> None
  and aux pats constrs =
    List.fold_left2 (fun acc p c ->
      match acc with None -> find_pat_var p c | _ -> acc)
      None pats constrs
  in
    Option.get (aux (rev pats) constrs)

let rec aux_ind_fun info = function
  | Split ((ctx,pats,_), var, _, splits) ->
      tclTHEN_i (fun gl ->
	match kind_of_term (pf_concl gl) with
	| App (ind, args) -> 
	    let pats' = list_drop_last (Array.to_list args) in
	    let pats = filter (fun x -> not (hidden x)) pats in
	    let id = find_splitting_var pats var pats' in
	      depelim_nosimpl_tac id gl
	| _ -> tclFAIL 0 (str"Unexpected goal in functional induction proof") gl)
	(fun i -> 
	  match splits.(pred i) with
	  | None -> simpl_dep_elim_tac ()
	  | Some s ->
	      tclTHEN (simpl_dep_elim_tac ())
		(aux_ind_fun info s))
	  
  | Valid ((ctx, _, _), ty, substc, tac, rest) -> tclTHEN intros
      (tclTHEN_i tac (fun i -> let _, subst, split = nth rest (pred i) in
				 tclTHEN (Lazy.force unfold_add_pattern) 
				   (aux_ind_fun info split)))
      
  | RecValid (id, cs) -> aux_ind_fun info cs
      
  | Refined ((ctx, _, _), (id, c, ty), _, _, _, _, _, _, newprob, newty, s) -> 
      let elimtac gl =
	match kind_of_term (pf_concl gl) with
	| App (ind, args) ->
	    let last_arg = args.(Array.length args - 1) in
	    let f, args = destApp last_arg in
	    let _, elim = find_helper_arg info f args in
	      tclTHENLIST
		[letin_tac None (Name id) elim None allHypsAndConcl; 
		 clear_body [id]; aux_ind_fun info s] gl
	| _ -> tclFAIL 0 (str"Unexpected refinement goal in functional induction proof") gl
      in
      let cstrtac =
	tclTHENLIST [tclTRY (autorewrite_one info.base_id); any_constructor false None]
      in tclTHENLIST [ intros; tclTHENLAST cstrtac (tclSOLVE [elimtac]); solve_rec_tac ()]
	
  | Compute (_, _, _) ->
      tclTHENLIST [intros; simp_eqns [info.base_id]]
	
  (* | Compute ((ctx,_,_), _, REmpty id) -> *)
  (*     let (na,_,_) = nth ctx (pred id) in *)
  (*     let id = out_name na in *)
  (* 	do_empty_tac id *)

let ind_fun_tac is_rec f info fid split ind =
  if is_rec = Some Structural then
    let c = constant_value (Global.env ()) (destConst f) in
    let i = let (inds, _), _ = destFix c in inds.(0) in
    let recid = add_suffix fid "_rec" in
      (* tclCOMPLETE  *)
      (tclTHENLIST
	  [fix (Some recid) (succ i);
	   onLastDecl (fun (n,b,t) gl ->
	     let sort = pf_type_of gl t in
	     let fixprot = mkApp (delayed_force Subtac_utils.fix_proto, [|sort; t|]) in
	       change_in_hyp None fixprot (n, InHyp) gl);
	   intros; aux_ind_fun info split])
  else tclCOMPLETE (tclTHEN intros (aux_ind_fun info split))
    
let mapping_rhs s = function
  | RProgram c -> RProgram (mapping_constr s c)
  | REmpty i -> 
      try match nth (pi2 s) (pred i) with 
      | PRel i' -> REmpty i'
      | _ -> assert false
      with Not_found -> assert false

let map_rhs f g = function
  | RProgram c -> RProgram (f c)
  | REmpty i -> REmpty (g i)

let clean_clause (ctx, pats, ty, c) =
  (ctx, pats, ty, 
  map_rhs (nf_beta Evd.empty) (fun x -> x) c)

let map_evars_in_constr evar_map c = 
  evar_map (fun id -> 
    constr_of_global (Nametab.locate (Libnames.make_short_qualid id))) c

let map_split f split =
  let rec aux = function
    | Compute (lhs, ty, RProgram c) -> Compute (lhs, ty, RProgram (f c))
    | Split (lhs, y, z, cs) -> Split (lhs, y, z, Array.map (Option.map aux) cs)
    | RecValid (id, c) -> RecValid (id, aux c)
    | Valid (lhs, y, z, w, cs) ->
	Valid (lhs, y, z, w, List.map (fun (cl, subst, s) -> (cl, subst, aux s)) cs)
    | Refined (lhs, (id, c, cty), ty, arg, path, ev, (scf, scargs), revctx, newprob, newty, s) -> 
	Refined (lhs, (id, f c, f cty), ty, arg, path, ev,
		(f scf, List.map f scargs), revctx, newprob, newty, aux s)
    | Compute (_, _, REmpty _) as c -> c
  in aux split

let map_evars_in_split m = map_split (map_evars_in_constr m)

let subst_rec_split f prob s split = 
  let subst_rec cutprob s (ctx, _, _ as lhs) =
    let subst = 
      fold_left (fun (ctx, _, _ as lhs) (id, b) ->
	let n, _, _ = lookup_rel_id id ctx in
	let substf = single_subst n (PInac b) ctx in
	  compose_subst substf lhs) (id_subst ctx) s
    in
      subst, compose_subst subst (compose_subst lhs cutprob)
  in
  let rec aux cutprob s = function
    | Compute ((ctx,pats,del as lhs), ty, c) ->
	let subst, lhs' = subst_rec cutprob s lhs in	  
	  Compute (lhs', mapping_constr subst ty, mapping_rhs subst c)
	  
    | Split (lhs, x, y, cs) -> 
	let subst, lhs' = subst_rec cutprob s lhs in
	  Split (lhs', x, y, Array.map (Option.map (aux cutprob s)) cs)
	  
    | RecValid (id, c) ->
	RecValid (id, aux cutprob s c)
	  
    | Refined (lhs, (id, constr, cty), ty, arg, path, ev, (fev, args), revctx, newprob, newty, sp) -> 
	let subst, lhs' = subst_rec cutprob s lhs in
        let _, revctx' = subst_rec (id_subst (pi3 revctx)) s revctx in
	let cutnewprob = 
	  let (ctx, pats, ctx') = newprob in
	    (ctx, list_drop_last pats, list_drop_last ctx')
	in
	let subst', newprob' = subst_rec cutnewprob s newprob in
	let sc' = 
	  let recprots, args = list_chop (List.length s) args in
	    (mapping_constr subst (applist (fev, recprots)),
	    map (mapping_constr subst) args)
	in
	  Refined (lhs', (id, mapping_constr subst constr, mapping_constr subst cty),
		  mapping_constr subst ty, arg - List.length s, path, ev, sc', 
		  revctx',
		  newprob', mapping_constr subst' newty, 
		  aux cutnewprob s sp)

    | Valid (lhs, x, y, w, cs) -> 
	let subst, lhs' = subst_rec cutprob s lhs in
	  Valid (lhs', x, y, w,
		List.map (fun (l, subst, sp) -> (l, subst, aux cutprob s sp)) cs)
  in aux prob s split

type statement = constr * types option
type statements = statement list

let subst_app f fn c = 
  let rec aux n c =
    match kind_of_term c with
    | App (f', args) when eq_constr f f' -> fn n f' args
    | _ -> map_constr_with_binders succ aux n c
  in aux 0 c
  
let subst_comp_proj f proj c =
  subst_app proj (fun n x args -> 
    mkApp (f, Array.sub args 0 (Array.length args - 1)))
    c

let subst_comp_proj_split f proj s =
  map_split (subst_comp_proj f proj) s

let reference_of_id s = 
  Ident (dummy_loc, s)

let clear_ind_assums ind ctx = 
  let rec clear_assums c =
    match kind_of_term c with
    | Prod (na, b, c) ->
	let t, _ = decompose_app b in
	  if isInd t then
	    let ind', _ = destInd t in
	      if ind' = ind then (
		assert(not (dependent (mkRel 1) c));
		clear_assums (subst1 mkProp c))
	      else mkProd (na, b, clear_assums c)
	  else mkProd (na, b, clear_assums c)
    | LetIn (na, b, t, c) ->
	mkLetIn (na, b, t, clear_assums c)
    | _ -> c
  in map_rel_context clear_assums ctx

let unfold s = Tactics.unfold_in_concl [all_occurrences, s]

let ind_elim_tac indid inds info gl = 
  let eauto = Class_tactics.typeclasses_eauto [info.base_id; "funelim"] in
  let _nhyps = List.length (pf_hyps gl) in
  let prove_methods tac gl = 
    tclTHEN tac eauto gl
  in
  let rec applyind args gl =
    match kind_of_term (pf_concl gl) with
    | LetIn (Name id, b, t, t') ->
	tclTHENLIST [convert_concl_no_check (subst1 b t') DEFAULTcast; applyind (b :: args)] gl
    | _ -> tclTHENLIST [simpl_in_concl; intros; 
			prove_methods (apply (nf_beta (project gl) (applistc indid (rev args))))] gl
  in
    tclTHENLIST [intro; onLastHypId (fun id -> applyind [mkVar id])] gl


let build_equations with_ind env id info data sign is_rec arity cst 
    f ?(alias:(constr * constr * splitting) option) prob split =
  let rec computations prob f = function
    | Compute (lhs, ty, c) ->
	let (ctx', pats', _) = compose_subst lhs prob in
	let c' = map_rhs (nf_beta Evd.empty) (fun x -> x) c in
	let patsconstrs = rev_map pat_constr pats' in
	  [ctx', patsconstrs, ty, f, false, c', None]
	    
    | Split (_, _, _, cs) -> Array.fold_left (fun acc c ->
	match c with None -> acc | Some c -> 
	  acc @ computations prob f c) [] cs

    | RecValid (id, cs) -> computations prob f cs
	
    | Refined (lhs, (id, c, t), ty, arg, path, ev, (f', args), revctx, newprob, newty, cs) ->
	let (ctx', pats', _) = compose_subst lhs prob in
	let patsconstrs = rev_map pat_constr pats' in
	  [ctx', patsconstrs, ty, f, true, RProgram (applist (f', args)),
	  Some (f', path, pi1 newprob, newty,
	       map (mapping_constr revctx) patsconstrs, [mapping_constr revctx c],
	       computations newprob f' cs)]
	    
    | Valid ((ctx,pats,del), _, _, _, cs) -> 
	List.fold_left (fun acc (_, subst, c) ->
	  acc @ computations (compose_subst subst prob) f c) [] cs
  in
  let comps = computations prob f split in
  let rec flatten_comp (ctx, pats, ty, f, refine, c, rest) =
    let rest = match rest with
      | None -> []
      | Some (f, path, ctx, ty, pats, newargs, rest) ->
	  let nextlevel, rest = flatten_comps rest in
	    ((f, path, ctx, ty, pats, newargs), nextlevel) :: rest
    in (ctx, pats, ty, f, refine, c), rest
  and flatten_comps r =
    fold_right (fun cmp (acc, rest) -> 
      let stmt, rest' = flatten_comp cmp in
	(stmt :: acc, rest' @ rest)) r ([], [])
  in
  let comps =
    let (top, rest) = flatten_comps comps in
      ((f, [], sign, arity, rev_map pat_constr (pi2 prob), []), top) :: rest
  in
  let protos = map fst comps in
  let lenprotos = length protos in
  let protos = 
    list_map_i (fun i (f', path, sign, arity, pats, args) -> 
      (f', (if f' = f then Option.map pi1 alias else None), lenprotos - i, arity))
      1 protos
  in
  let rec statement i f (ctx, pats, ty, f', refine, c) =
    let comp = applistc f pats in
    let body =
      let b = match c with
	| RProgram c ->
	    mkEq ty comp (nf_beta Evd.empty c)
	| REmpty i ->
	    (* mkLetIn (Anonymous, comp, ty,  *)
	    mkApp (Lazy.force coq_ImpossibleCall, [| ty; comp |])
      in it_mkProd_or_LetIn b ctx
    in
    let cstr = 
      match c with
      | RProgram c ->
	  let len = List.length ctx in
	  let hyps, hypslen, c' = abstract_rec_calls is_rec len protos (nf_beta Evd.empty c) in
	    Some (it_mkProd_or_clear
		     (it_mkProd_or_subst
			 (applistc (mkRel (len + (lenprotos - i) + hypslen))
			     (lift_constrs hypslen pats @ [c']))
			 hyps) ctx)
      | REmpty i -> None
    in (refine, body, cstr)
  in
  let statements i ((f', path, sign, arity, pats, args as fs), c) = 
    let fs, f', unftac = 
      if f' = f then 
	match alias with
	| Some (f', unf, split) -> 
	    (f', path, sign, arity, pats, args), f', Equality.rewriteLR unf
	| None -> fs, f', tclIDTAC
      else fs, f', tclIDTAC
    in fs, unftac, map (statement i f') c in
  let stmts = list_map_i statements 0 comps in
  let ind_stmts = list_map_i (fun i (f, unf, c) -> i, f, unf, list_map_i (fun j x -> j, x) 1 c) 0 stmts in
  let all_stmts = concat (map (fun (f, unf, c) -> c) stmts) in 
  let declare_one_ind (i, (f, path, sign, arity, pats, refs), unf, stmts) = 
    let indid = add_suffix id (if i = 0 then "_ind" else ("_ind_" ^ string_of_int i)) in
    let constructors = list_map_filter (fun (_, (_, _, n)) -> n) stmts in
    let consnames = list_map_filter (fun (i, (r, _, n)) -> 
      Option.map (fun _ -> 
	let suff = (if not r then "_equation_" else "_refinement_") ^ string_of_int i in
	  add_suffix indid suff) n) stmts
    in
      { mind_entry_typename = indid;
	mind_entry_arity = it_mkProd_or_LetIn (mkProd (Anonymous, arity, mkProp)) sign;
	mind_entry_consnames = consnames;	      
	mind_entry_lc = constructors }
  in
  let declare_ind () =
    let inds = map declare_one_ind ind_stmts in
    let inductive =
      { mind_entry_record = false;
	mind_entry_finite = true;
	mind_entry_params = []; (* (identifier * local_entry) list; *)
	mind_entry_inds = inds }
    in
    let k = Command.declare_mutual_inductive_with_eliminations Declare.KernelSilent inductive [] in
    let ind = mkInd (k,0) in
    let _ =
      list_iter_i (fun i ind ->
	let constrs = list_map_i (fun j _ -> None, true, mkConstruct ((k,i),j)) 1 ind.mind_entry_lc in
	  Auto.add_hints false [info.base_id] (Auto.HintsResolveEntry constrs))
	inds
    in
    let indid = add_suffix id "_ind_fun" in
    let args = rel_list 0 (List.length sign) in
    let f, split = match alias with Some (f, _, split) -> f, split | None -> f, split in
    let app = applist (f, args) in
    let statement = it_mkProd_or_subst (applist (ind, args @ [app])) sign in
    let hookind _ gr = 
      let env = Global.env () in (* refresh *)
      let cgr = constr_of_global gr in
      Auto.add_hints false [info.base_id] (Auto.HintsImmediateEntry [cgr]);
      let _funind_stmt =
	let leninds = List.length inds in
	let elim =
	  if leninds > 1 then
	    (Indschemes.do_mutual_induction_scheme
		(list_map_i (fun i ind ->
		  let id = (dummy_loc, add_suffix ind.mind_entry_typename "_mut") in
		    (id, false, (k, i), RProp Null)) 0 inds);
	     let elimid = 
	       add_suffix (List.hd inds).mind_entry_typename "_mut"
	     in Smartlocate.global_with_alias (reference_of_id elimid))
	  else 
	    let elimid = add_suffix id "_ind_ind" in
	      Smartlocate.global_with_alias (reference_of_id elimid) 
	in
	let elimty = Global.type_of_global elim in
	let ctx, arity = decompose_prod_assum elimty in
	let newctx = list_skipn (length sign + 2) ctx in
	let newarity = it_mkProd_or_LetIn (substl [mkProp; app] arity) sign in
	let newctx' = clear_ind_assums k newctx in
	let newty =
	  if leninds = 1 then it_mkProd_or_LetIn newarity newctx'
	  else
	    let methods, preds = list_chop (List.length newctx - leninds) newctx' in
	    let ppred, preds = list_sep_last preds in
	    let newpreds =
	      list_map2_i (fun i (n, b, t) (idx, (f', path, sign, arity, pats, args), _, _) ->
		let signlen = List.length sign in
		let ctx = (Anonymous, None, arity) :: sign in
		let app =
		  let argsinfo =
		    list_map_i (fun i c -> 
		      let ty = lift (i + 2) (pi3 (List.nth sign i)) in
			(succ i, ty, lift 2 c, mkRel (i + 2)))
		      0 args
		  in
		  let lenargs = length argsinfo in
		  let cast_obj, _ = 
		    fold_left (fun (acc, pred) (i, ty, c, rel) -> 
		      if dependent (mkRel 1) pred then
			let app = 
			  mkApp (global_reference (id_of_string "eq_rect_r"),
				[| lift lenargs ty; lift lenargs rel;
				   mkLambda (Name (id_of_string "refine"), lift lenargs ty, pred); 
				   acc; (lift lenargs c); mkRel i |])
			in (app, subst1 c pred)
		      else (acc, subst1 c pred))
		      (mkRel (succ lenargs), 
		      (liftn (succ (lenargs * 2)) (succ lenargs) arity))
		      argsinfo
		  in
		  let ppath = (* The preceding P *) 
		    match path with
		    | [] -> assert false
		    | ev :: path -> 
			let res = 
			  list_try_find_i (fun i' (_, (_, path', _, _, _, _), _, _) ->
			    if path' = path then Some (idx + 1 - i')
			    else None) 1 ind_stmts
			in match res with None -> assert false | Some i -> i
		  in
		  let papp =
		    applistc (lift (succ signlen + lenargs) (mkRel ppath)) 
		      ((map (lift (lenargs * 2 + 1)) pats) @ [cast_obj])
		  in
		  let refeqs = map (fun (i, ty, c, rel) -> lift (lenargs - i) (mkEq ty c rel)) argsinfo in
		  let app c = fold_right
		    (fun c acc ->
		      mkProd (Name (id_of_string "Heq"), c, acc))
		    refeqs c
		  in
		  let indhyps =
		    concat
		      (map (fun c ->
			let hyps, hypslen, c' = 
			  abstract_rec_calls ~do_subst:false
			    is_rec signlen protos (nf_beta Evd.empty (lift 2 c)) 
			in 
			let lifthyps = lift_rel_contextn (signlen + 2) (- (pred i)) hyps in
			  lifthyps) args)
		  in
		    it_mkLambda_or_LetIn
		      (app (it_mkProd_or_subst (lift (length indhyps) papp) 
			       (lift_rel_context lenargs indhyps)))
		      ctx
		in
		let ty = it_mkProd_or_LetIn mkProp ctx in
		  (n, Some app, ty)) 1 preds (rev (List.tl ind_stmts))
	    in
	    let skipped, methods' = (* Skip the indirection methods due to refinements, 
			      as they are trivially provable *)
	      let rec aux stmts meths n meths' = 
		match stmts, meths with
		| (true, _, _) :: stmts, decl :: decls ->
		    aux stmts (subst_telescope mkProp decls) (succ n) meths'
		| (false, _, _) :: stmts, decl :: decls ->
		    aux stmts decls n (decl :: meths')
		| [], [] -> n, meths'
		| _, _ -> assert false
	      in aux all_stmts (rev methods) 0 []
	    in
	      it_mkProd_or_LetIn (lift (-skipped) newarity)
		(methods' @ newpreds @ [ppred])
	in
	let hookelim _ elimgr =
	  let env = Global.env () in
	  let elimcgr = constr_of_global elimgr in
	  let cl = functional_elimination_class () in
	  let args = [Typing.type_of env Evd.empty f; f; 
		      Typing.type_of env Evd.empty elimcgr; elimcgr]
	  in
	  let instid = add_prefix "FunctionalElimination_" id in
	    ignore(declare_instance instid [] cl args)
	in
	  (* Conv_oracle.set_strategy (ConstKey cst) Conv_oracle.Expand; *)
	  Subtac_obligations.add_definition (add_suffix id "_elim")
	    ~tactic:(ind_elim_tac (constr_of_global elim) leninds info)
	    ~hook:hookelim newty [||]
      in
      let cl = functional_induction_class () in
      let args = [Typing.type_of env Evd.empty f; f; 
		  Typing.type_of env Evd.empty cgr; cgr]
      in
      let instid = add_prefix "FunctionalInduction_" id in
	ignore(declare_instance instid [] cl args)
    in
      try ignore(Subtac_obligations.add_definition ~hook:hookind
		    indid statement ~tactic:(ind_fun_tac is_rec f info id split ind) [||])
      with e ->
	warn (str "Induction principle could not be proved automatically: " ++ fnl () ++
		 Cerrors.explain_exn e)
	  (* ignore(Subtac_obligations.add_definition ~hook:hookind indid statement [||]) *)
  in
  let proof (j, f, unf, stmts) =
    let eqns = Array.make (List.length stmts) false in
    let id = if j <> 0 then add_suffix id ("_helper_" ^ string_of_int j) else id in
    let proof (i, (r, c, n)) = 
      let ideq = add_suffix id ("_equation_" ^ string_of_int i) in
      let hook _ gr = 
	if n <> None then
	  Autorewrite.add_rew_rules info.base_id 
	    [dummy_loc, constr_of_global gr, true, Tacexpr.TacId []]
	else (Classes.declare_instance true (Ident (dummy_loc, Nametab.basename_of_global gr));
	      Auto.add_hints false [info.base_id] 
		(Auto.HintsExternEntry (0, None, impossible_call_tac (ConstRef cst))));
	eqns.(pred i) <- true;
	if array_for_all (fun x -> x) eqns then (
	  (* From now on, we don't need the reduction behavior of the constant anymore *)
	  Typeclasses.set_typeclass_transparency (EvalConstRef cst) false;
	  Conv_oracle.set_strategy (ConstKey cst) Conv_oracle.Opaque;
	  if with_ind && succ j = List.length ind_stmts then declare_ind ())
      in
	ignore(Subtac_obligations.add_definition
		  ideq c ~tactic:(tclTHENLIST [intros; unf; solve_equation_tac (ConstRef cst)]) ~hook [||])
    in iter proof stmts
  in iter proof ind_stmts

open Typeclasses

let rev_assoc k =
  let rec loop = function
    | [] -> raise Not_found | (v,k')::_ when k = k' -> v | _ :: l -> loop l 
  in
  loop

type equation_option = 
  | OInd | ORec | OComp | OEquations

let is_comp_obl comp t =
  match comp with
  | None -> false
  | Some (comp, _, _) ->
      let _, rest = decompose_prod_assum t in
      let f, _ = decompose_app rest in
	eq_constr f (mkConst comp)

let hintdb_set_transparency cst b db =
  Auto.add_hints false [db] 
    (Auto.HintsTransparencyEntry ([EvalConstRef cst], b))

let define_tree is_recursive impls status isevar env (i, sign, arity) comp ann split hook =
  let helpers, oblevs, t, ty = term_of_tree status isevar env (i, sign, arity) ann split in
  let _ = isevar := nf_evars !isevar in
  let undef = undefined_evars !isevar in
  let obls, (emap, cmap), t', ty' = 
    Eterm.eterm_obligations env i !isevar undef 0 ~status t (whd_betalet !isevar ty)
  in
  let obls = 
    Array.map (fun (id, ty, loc, s, d, t) ->
      let tac = 
	if Intset.mem (rev_assoc id emap) oblevs 
	then Some (equations_tac ()) 
	else if is_comp_obl comp ty then
	  Some (tclTRY (solve_rec_tac ()))
	else Some (snd (Subtac_obligations.get_default_tactic ()))
      in (id, ty, loc, s, d, tac)) obls
  in
  let term_info = map (fun (ev, arg) ->
    (ev, arg, List.assoc ev emap)) helpers
  in
  let hook = hook cmap term_info in
    if is_recursive = Some Structural then
      ignore(Subtac_obligations.add_mutual_definitions [(i, t', ty', impls, obls)] [] 
		~hook (Subtac_obligations.IsFixpoint [None, CStructRec]))
    else
      ignore(Subtac_obligations.add_definition ~hook
		~implicits:impls i ~term:t' ty' obls)

let conv_proj_call proj f_cst c =
  let rec aux n c =
    match kind_of_term c with
    | App (f, args) when eq_constr f proj ->
	mkApp (mkConst f_cst, array_remove_last args)
    | _ -> map_constr_with_binders succ aux n c
  in aux 0 c

let convert_projection proj f_cst = fun gl ->
  let concl = pf_concl gl in
  let concl' = conv_proj_call proj f_cst concl in
    if eq_constr concl concl' then tclIDTAC gl
    else convert_concl_no_check concl' DEFAULTcast gl

let unfold_constr c = 
  unfold_in_concl [(all_occurrences, EvalConstRef (destConst c))]

let simpl_except (ids, csts) =
  let csts = Cset.fold Cpred.remove csts Cpred.full in
  let ids = Idset.fold Idpred.remove ids Idpred.full in
    Closure.RedFlags.red_add_transparent Closure.betadeltaiota
      (ids, csts)
      
let simpl_of csts =
  (* let (ids, csts) = Auto.Hint_db.unfolds (Auto.searchtable_map db) in *)
  (* let (ids', csts') = Auto.Hint_db.unfolds (Auto.searchtable_map (db ^ "_unfold")) in *)
  (* let ids, csts = (Idset.union ids ids', Cset.union csts csts') in *)
  let opacify () = List.iter (fun cst -> 
    Conv_oracle.set_strategy (ConstKey cst) Conv_oracle.Opaque) csts
  and transp () = List.iter (fun cst -> 
    Conv_oracle.set_strategy (ConstKey cst) Conv_oracle.Expand) csts
  in opacify, transp

  (* let flags = simpl_except  in *)
  (*   reduct_in_concl (Tacred.cbv_norm_flags flags, DEFAULTcast) *)

let prove_unfolding_lemma info proj f_cst funf_cst split gl =
  let depelim h = depelim_tac h in
  let helpercsts = List.map (fun (_, _, i) -> destConst (global_reference i)) info.helpers_info in
  let opacify, transp = simpl_of helpercsts in
  let simpltac gl = opacify ();
    let res = simpl_equations_tac () gl in
      transp (); res
  in
  let unfolds = tclTHEN (autounfold_first [info.base_id] None)
    (autounfold_first [info.base_id ^ "_unfold"] None)
  in
  let solve_rec_eq gl =
    match kind_of_term (pf_concl gl) with
    | App (eq, [| ty; x; y |]) ->
	let xf, _ = decompose_app x and yf, _ = decompose_app y in
	  if eq_constr (mkConst f_cst) xf && eq_constr proj yf then
	    let unfolds = unfold_in_concl 
	      [((true, [1]), EvalConstRef f_cst); 
	       ((true, [1]), EvalConstRef (destConst proj))]
	    in 
	      tclTHENLIST [unfolds; simpltac; pi_tac ()] gl
	  else reflexivity gl
    | _ -> reflexivity gl
  in
  let solve_eq =
    tclORELSE reflexivity
      (tclTHEN (tclTRY Cctac.f_equal) solve_rec_eq)
  in
  let abstract tac = tclABSTRACT None tac in
  let rec aux = function
    | Split ((ctx,pats,_), var, _, splits) ->
	(fun gl ->
	  match kind_of_term (pf_concl gl) with
	  | App (eq, [| ty; x; y |]) -> 
	      let f, pats' = decompose_app y in
	      let id = find_splitting_var pats var pats' in
	      let splits = list_map_filter (fun x -> x) (Array.to_list splits) in
		abstract (tclTHEN_i (depelim id)
			     (fun i -> let split = nth splits (pred i) in
					 tclTHENLIST [aux split])) gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding goal") gl)
	    
    | Valid ((ctx, _, _), ty, substc, tac, rest) ->
	tclTHEN_i tac (fun i -> let _, subst, split = nth rest (pred i) in
				  tclTHEN (Lazy.force unfold_add_pattern) (aux split))

    | RecValid (id, cs) -> 
	tclTHEN (unfold_recursor_tac ()) (aux cs)
	  
    | Refined ((ctx, _, _), (id, c, ty), _, arg, path, ev, _, _, newprob, newty, s) -> 
	let rec reftac gl = 
	  match kind_of_term (pf_concl gl) with
	  | App (f, [| ty; term1; term2 |]) ->
	      let f1, arg1 = destApp term1 and f2, arg2 = destApp term2 in
	      let _, a1 = find_helper_arg info f1 arg1 
	      and ev2, a2 = find_helper_arg info f2 arg2 in
		if ev2 = ev then 
	  	  tclTHENLIST
	  	    [Equality.replace_by a1 a2
	  		(tclTHENLIST [solve_eq]);
	  	     letin_tac None (Name id) a2 None allHypsAndConcl;
	  	     clear_body [id]; aux s] gl
		else tclTHENLIST [unfolds; simpltac; reftac] gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding lemma goal") gl
	in
	  abstract (tclTHENLIST [intros; simpltac; reftac])
	    
    | Compute (_, _, RProgram c) ->
	abstract (tclTHENLIST [intros; tclTRY unfolds; simpltac; solve_eq])
	  
    | Compute ((ctx,_,_), _, REmpty id) ->
	let (na,_,_) = nth ctx (pred id) in
	let id = out_name na in
	  abstract (depelim id)
  in
    try
      let unfolds = unfold_in_concl
	[((true, [1]), EvalConstRef f_cst); ((true, [1]), EvalConstRef funf_cst)]
      in
      let res =
	tclTHENLIST 
	  [set_eos_tac (); intros; unfolds; simpl_in_concl; unfold_recursor_tac ();
	   (fun gl -> 
	     Conv_oracle.set_strategy (ConstKey f_cst) Conv_oracle.Opaque;
	     Conv_oracle.set_strategy (ConstKey funf_cst) Conv_oracle.Opaque;
	     aux split gl)] gl
      in Conv_oracle.set_strategy (ConstKey f_cst) Conv_oracle.Expand;
	Conv_oracle.set_strategy (ConstKey funf_cst) Conv_oracle.Expand;
	res
    with e ->
      Conv_oracle.set_strategy (ConstKey f_cst) Conv_oracle.Expand;
      Conv_oracle.set_strategy (ConstKey funf_cst) Conv_oracle.Expand;
      raise e
      
let update_split is_rec cmap f prob id split =
  let split' = map_evars_in_split cmap split in
    match is_rec with
    | Some Structural -> subst_rec_split f prob [(id, f)] split'
    | Some (Logical (comp, compapp, proj)) ->
	subst_comp_proj_split f (mkConst proj) split'
    | _ -> split'

let rec translate_cases_pattern env avoid = function
  | PatVar (loc, Name id) -> PUVar id
  | PatVar (loc, Anonymous) -> 
      let n = next_ident_away (id_of_string "wildcard") avoid in
	avoid := n :: !avoid; PUVar n
  | PatCstr (loc, (ind, _ as cstr), pats, Anonymous) ->
      PUCstr (cstr, (fst (inductive_nargs env ind)), map (translate_cases_pattern env avoid) pats)
  | PatCstr (loc, cstr, pats, Name id) ->
      user_err_loc (loc, "interp_pats", str "Aliases not supported by Equations")

let interp_eqn i is_rec isevar env impls sign arity recu eqn =
  let avoid = ref [] in
  let rec interp_pat (loc, p) =
    match p with
    | PEApp ((loc,f), l) -> 
	(try match Nametab.extended_locate (make_short_qualid f) with
	| TrueGlobal (ConstructRef c) -> 
	    let (ind,_) = c in
	    let nparams, _ = inductive_nargs env ind in
	    let nargs = constructor_nrealargs env c in
	    let len = List.length l in
	    let l' =
	      if len < nargs then 
		list_make (nargs - len) (loc,PEWildcard) @ l
	      else l
	    in 
	      Dumpglob.add_glob loc (ConstructRef c);
	      PUCstr (c, nparams, map interp_pat l')
	| _ -> 
	    if l <> [] then 
	      user_err_loc (loc, "interp_pats",
			   str "Pattern variable " ++ pr_id f ++ str" cannot be applied ")
	    else PUVar f
	  with Not_found -> PUVar f)
    | PEInac c -> PUInac c
    | PEWildcard -> 
	let n = next_ident_away (id_of_string "wildcard") avoid in
	  avoid := n :: !avoid; PUVar n

    | PEPat p ->
	let ids, pats = intern_pattern env p in
	  (* Names.identifier list * *)
	  (*   ((Names.identifier * Names.identifier) list * Rawterm.cases_pattern) list *)
	let upat = 
	  match pats with
	  | [(l, pat)] -> translate_cases_pattern env avoid pat
	  | _ -> user_err_loc (loc, "interp_pats", str "Or patterns not supported by equations")
	in upat
  in
  let rec aux curpats (idopt, pats, rhs) =
    let curpats' = 
      match pats with
      | SignPats l -> l
      | RefinePats l -> curpats @ l
    in
    avoid := !avoid @ ids_of_pats curpats';
    Option.iter (fun (loc,id) ->
      if id <> i then
	user_err_loc (loc, "interp_pats",
		     str "Expecting a pattern for " ++ pr_id i);
      Dumpglob.dump_reference loc "<>" (string_of_id id) "def")
      idopt;
    (*   if List.length pats <> List.length sign then *)
    (*     user_err_loc (loc, "interp_pats", *)
    (* 		 str "Patterns do not match the signature " ++  *)
    (* 		   pr_rel_context env sign); *)
    let pats = map interp_pat curpats' in
      match is_rec with
      | Some Structural -> (PUVar i :: pats, interp_rhs curpats' None rhs)
      | Some (Logical (_, _, compproj)) -> (pats, interp_rhs curpats' (Some (ConstRef compproj)) rhs)
      | None -> (pats, interp_rhs curpats' None rhs)
  and interp_rhs curpats compproj = function
    | Refine (c, eqs) -> Refine (interp_constr_expr compproj !avoid c, map (aux curpats) eqs)
    | Program c -> Program (interp_constr_expr compproj !avoid c)
    | Empty i -> Empty i
    | Rec (i, r, s) -> Rec (i, r, map (aux curpats) s)
    | By (x, s) -> By (x, map (aux curpats) s)
  and interp_constr_expr compproj ids c = 
    match c, compproj with
    (* |   | CAppExpl of loc * (proj_flag * reference) * constr_expr list *)
    | CApp (loc, (None, CRef (Ident (loc',id'))), args), Some compproj when i = id' ->
	let qidproj = Nametab.shortest_qualid_of_global Idset.empty compproj in
	  CApp (loc, (None, CRef (Qualid (loc', qidproj))), args)
    | _ -> map_constr_expr_with_binders (fun id l -> id :: l) 
	(interp_constr_expr compproj) ids c
  in aux [] eqn
	
let define_by_eqs opts i (l,ann) t nt eqs =
  let with_comp, with_rec, with_eqns, with_ind =
    let try_opt default opt =
      try List.assoc opt opts with Not_found -> default
    in
      try_opt true OComp, try_opt true ORec, 
    try_opt true OEquations, try_opt true OInd
  in
  let env = Global.env () in
  let isevar = ref (create_evar_defs Evd.empty) in
  let (env', sign), impls = interp_context_evars isevar env l in
  let arity = interp_type_evars isevar env' t in
  let sign = nf_rel_context_evar ( !isevar) sign in
  let arity = nf_evar ( !isevar) arity in
  let arity, comp = 
    let body = it_mkLambda_or_LetIn arity sign in
    let _ = check_evars env Evd.empty !isevar body in
      if with_comp then
	let compid = add_suffix i "_comp" in
	let ce =
	  { const_entry_body = body;
	    const_entry_type = None;
	    const_entry_opaque = false;
	    const_entry_boxed = false}
	in
	let comp =
	  Declare.declare_constant compid (DefinitionEntry ce, IsDefinition Definition)
	in (*Typeclasses.add_constant_class c;*)
	let compapp = mkApp (mkConst comp, rel_vect 0 (length sign)) in
	let projid = add_suffix i "_comp_proj" in
	let compproj = 
	  let body = it_mkLambda_or_LetIn (mkRel 1)
	    ((Name (id_of_string "comp"), None, compapp) :: sign)
	  in
	  let ce =
	    { const_entry_body = body;
	      const_entry_type = None;
	      const_entry_opaque = false;
	      const_entry_boxed = false}
	  in Declare.declare_constant projid (DefinitionEntry ce, IsDefinition Definition)
	in
	  Impargs.declare_manual_implicits true (ConstRef comp) impls;
	  Impargs.declare_manual_implicits true (ConstRef compproj) 
	    (impls @ [ExplByPos (succ (List.length sign), None), (true, false, true)]);
	  hintdb_set_transparency comp false "Below";
	  hintdb_set_transparency comp false "subterm_relation";
	  compapp, Some (comp, compapp, compproj)
      else arity, None
  in
  let env = Global.env () in (* To find the comp constant *)
  let ty = it_mkProd_or_LetIn arity sign in
  let data = Constrintern.compute_full_internalization_env
    env Constrintern.Recursive [] [i] [ty] [impls] 
  in
  let sort = Retyping.get_type_of env !isevar ty in
  let fixprot = mkApp (delayed_force Subtac_utils.fix_proto, [|sort; ty|]) in
  let fixdecls = [(Name i, None, fixprot)] in
  let is_recursive =
    let rec occur_eqn (_, _, rhs) =
      match rhs with
      | Program c -> if occur_var_constr_expr i c then Some false else None
      | Refine (c, eqs) -> 
	  if occur_var_constr_expr i c then Some false
	  else occur_eqns eqs
      | Rec _ -> Some true
      | _ -> None
    and occur_eqns eqs =
      let occurs = map occur_eqn eqs in
	if for_all ((=) None) occurs then None
	else if exists ((=) (Some true)) occurs then Some true
	else Some false
    in 
      match occur_eqns eqs with
      | None -> None 
      | Some true -> Option.map (fun c -> Logical c) comp
      | Some false -> Some Structural
  in
  let equations = 
    States.with_heavy_rollback (fun () -> 
      Option.iter (Metasyntax.set_notation_for_interpretation data) nt;
      map (interp_eqn i is_recursive isevar env data sign arity None) eqs) ()
  in
  let sign = nf_rel_context_evar ( !isevar) sign in
  let arity = nf_evar ( !isevar) arity in
  let fixdecls = nf_rel_context_evar ( !isevar) fixdecls in
    (*   let ce = check_evars fixenv Evd.empty !isevar in *)
    (*   List.iter (function (_, _, Program rhs) -> ce rhs | _ -> ()) equations; *)
  let prob = 
    if is_recursive = Some Structural then
      id_subst (sign @ fixdecls)
    else id_subst sign
  in
  let split = covering env isevar (i,with_comp,data) equations prob arity in
    (* if valid_tree prob split then *)
  let status = (* if is_recursive then Expand else *) Define false in
  let baseid = string_of_id i in
  let (ids, csts) = full_transparent_state in
  Auto.create_hint_db false baseid (ids, Cpred.remove (Subtac_utils.fix_proto_ref ()) csts) true;
  let hook cmap helpers _ gr = 
    let info = { base_id = baseid; helpers_info = helpers } in
    let f_cst = match gr with ConstRef c -> c | _ -> assert false in
    let env = Global.env () in
    let f = constr_of_global gr in
      if with_eqns or with_ind then
	match is_recursive with
	| Some Structural ->
	    let cutprob, norecprob = 
	      let (ctx, pats, ctx' as ids) = id_subst sign in
	      let fixdecls' = [Name i, Some f, fixprot] in
		(ctx @ fixdecls', pats, ctx'), ids
	    in
	    let split = update_split is_recursive cmap f cutprob i split in
	      build_equations with_ind env i info data sign is_recursive arity 
		f_cst (constr_of_global gr) norecprob split
	| None ->
	    let split = update_split is_recursive cmap f prob i split in
	    build_equations with_ind env i info data sign is_recursive arity 
	      f_cst (constr_of_global gr) prob split
	| Some (Logical (comp, capp, compproj)) ->
	    let split = update_split is_recursive cmap f prob i split in
	    (* We first define the unfolding and show the fixpoint equation. *)
	    isevar := Evd.empty;
	    let unfoldi = add_suffix i "_unfold" in
	    (* let unfold_baseid = string_of_id unfoldi in *)
	    (* Auto.create_hint_db false unfold_baseid (ids, Cpred.remove (Subtac_utils.fix_proto_ref ()) csts) true; *)
	    let rec unfold_eqs eqs =
	      concat (map
			 (fun (optid, pats, rhs) ->
			   let optid = Option.map (fun (loc,id) -> (loc, unfoldi)) optid in
			   match rhs with
			   | Rec (v, r, eqs) -> unfold_eqs eqs
			   | Refine (ce, eqs) -> [(optid, pats, Refine (ce, unfold_eqs eqs))]
			   | _ -> [(optid, pats, rhs)])
			 eqs)
	    in
	    let unfold_equations = 
	      map (interp_eqn unfoldi None isevar env data sign arity None)
		(unfold_eqs eqs)
	    in
	    let data = ([], []) in
	    let unfold_split = covering env isevar (unfoldi, with_comp, data) unfold_equations prob arity in
	    let hook_unfold cmap helpers' _ gr' = 
	      let info = { base_id = baseid; helpers_info = helpers @ helpers' } in
	      let funf_cst = match gr' with ConstRef c -> c | _ -> assert false in
	      let funfc =  mkConst funf_cst in
	      let unfold_split = update_split None cmap funfc prob unfoldi unfold_split in
	      let hook_eqs _ grunfold =
		Conv_oracle.set_strategy (ConstKey funf_cst) Conv_oracle.transparent;
		build_equations with_ind env i info data sign None arity
		  funf_cst funfc ~alias:(f, constr_of_global grunfold, split) prob unfold_split
	      in
	      let stmt = it_mkProd_or_LetIn 
		(mkEq arity (mkApp (f, extended_rel_vect 0 sign))
		    (mkApp (mkConst funf_cst, extended_rel_vect 0 sign))) sign 
	      in
	      let tac = prove_unfolding_lemma info (mkConst compproj) f_cst funf_cst unfold_split in
	      let unfold_eq_id = add_suffix unfoldi "_eq" in
		ignore(Subtac_obligations.add_definition ~hook:hook_eqs ~reduce:(fun x -> x)
			  ~implicits:impls unfold_eq_id stmt ~tactic:tac [||])
	    in
	      define_tree None impls status isevar env (unfoldi, sign, arity) None ann unfold_split hook_unfold
      else ()
  in define_tree is_recursive impls status isevar env (i, sign, arity) comp ann split hook

module Gram = Pcoq.Gram
module Vernac = Pcoq.Vernac_
module Tactic = Pcoq.Tactic

module DeppatGram =
struct
  let gec s = Gram.Entry.create ("Deppat."^s)

  let deppat_equations : pre_equation list Gram.Entry.e = gec "deppat_equations"

  let equation_options : (equation_option * bool) list Gram.Entry.e = gec "equation_options"

  let binders_let2 : (local_binder list * (identifier located option * recursion_order_expr)) 
      Gram.Entry.e = gec "binders_let2"

(*   let where_decl : decl_notation Gram.Entry.e = gec "where_decl" *)

end

open Rawterm
open DeppatGram
open Util
open Pcoq
open Prim
open Constr
open G_vernac

GEXTEND Gram
  GLOBAL: (* deppat_gallina_loc *) pattern deppat_equations binders_let2 equation_options;
 
  deppat_equations:
    [ [ l = LIST1 equation SEP ";" -> l ] ]
  ;

  binders_let2:
    [ [ l = binders_let_fixannot -> l ] ]
  ;

  equation:
    [ [ id = identref; 	pats = LIST1 patt; r = rhs -> (Some id, SignPats pats, r)
      | "|"; pats = LIST1 lpatt SEP "|"; r = rhs -> (None, RefinePats pats, r) 
    ] ]
  ;

  patt:
    [ [ id = identref -> loc, PEApp (id, [])
      | "_" -> loc, PEWildcard
      | "("; p = lpatt; ")" -> p
      | "?("; c = Constr.lconstr; ")" -> loc, PEInac c
      | p = pattern LEVEL "0" -> loc, PEPat p
    ] ]
  ;

  lpatt:
    [ [ id = identref; pats = LIST0 patt -> loc, PEApp (id, pats)
      | p = patt -> p
    ] ]
  ;

  rhs:
    [ [ ":=!"; id = identref -> Empty id
      |":="; c = Constr.lconstr -> Program c
      | "with"; c = Constr.lconstr; ":="; e = equations -> Refine (c, e)
      | "<="; c = Constr.lconstr; "=>"; e = equations -> Refine (c, e)
      | "<-"; "(" ; t = Tactic.tactic; ")"; e = equations -> By (Inl t, e)
      | "by"; IDENT "rec"; id = identref; rel = OPT constr; ":="; e = deppat_equations -> Rec (id, rel, e)
    ] ]
  ;

  equations:
    [ [ "{"; l = deppat_equations; "}" -> l 
      | l = deppat_equations -> l
    ] ]
  ;

  equation_option:
    [ [ IDENT "noind" -> OInd, false
      | IDENT "ind" -> OInd, true
      | IDENT "struct" -> ORec, true
      | IDENT "nostruct" -> ORec, false
      | IDENT "comp" -> OComp, true
      | IDENT "nocomp" -> OComp, false
      | IDENT "eqns" -> OEquations, true
      | IDENT "noeqns" -> OEquations, false
    ] ]
  ;
  
  equation_options:
    [ [ "(" ; l = LIST1 equation_option; ")" -> l
      | -> [] ] ]
  ;
  END

type 'a deppat_equations_argtype = (pre_equation list, 'a) Genarg.abstract_argument_type

let (wit_deppat_equations : Genarg.tlevel deppat_equations_argtype),
  (globwit_deppat_equations : Genarg.glevel deppat_equations_argtype),
  (rawwit_deppat_equations : Genarg.rlevel deppat_equations_argtype) =
  Genarg.create_arg "deppat_equations"

type 'a equation_options_argtype = ((equation_option * bool) list, 'a) Genarg.abstract_argument_type

let (wit_equation_options : Genarg.tlevel equation_options_argtype),
  (globwit_equation_options : Genarg.glevel equation_options_argtype),
  (rawwit_equation_options : Genarg.rlevel equation_options_argtype) =
  Genarg.create_arg "equation_options"

type 'a binders_let2_argtype = (local_binder list * (identifier located option * recursion_order_expr), 'a) Genarg.abstract_argument_type

let (wit_binders_let2 : Genarg.tlevel binders_let2_argtype),
  (globwit_binders_let2 : Genarg.glevel binders_let2_argtype),
  (rawwit_binders_let2 : Genarg.rlevel binders_let2_argtype) =
  Genarg.create_arg "binders_let2"

type 'a decl_notation_argtype = (Vernacexpr.decl_notation option, 'a) Genarg.abstract_argument_type

let (wit_decl_notation : Genarg.tlevel decl_notation_argtype),
  (globwit_decl_notation : Genarg.glevel decl_notation_argtype),
  (rawwit_decl_notation : Genarg.rlevel decl_notation_argtype) =
  Genarg.create_arg "decl_notation"

type 'a identref_argtype = (identifier located, 'a) Genarg.abstract_argument_type

let (wit_identref : Genarg.tlevel identref_argtype),
  (globwit_identref : Genarg.glevel identref_argtype),
  (rawwit_identref : Genarg.rlevel identref_argtype) =
  Genarg.create_arg "identref"

let with_rollback f x =
  let st = States.freeze () in
    try f x with e -> msg (Toplevel.print_toplevel_error e); States.unfreeze st

let equations opts (loc, i) l t nt eqs =
  Dumpglob.dump_definition (loc, i) false "def";
  with_rollback (define_by_eqs opts i l t nt) eqs

VERNAC COMMAND EXTEND Define_equations
| [ "Equations" equation_options(opt) identref(i) binders_let2(l) 
      ":" lconstr(t) ":=" deppat_equations(eqs)
      decl_notation(nt) ] ->
    [ equations opt i l t nt eqs ]
      END

let rec int_of_coq_nat c = 
  match kind_of_term c with
  | App (f, [| arg |]) -> succ (int_of_coq_nat arg)
  | _ -> 0

let gclause_none =
  { onhyps=Some []; concl_occs=no_occurrences_expr }

let solve_equations_goal destruct_tac tac gl =
  let concl = pf_concl gl in
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
      if n = 0 then [], c
      else match kind_of_term c with
      | LetIn (Name id, br, brt, b) ->
	  let rest, b = aux (pred n) b in
	    (id, br, brt) :: rest, b
      | _ -> error "Unnexpected goal"
    in aux brs b
  in
  let ids = targetn :: branchesn :: map pi1 branches in
  let cleantac = tclTHEN (intros_using ids) (thin ids) in
  let dotac = tclDO (succ targ) intro in
  let letintac (id, br, brt) = 
    tclTHEN (letin_tac None (Name id) br (Some brt) gclause_none) tac 
  in
  let subtacs =
    tclTHENS destruct_tac (map letintac branches)
  in tclTHENLIST [cleantac ; dotac ; subtacs] gl

TACTIC EXTEND solve_equations
  [ "solve_equations" tactic(destruct) tactic(tac) ] -> [ solve_equations_goal (snd destruct) (snd tac) ]
    END

let db_of_constr c = match kind_of_term c with
  | Const c -> string_of_label (con_label c)
  | _ -> assert false

let dbs_of_constrs = map db_of_constr

open Extraargs

TACTIC EXTEND simp
| [ "simp" ne_preident_list(l) in_arg_hyp(c) ] -> 
    [ simp_eqns_in (glob_in_arg_hyp_to_clause c) l ]
| [ "simpc" constr_list(l) in_arg_hyp(c) ] -> 
    [ simp_eqns_in (glob_in_arg_hyp_to_clause c) (dbs_of_constrs l) ]
END

let depcase (mind, i as ind) =
  let indid = Nametab.basename_of_global (IndRef ind) in
  let mindb, oneind = Global.lookup_inductive ind in
  let inds = List.rev (Array.to_list (Array.mapi (fun i oib -> mkInd (mind, i)) mindb.mind_packets)) in
  let ctx = oneind.mind_arity_ctxt in
  let nparams = mindb.mind_nparams in
  let args, params = list_chop (List.length ctx - nparams) ctx in
  let nargs = List.length args in
  let liftconstr = nargs + 1 in
  let indapp = mkApp (mkInd ind, extended_rel_vect 0 ctx) in
  let pred = it_mkProd_or_LetIn (new_Type ()) 
    ((Anonymous, None, indapp) :: args)
  in
  let nconstrs = Array.length oneind.mind_nf_lc in
  let branches = 
    array_map2_i (fun i id cty ->
      let substcty = substl inds cty in
      let (args, arity) = decompose_prod_assum substcty in
      let _, indices = decompose_app arity in
      let _, indices = list_chop nparams indices in
      let ncargs = List.length args - nparams in
      let realargs, pars = list_chop ncargs args in
      let realargs = lift_rel_context (i + 1) realargs in
      let arity = applistc (mkRel (ncargs + i + 1)) 
	(indices @ [mkApp (mkConstruct (ind, succ i), 
			  Array.append (extended_rel_vect (ncargs + i + 1) params)
			    (extended_rel_vect 0 realargs))])
      in
      let body = mkRel (liftconstr + nconstrs - i) in
      let br = it_mkProd_or_LetIn arity realargs in
	(Name (id_of_string ("P" ^ string_of_int i)), None, br), body)
      oneind.mind_consnames oneind.mind_nf_lc
  in
  let ci = {
    ci_ind = ind;
    ci_npar = nparams;
    ci_cstr_ndecls = oneind.mind_consnrealdecls;
    ci_pp_info = { ind_nargs = oneind.mind_nrealargs; style = RegularStyle; } }
  in
  let obj i =
    mkApp (mkInd ind,
	  (Array.append (extended_rel_vect (nargs + nconstrs + i) params)
	      (extended_rel_vect 0 args)))
  in
  let ctxpred = (Anonymous, None, obj (2 + nargs)) :: args in
  let app = mkApp (mkRel (nargs * 2 + nconstrs + 3),
		  (extended_rel_vect 0 ctxpred))
  in
  let ty = it_mkLambda_or_LetIn app ctxpred in
  let case = mkCase (ci, ty, mkRel 1, Array.map snd branches) in
  let xty = obj 1 in
  let xid = Namegen.named_hd (Global.env ()) xty Anonymous in
  let body = 
    it_mkLambda_or_LetIn case 
      ((xid, None, obj 1) 
	:: ((lift_rel_context 1 args) 
	     @ (List.rev (Array.to_list (Array.map fst branches))) 
	     @ ((Name (id_of_string "P"), None, pred) :: params)))
  in
  let ce =
    { const_entry_body = body;
      const_entry_type = None;
      const_entry_opaque = false;
      const_entry_boxed = false}
  in
  let kn = 
    Declare.declare_constant (add_suffix indid "_case") 
      (DefinitionEntry ce, IsDefinition Scheme)
  in ctx, indapp, kn

let derive_dep_elimination i loc =
  let ctx, ty, kn = depcase i in
  let indid = Nametab.basename_of_global (IndRef i) in
  let id = add_prefix "DependentElimination_" indid in
  let cl = dependent_elimination_class () in
  let env = Global.env () in
  let casety = type_of_constant env kn in
    declare_instance id ctx cl [ty; casety; mkConst kn]

VERNAC COMMAND EXTEND Derive_DependentElimination
| [ "Derive" "DependentElimination" "for" constr_list(c) ] -> [ 
    List.iter (fun c ->
      let c' = interp_constr Evd.empty (Global.env ()) c in
	match kind_of_term c' with
	| Ind i -> ignore(derive_dep_elimination i (constr_loc c))
	| _ -> error "Expected an inductive type")
      c
  ]
END

let mkcase env c ty constrs =
  let cty = Typing.type_of env Evd.empty c in
  let ind, origargs = decompose_app cty in
  let mind, ind = match kind_of_term ind with
    | Ind (mu, n as i) -> mu, i
    | _ -> assert false
  in
  let mindb, oneind = Global.lookup_inductive ind in
  let inds = List.rev (Array.to_list (Array.mapi (fun i oib -> mkInd (mind, i)) mindb.mind_packets)) in
  let ctx = oneind.mind_arity_ctxt in
  let _len = List.length ctx in
  let params = mindb.mind_nparams in
  let origparams, _ = list_chop params origargs in
  let ci = {
    ci_ind = ind;
    ci_npar = params;
    ci_cstr_ndecls = oneind.mind_consnrealdecls;
    ci_pp_info = { ind_nargs = oneind.mind_nrealargs; style = RegularStyle; } }
  in
  let brs = 
    array_map2_i (fun i id cty ->
      let (args, arity) = decompose_prod_assum (substl inds cty) in
      let realargs, pars = list_chop (List.length args - params) args in
      let args = substl (List.rev origparams) (it_mkProd_or_LetIn arity realargs) in
      let args, arity = decompose_prod_assum args in
      let res = constrs ind i id params args arity in
	it_mkLambda_or_LetIn res args)
      oneind.mind_consnames oneind.mind_nf_lc
  in
    mkCase (ci, ty, c, brs)
      


let mkEq t x y = 
  mkApp (Coqlib.build_coq_eq (), [| refresh_universes t; x; y |])
    
let mkRefl t x = 
  mkApp ((Coqlib.build_coq_eq_data ()).Coqlib.refl, [| refresh_universes t; x |])

let mkHEq t x u y =
  mkApp (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq",
	[| refresh_universes t; x; refresh_universes u; y |])
    
let mkHRefl t x =
  mkApp (Coqlib.coq_constant "mkHEq" ["Logic";"JMeq"] "JMeq_refl",
	[| refresh_universes t; x |])

let mk_term_eq env sigma ty t ty' t' =
  if Reductionops.is_conv env sigma ty ty' then
    mkEq ty t t', mkRefl ty' t'
  else
    mkHEq ty t ty' t', mkHRefl ty' t'

let mk_eqs env args args' pv = 
  let prf =
    List.fold_right2 (fun x y c -> 
      let tyx = Typing.type_of env Evd.empty x 
      and tyy = Typing.type_of env Evd.empty y in
      let hyp, prf = mk_term_eq env Evd.empty tyx x tyy y in
	mkProd (Anonymous, hyp, lift 1 c))
      args args' pv
  in mkProd (Anonymous, prf, pv)
	
let derive_no_confusion ind =
  let mindb, oneind = Global.lookup_inductive ind in
  let ctx = map_rel_context refresh_universes oneind.mind_arity_ctxt in
  let len = List.length ctx in
  let params = mindb.mind_nparams in
  let args = oneind.mind_nrealargs in
  let argsvect = rel_vect 0 len in
  let paramsvect, rest = array_chop params argsvect in
  let indty = mkApp (mkInd ind, argsvect) in
  let pid = (id_of_string "P") in
  let pvar = mkVar pid in
  let xid = id_of_string "x" and yid = id_of_string "y" in
  let xdecl = (Name xid, None, lift 1 indty) in
  let binders = xdecl :: (Name pid, None, new_Type ()) :: ctx in
  let ydecl = (Name yid, None, lift 2 indty) in
  let fullbinders = ydecl :: binders in
  let arity = it_mkProd_or_LetIn (new_Type ()) fullbinders in
  let env = push_rel_context binders (Global.env ()) in
  let ind_with_parlift n =
    mkApp (mkInd ind, Array.append (Array.map (lift n) paramsvect) rest) 
  in
  let lenargs = List.length ctx - params in
  let pred =
    let elim =
      let app = ind_with_parlift (args + 2) in
	it_mkLambda_or_LetIn 
	  (mkProd_or_LetIn (Anonymous, None, lift 1 app) (new_Type ()))
	  ((Name xid, None, ind_with_parlift (2 + lenargs)) :: list_firstn lenargs ctx)
    in
      mkcase env (mkRel 1) elim (fun ind i id nparams args arity ->
	let ydecl = (Name yid, None, arity) in
	let env' = push_rel_context (ydecl :: args) env in
	let decl = (Name yid, None, ind_with_parlift (lenargs + List.length args + 3)) in
	  mkLambda_or_LetIn ydecl
	    (mkcase env' (mkRel 1) 
		(it_mkLambda_or_LetIn (new_Type ()) (decl :: list_firstn lenargs ctx))
		(fun _ i' id' nparams args' arity' ->
		  if i = i' then 
		    mk_eqs (push_rel_context args' env')
		      (rel_list (List.length args' + 1) (List.length args))
		      (rel_list 0 (List.length args')) pvar
		  else pvar)))
  in
  let app = it_mkLambda_or_LetIn (replace_vars [(pid, mkRel 2)] pred) binders in
  let ce =
    { const_entry_body = app;
      const_entry_type = Some arity;
      const_entry_opaque = false;
      const_entry_boxed = false} 
  in
  let indid = Nametab.basename_of_global (IndRef ind) in
  let id = add_prefix "NoConfusion_" indid
  and noid = add_prefix "noConfusion_" indid
  and packid = add_prefix "NoConfusionPackage_" indid in
  let cstNoConf = Declare.declare_constant id (DefinitionEntry ce, IsDefinition Definition) in
  let stmt = it_mkProd_or_LetIn
    (mkApp (mkConst cstNoConf, rel_vect 1 (List.length fullbinders)))
    ((Anonymous, None, mkEq (lift 3 indty) (mkRel 2) (mkRel 1)) :: fullbinders)
  in
  let hook _ gr = 
    let tc = class_info (global_of_constr (Lazy.force coq_noconfusion_class)) in
    let b, ty = instance_constructor tc [indty; mkApp (mkConst cstNoConf, argsvect) ; 
					 mkApp (constr_of_global gr, argsvect) ] in
    let ce = { const_entry_body = it_mkLambda_or_LetIn b ctx;
	       const_entry_type = Some (it_mkProd_or_LetIn ty ctx); 
	       const_entry_opaque = false; const_entry_boxed = false }
    in
    let inst = Declare.declare_constant packid (DefinitionEntry ce, IsDefinition Instance) in
      Typeclasses.add_instance (Typeclasses.new_instance tc None true (ConstRef inst))
  in
    ignore(Subtac_obligations.add_definition ~hook noid 
	      stmt ~tactic:(noconf_tac ()) [||])
     

VERNAC COMMAND EXTEND Derive_NoConfusion
| [ "Derive" "NoConfusion" "for" constr_list(c) ] -> [ 
    List.iter (fun c ->
      let c' = interp_constr Evd.empty (Global.env ()) c in
	match kind_of_term c' with
	| Ind i -> derive_no_confusion i
	| _ -> error "Expected an inductive type")
      c
  ]
END
  
(* TACTIC EXTEND pattern_call *)
(* [ "pattern_call" constr(c) ] -> [ fun gl -> *)
(*   match kind_of_term c with *)
(*   | App (f, [| arg |]) -> *)
(*       let concl = pf_concl gl in *)
(*       let replcall = replace_term c (mkRel 1) concl in *)
(*       let replarg = replace_term arg (mkRel 2) replcall in *)
(*       let argty = pf_type_of gl arg and cty = pf_type_of gl c in *)
(*       let rels = [(Name (id_of_string "call"), None, replace_term arg (mkRel 1) cty); *)
(* 		  (Name (id_of_string "arg"), None, argty)] in *)
(*       let newconcl = mkApp (it_mkLambda_or_LetIn replarg rels, [| arg ; c |]) in *)
(* 	convert_concl newconcl DEFAULTcast gl  *)
(*   | _ -> tclFAIL 0 (str "Not a recognizable call") gl ] *)
(* END *)

let pattern_call ?(pattern_term=true) c gl =
  let cty = pf_type_of gl c in
  let ids = ids_of_named_context (pf_hyps gl) in
  let deps =
    match kind_of_term c with
    | App (f, args) -> Array.to_list args
    | _ -> []
  in
  let varname c = match kind_of_term c with
    | Var id -> id
    | _ -> Namegen.next_ident_away (id_of_string (Namegen.hdchar (pf_env gl) c))
	ids
  in
  let mklambda ty (c, id, cty) =
    let conclvar = subst_term_occ all_occurrences c ty in
      mkNamedLambda id cty conclvar
  in
  let subst = 
    let deps = List.rev_map (fun c -> (c, varname c, pf_type_of gl c)) deps in
      if pattern_term then (c, varname c, cty) :: deps
      else deps
  in
  let concllda = List.fold_left mklambda (pf_concl gl) subst in
  let conclapp = applistc concllda (List.rev_map pi1 subst) in
    convert_concl_no_check conclapp DEFAULTcast gl

TACTIC EXTEND pattern_call
[ "pattern_call" constr(c) ] -> [ pattern_call c ]
END

let dependencies env c ctx = 
  let init = global_vars_set env c in
  let deps =
    Sign.fold_named_context_reverse 
      (fun variables (n, _, _ as decl) ->
	let dvars = global_vars_set_of_decl env decl in
	  if Idset.mem n variables then Idset.union dvars variables
	  else variables)
      ~init:init ctx
  in
    (init, Idset.diff deps init)


