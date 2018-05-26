(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Constr
open Util
open Covering

open EConstr
open Reductionops
open Termops

module MatchingProblem = struct
  type t = pat * pat

  let rec pat_compare x y =
    match x, y with
    | PRel i, PRel j -> Int.compare i j
    | PCstr ((c, u), pl), PCstr ((c', u'), pl') ->
      let x = Names.constructor_ord c c' in
	if Int.equal x 0 then
	  compare_pats pl pl'
	else x
    | PInac t, PInac t' -> Constr.compare (EConstr.Unsafe.to_constr t) (EConstr.Unsafe.to_constr t')
    | PRel _, _ -> -1
    | _, PRel _ -> 1
    | PCstr _, _ -> -1
    | _, PCstr _ -> 1
    | PHide _, _ -> -1
    | _, PHide _ -> 1
      
  and compare_pats pl pl' =
    match pl, pl' with
    | hd :: tl, hd' :: tl' ->
      let x = pat_compare hd hd' in
	if Int.equal x 0 then compare_pats tl tl'
	else x
    | [], [] -> 0
    | _ :: _, _ -> 1
    | [], _ :: _ -> -1
      
  let compare (p, q) (r, s) =
    let x = pat_compare p r in
      if Int.equal x 0 then pat_compare q s
      else x
end

module ProblemSet = Set.Make(MatchingProblem)

let specialize_pb sigma rho (l, r) =
  let spec = specialize sigma (pi2 rho) in
    (spec l, spec r)

let specialize_pbs sigma rho pbs =
  ProblemSet.map (specialize_pb sigma rho) pbs

let pp_pb env sigma (l, r) =
  let open Pp in
    pr_pat env sigma l ++ str" =? " ++ pr_pat env sigma r 
  
let pp_pbs env sigma pbs =
  let open Pp in
    ProblemSet.fold (fun pb acc ->
      pp_pb env sigma pb ++ spc () ++ acc)
      pbs (mt ())

let pr_one_pb env sigma (inner, pbs) =
  let open Pp in
  pr_context_map env sigma inner ++ str " | " ++
    pp_pbs (push_rel_context (pi1 inner) env) sigma pbs

let pr_all_pbs env sigma pbs =
  let open Pp in
    prlist_with_sep spc (pr_one_pb env sigma) pbs
      
type matching_problem = ProblemSet.t    
type clause = rel_context * matching_problem
type problems = rel_context * clause list

let rec pattern_of_constr sigma c =
  let f, args = decompose_app sigma c in
  match kind sigma f with
  | Construct (c, u) -> PCstr ((c, u), List.map (pattern_of_constr sigma) args)
  | Rel n when List.is_empty args -> PRel n
  | _ -> PInac c

let rec decompose_pattern env sigma p c =
  match p, c with
  | p, PRel i ->
    ProblemSet.singleton (p, c)
  | PCstr ((c,_), pl), PCstr ((c', _), pl') -> 
    if Names.eq_constructor c c' then
      decompose_patterns env sigma pl pl'
    else raise Conflict
  | PInac t, u ->
    let uc = pat_constr u in
      if is_conv env sigma t uc then ProblemSet.empty
      else ProblemSet.singleton (p, c)
  | _, _ -> ProblemSet.singleton (p, c)

and decompose_patterns env sigma pl l =
  match pl, l with
  | [], [] -> ProblemSet.empty
  | hd :: tl, hd' :: tl' -> 
    let pbs = decompose_pattern env sigma hd hd' in
      ProblemSet.union pbs (decompose_patterns env sigma tl tl')
  | _, _ -> raise Conflict

let decompose_problems env sigma pbs =
  ProblemSet.fold (fun (l, r) acc ->
    ProblemSet.union (decompose_pattern env sigma l r) acc)
    pbs ProblemSet.empty

let name_ctx ctx =
  let open Names in
  let open Context.Rel.Declaration in
    List.map (fun decl ->
      match get_name decl with
      | Anonymous -> set_name (Name (Id.of_string "var")) decl
      | Name _ -> decl)
      ctx

let make_inversion_pb env sigma (ind, u) na : problems * constr * Syntax.rec_type option =
  let indu = (ind, EInstance.kind sigma u) in
  let arity = EConstr.of_constr (Inductiveops.type_of_inductive env indu) in
  let cstrs = Array.map EConstr.of_constr (Inductiveops.type_of_constructors env indu) in
  let outer, sort = splay_prod_assum env sigma arity in (* With lets *)
  let recursive =
    let (mib, oib) = Inductive.lookup_mind_specif env ind in
      mib.Declarations.mind_finite == Declarations.Finite
  in
  let init_ctx, rec_info =
    if recursive then
      let ctx = [Context.Rel.Declaration.LocalAssum (Names.Name na, arity)] in
      let rec_info =
	Syntax.Structural [(na, Syntax.StructuralOn 0, None)]
      in ctx, Some rec_info
    else [], None
  in
  let outer = name_ctx outer @ init_ctx in
  let env = push_rel_context init_ctx env in
  let params = Inductiveops.inductive_nparams_env env ind in
  let _paramsdecls = Inductiveops.inductive_nparamdecls_env env ind in
  let realdecls = Inductiveops.inductive_nrealdecls_env env ind in
  let args_ctx, params_ctx = CList.chop realdecls outer in
  let params_rels = Context.Rel.to_extended_vect mkRel realdecls params_ctx in
  let realargs_rels = Context.Rel.to_extended_vect mkRel 0 args_ctx in
  let params_env = push_rel_context params_ctx env in
  let problems =
    Array.map_to_list (fun ty ->
      let instty = hnf_prod_appvect params_env sigma ty params_rels in
      let inner, concl = splay_prod_assum params_env sigma instty in
      let hd, args = decompose_app_vect sigma concl in (* I pars args *)
      let cpars, cargs = Array.chop params args in
      let pbs = Array.map2 (fun oarg carg ->
	(pattern_of_constr sigma oarg, pattern_of_constr sigma carg))
	realargs_rels cargs
      in
      let pbs = 
	Array.fold_left (fun acc (l, r) ->
	  ProblemSet.add (l, r) acc) ProblemSet.empty pbs
      in inner, pbs) cstrs
  in
    (outer, problems), sort, rec_info

let is_prel_pat n = function
  | PRel n' -> Int.equal n n'
  | _ -> false
    
let is_constructor_pat = function
  | PCstr _ -> true
  | _ -> false

let make_telescope evdref g =
  if List.is_empty g then
    let sigma, g = Evarutil.new_global !evdref (Equations_common.get_one ()) in
      (evdref := sigma; g)
  else
    let c, ctx, p = Sigma_types.telescope evdref g in c
						     
let find_split env sigma outer problems =
  let do_split x =
    let do_split (inner, pbs) =
      let open Pp in
      let () = Feedback.msg_debug (str"splitting on: " ++ int x ++ str" in " ++ pr_one_pb env sigma (inner, pbs)) in
      let diff = List.length (pi1 inner) - List.length outer in
      let x = x + diff in
	ProblemSet.exists (fun (l, r) -> is_prel_pat x l && is_constructor_pat r) pbs
    in
      List.for_all do_split problems
  in
  let len = List.length outer in (* Lets? *)
  let rec aux i =
    if i < len then
      if do_split (succ i) then Some (succ i)
      else aux (succ i)
    else None
  in aux 0

let solve_problems env sigma rho pbs =
  let rec aux rho' pbs postponed =
    if ProblemSet.is_empty pbs then
      (compose_subst env ~sigma rho' rho,
       specialize_pbs sigma rho' postponed)
    else 
      let pb = ProblemSet.choose pbs in
      let pbs = ProblemSet.remove pb pbs in
      let (l, r) = specialize_pb sigma rho' pb in
	match l, r with
	| _, PRel i -> 
	  let rho'' = single_subst env sigma i l (pi1 rho') in
	    aux (compose_subst env ~sigma rho'' rho') pbs postponed
	| PInac t, u ->
	  let uc = pat_constr u in
	    if is_conv env sigma t uc then aux rho' pbs postponed
	    else aux rho' pbs (ProblemSet.add pb postponed)
	| _, _ -> aux rho' pbs (ProblemSet.add pb postponed)
  in aux (id_subst (pi1 rho)) pbs ProblemSet.empty
    
let simplify_problems env sigma problems =
  let open Pp in
  let aux (rho, pbs) =
    try
      let () = Feedback.msg_debug (str"decomposing: " ++ pp_pbs env sigma pbs) in
      let pbs = decompose_problems env sigma pbs in
      let () = Feedback.msg_debug (str"decomposed: " ++ pp_pbs env sigma pbs) in
      let rho, pbs = solve_problems env sigma rho pbs in
      let () = Feedback.msg_debug (str"solved: " ++ pp_pbs env sigma pbs) in
      let pbs = decompose_problems env sigma pbs in
      let () = Feedback.msg_debug (str"decomposing postponed: " ++ pp_pbs env sigma pbs) in
	Some (solve_problems env sigma rho pbs)
    with Conflict ->
      Feedback.msg_debug (str"Conflict!");
      None
    | Stuck ->
      Feedback.msg_debug (str"Stuck!");
      Some (rho, pbs)
  in List.map_filter aux problems

let solve_problem env sigma ty (outer, problems) =
  let problems = List.map (fun (inner, pbs) ->
     (* outer ; inner |- .. : outer ; inner *)
    let subst = id_subst (inner @ outer) in
    let pbs = ProblemSet.map (fun (l, r) -> (lift_pat (List.length inner) l, r)) pbs in
      (subst, pbs))
    problems
  in
  let update_problems pbs s (* outer' |- .. : outer *) =
    let update_problem (rho, pbs) =
      let gamma = pi1 rho in (* outer', gamma *)
      let innerlen = List.length gamma - List.length (pi3 s) in
      let s' = lift_subst env sigma s (List.firstn innerlen gamma) in
      (* outer', gamma |- s' : outer ; gamma *)
	(compose_subst env ~sigma s' rho, specialize_pbs sigma s' pbs)
    in List.map update_problem pbs
  in
  let sigma, coq_false = Evarutil.new_global sigma (Equations_common.get_zero ()) in
  let evdref = ref sigma in
  let rec aux (outer, problems) lhs =
    let () = Feedback.msg_debug Pp.(str"Simplifying pbs: " ++ pr_all_pbs env sigma problems) in
    let pbs = simplify_problems env !evdref problems in
    let () = Feedback.msg_debug Pp.(str"Simplified pbs: " ++ pr_all_pbs env sigma pbs) in
      match pbs with
      | [] -> (* No matching constructor *)
	Compute (lhs, [], ty, RProgram coq_false)
      | [(subst, pbs)] when ProblemSet.is_empty pbs ->
	(* Found a single matching constructor *)
	let innerlen = List.length (pi1 subst) - List.length outer in
	let inner = List.firstn innerlen (pi1 subst) in
	Compute (lhs, [], ty, RProgram (make_telescope evdref inner))
      | _ ->
	match find_split env sigma outer pbs with
	| Some var ->
	  (match split_var (env, evdref) var outer with
	  | Some (k, newctx, split) -> (* outer' |- s : outer *)
	    let branches sopt =
	      match sopt with
	      | None -> None
	      | Some s ->
		let problems' = update_problems pbs s in
		  Some (aux (pi1 s, problems') (compose_subst env ~sigma:!evdref s lhs))
	    in
	      Split (lhs, var, ty, Array.map branches split)
	  | None -> CErrors.user_err (Pp.str"Couldn't split variable!"))
	| None -> CErrors.user_err (Pp.str"No variable can be split")
  in
  let splitting = aux (outer, problems) (id_subst outer) in
    !evdref, splitting
    
let derive_inversion env sigma ~polymorphic indu =
  let na = Nametab.basename_of_global (Names.GlobRef.IndRef (fst indu)) in
  let name = Nameops.add_prefix "invert_" na in
  let (outer, _ as problems), ty, rec_info = make_inversion_pb env sigma indu name in
  let sigma, ty = Evarsolve.refresh_universes (Some false) env sigma ty in
  let sigma, splitting = solve_problem env sigma ty problems in
  let hook splitting cmap terminfo ustate = () in
    Splitting.define_tree rec_info outer false [] (Evar_kinds.Define false)
      (ref sigma) env (name, outer, ty) None splitting hook

let _derive =
  Derive.(register_derive { derive_name = "Invert";
			    derive_fn = make_derive_ind derive_inversion })
