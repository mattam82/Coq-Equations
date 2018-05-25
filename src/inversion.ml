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

type matching_problem = pat list * pat list
type clause = rel_context * matching_problem
type problems = rel_context * clause list

let rec pattern_of_constr sigma c =
  let f, args = decompose_app sigma c in
  match kind sigma f with
  | Construct (c, u) -> PCstr ((c, u), List.map (pattern_of_constr sigma) args)
  | Rel n when List.is_empty args -> PRel n
  | _ -> PInac c

let rec match_pattern env sigma gamma p c =
  match p, c with
  | p, PRel i ->
    let rho = single_subst env sigma i p gamma in
      rho, ([], [])
  | PCstr ((c,_), pl), PCstr ((c', _), pl') -> 
    if Names.eq_constructor c c' then
      match_patterns env sigma gamma pl pl'
    else raise Conflict
  | PInac t, u ->
    let uc = pat_constr u in
      if is_conv env sigma t uc then id_subst gamma, ([], [])
      else id_subst gamma, ([p], [c])
  | _, _ -> raise Stuck
	
and match_patterns env sigma gamma pl l =
  match pl, l with
  | [], [] -> id_subst gamma, ([], [])
  | hd :: tl, hd' :: tl' -> 
    let rho, rest = match_pattern env sigma gamma hd hd' in
    let gamma' = pi1 rho in
    let spec = specialize_pats sigma (pi2 rho) in
    let rho', rest' =
      match_patterns env sigma gamma' (spec tl) (spec tl')
    in
    let spec' = specialize_pats sigma (pi2 rho') in
      compose_subst env ~sigma rho' rho, (spec' (fst rest) @ fst rest', spec' (snd rest) @ snd rest')
  | _ -> raise Conflict

let name_ctx ctx =
  let open Names in
  let open Context.Rel.Declaration in
    List.map (fun decl ->
      match get_name decl with
      | Anonymous -> set_name (Name (Id.of_string "var")) decl
      | Name _ -> decl)
      ctx

let make_inversion_pb env sigma (ind, u) : problems * constr =
  let indu = (ind, EInstance.kind sigma u) in
  let arity = EConstr.of_constr (Inductiveops.type_of_inductive env indu) in
  let cstrs = Array.map EConstr.of_constr (Inductiveops.type_of_constructors env indu) in
  let outer, sort = splay_prod_assum env sigma arity in (* With lets *)
  let outer = name_ctx outer in
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
      in inner, CList.split (Array.to_list pbs)) cstrs
  in
    (outer, problems), sort

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

let find_split outer problems =
  let do_split x =
    let do_split (inner, (l, r)) =
      let diff = List.length (pi1 inner) - List.length outer in
      let x = x + diff in
	List.exists2 (fun l r -> is_prel_pat x l && is_constructor_pat r) l r
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
						
let simplify_problems env sigma problems =
  let aux (rho, (l, r as pbs)) =
    try
      let rho', (l, r) = match_patterns env sigma (pi1 rho) l r in
      let rho' = compose_subst env ~sigma rho' rho in
      let rho'', rest' = match_patterns env sigma (pi1 rho') l r in
	Some (rho'', rest')
    with Conflict -> None
    | Stuck -> Some (rho, pbs)
  in List.map_filter aux problems

let solve_problem env sigma ty (outer, problems) =
  let problems = List.map (fun (inner, (l, r)) ->
     (* outer ; inner |- .. : outer ; inner *)
    let subst = id_subst (inner @ outer) in
      (subst, (List.map (lift_pat (List.length inner)) l, r)))
    problems
  in
  let update_problems pbs s (* outer' |- .. : outer *) =
    let update_problem (rho, (l, r)) =
      let gamma = pi1 rho in (* outer', gamma *)
      let innerlen = List.length gamma - List.length (pi3 s) in
      let s' = lift_subst env sigma s (List.firstn innerlen gamma) in
      (* outer', gamma |- s' : outer ; gamma *)
	(compose_subst env ~sigma s' rho,
	 (specialize_pats sigma (pi2 s') l,
	  specialize_pats sigma (pi2 s') r))
    in List.map update_problem pbs
  in
  let sigma, coq_false = Evarutil.new_global sigma (Equations_common.get_zero ()) in
  let evdref = ref sigma in
  let rec aux (outer, problems) lhs =
    let pbs = simplify_problems env !evdref problems in
      match pbs with
      | [] -> (* No matching constructor *)
	Compute (lhs, [], ty, RProgram coq_false)
      | [(subst, ([], []))] -> (* Found a single matching constructor *)
	let innerlen = List.length (pi1 subst) - List.length outer in
	let inner = List.firstn innerlen (pi1 subst) in
	Compute (lhs, [], ty, RProgram (make_telescope evdref inner))
      | _ ->
	match find_split outer pbs with
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
  let (outer, _ as problems), ty = make_inversion_pb env sigma indu in
  let sigma, ty = Evarsolve.refresh_universes (Some false) env sigma ty in
  let sigma, splitting = solve_problem env sigma ty problems in
  let hook splitting cmap terminfo ustate = () in
  let rec_info = None in
    Splitting.define_tree rec_info outer false [] (Evar_kinds.Define false)
      (ref sigma) env (name, outer, ty) None splitting hook

let _derive =
  Derive.(register_derive { derive_name = "Invert";
			    derive_fn = make_derive_ind derive_inversion })
