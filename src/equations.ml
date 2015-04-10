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
open Printer
open Ppconstr
open Decl_kinds
open Constrintern
open Syntax
open Covering
open Splitting

let abstract_rec_calls ?(do_subst=true) is_rec len protos c =
  let lenprotos = length protos in
  let proto_fs = map (fun (f, _, _, _) -> f) protos in
  let find_rec_call f =
    try Some (List.find (fun (f', alias, idx, arity) ->
      eq_constr (fst (decompose_app f')) f || 
	(match alias with Some f' -> eq_constr f' f | None -> false)) protos) 
    with Not_found -> None
  in
  let find_rec_call f args =
    match find_rec_call f with
    | Some (f', _, i, arity) -> 
	let args' = snd (Array.chop (length (snd (decompose_app f'))) args) in
	Some (i, arity, args')
    | None -> 
	match is_rec with
	| Some (Logical r) when eq_constr (mkConst r.comp_proj) f -> 
	    Some (lenprotos - 1, r.comp_app, array_remove_last args)
	| _ -> None
  in
  let rec aux n env c =
    match kind_of_term c with
    | App (f', args) ->
	let (ctx, lenctx, args) = 
	  Array.fold_left (fun (ctx,len,c) arg -> 
	    let ctx', lenctx', arg' = aux n env arg in
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
	    
    | Lambda (na,t,b) ->
	let ctx',lenctx',b' = aux (succ n) ((na,None,t) :: env) b in
	  (match ctx' with
	   | [] -> [], 0, c
	   | hyp :: rest -> 
	       let ty = mkProd (na, t, it_mkProd_or_LetIn (pi3 hyp) rest) in
		 [Anonymous, None, ty], 1, lift 1 c)

    (* | Cast (_, _, f) when is_comp f -> aux n f *)
	  
    | LetIn (na,b,t,c) ->
	let ctx',lenctx',b' = aux n env b in
	let ctx'',lenctx'',c' = aux (succ n) ((na,Some b,t) :: env) c in
	let ctx'' = lift_rel_contextn 1 lenctx' ctx'' in
	let fullctx = ctx'' @ [na,Some b',lift lenctx' t] @ ctx' in
	  fullctx, lenctx'+lenctx''+1, liftn lenctx' (lenctx'' + 2) c'

    | Prod (na, d, c) when not (dependent (mkRel 1) c)  -> 
	let ctx',lenctx',d' = aux n env d in
	let ctx'',lenctx'',c' = aux n env (subst1 mkProp c) in
	  lift_context lenctx' ctx'' @ ctx', lenctx' + lenctx'', 
	mkProd (na, lift lenctx'' d', 
	       liftn lenctx' (lenctx'' + 2) 
		 (lift 1 c'))

    | Case (ci, p, c, br) ->
	let ctx', lenctx', c' = aux n env c in
	let case' = mkCase (ci, lift lenctx' p, c', Array.map (lift lenctx') br) in
	  ctx', lenctx', substnl proto_fs (succ len + lenctx') case'

    | _ -> [], 0, if do_subst then (substnl proto_fs (len + n) c) else c
  in aux 0 [] c

let below_transparent_state () =
  Hints.Hint_db.transparent_state (Hints.searchtable_map "Below")

let simpl_star = 
  tclTHEN simpl_in_concl (onAllHyps (fun id -> simpl_in_hyp (id, Locus.InHyp)))

let eauto_with_below l =
  Class_tactics.typeclasses_eauto
    ~st:(below_transparent_state ()) (l@["subterm_relation"; "Below"; "rec_decision"])

let simp_eqns l =
  tclREPEAT (tclTHENLIST [Proofview.V82.of_tactic 
			     (Autorewrite.autorewrite (Tacticals.New.tclIDTAC) l);
			  (* simpl_star; Autorewrite.autorewrite tclIDTAC l; *)
			  tclTRY (eauto_with_below l)])

let simp_eqns_in clause l =
  tclREPEAT (tclTHENLIST 
		[Proofview.V82.of_tactic
		    (Autorewrite.auto_multi_rewrite l clause);
		 tclTRY (eauto_with_below l)])

let autorewrites b = 
  tclREPEAT (Proofview.V82.of_tactic (Autorewrite.autorewrite Tacticals.New.tclIDTAC [b]))

let autorewrite_one b =  (*FIXME*)
  (Proofview.V82.of_tactic (Autorewrite.autorewrite Tacticals.New.tclIDTAC [b]))

(* let autorewrite_one b = Rewrite.cl_rewrite_clause_strat  *)
(*   (Rewrite.Strategies.innermost (Rewrite.Strategies.hints b)) *)
(*   None *)

type term_info = {
  base_id : string;
  polymorphic : bool;
  helpers_info : (existential_key * int * identifier) list }

let find_helper_info info f =
  try List.find (fun (ev', arg', id') ->
    eq_constr (Constrintern.global_reference id') f) info.helpers_info
  with Not_found -> anomaly (str"Helper not found while proving induction lemma.")

let inline_helpers i = 
  let l = List.map (fun (_, _, id) -> Ident (dummy_loc, id)) i.helpers_info in
    Table.extraction_inline true l

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

let rec intros_reducing gl =
  let concl = pf_concl gl in
    match kind_of_term concl with
    | LetIn (_, _, _, _) -> tclTHEN hnf_in_concl intros_reducing gl
    | Prod (_, _, _) -> tclTHEN intro intros_reducing gl
    | _ -> tclIDTAC gl

let rec aux_ind_fun info = function
  | Split ((ctx,pats,_), var, _, splits) ->
      tclTHEN_i (fun gl ->
	match kind_of_term (pf_concl gl) with
	| App (ind, args) -> 
	    let pats' = List.drop_last (Array.to_list args) in
	    let pats = filter (fun x -> not (hidden x)) pats in
	    let id = find_splitting_var pats var pats' in
	      to82 (depelim_nosimpl_tac id) gl
	| _ -> tclFAIL 0 (str"Unexpected goal in functional induction proof") gl)
	(fun i -> 
	  match splits.(pred i) with
	  | None -> to82 (simpl_dep_elim_tac ())
	  | Some s ->
	      tclTHEN (to82 (simpl_dep_elim_tac ()))
		(aux_ind_fun info s))
	  
  | Valid ((ctx, _, _), ty, substc, tac, valid, rest) -> tclTHEN (to82 intros)
      (tclTHEN_i tac (fun i -> let _, _, subst, split = nth rest (pred i) in
				 tclTHEN (Lazy.force unfold_add_pattern) 
				   (aux_ind_fun info split)))
      
  | RecValid (id, cs) -> aux_ind_fun info cs
      
  | Refined ((ctx, _, _), refinfo, s) -> 
      let id = pi1 refinfo.refined_obj in
      let elimtac gl =
	match kind_of_term (pf_concl gl) with
	| App (ind, args) ->
	    let last_arg = args.(Array.length args - 1) in
	    let f, args = destApp last_arg in
	    let _, elim = find_helper_arg info f args in
	    let id = pf_get_new_id id gl in
	      tclTHENLIST
		[to82 (letin_tac None (Name id) elim None Locusops.allHypsAndConcl); 
		 Proofview.V82.of_tactic (clear_body [id]); aux_ind_fun info s] gl
	| _ -> tclFAIL 0 (str"Unexpected refinement goal in functional induction proof") gl
      in
      let cstrtac =
	tclTHENLIST [tclTRY (autorewrite_one info.base_id); to82 (any_constructor false None)]
      in tclTHENLIST [ to82 intros; tclTHENLAST cstrtac (tclSOLVE [elimtac]); to82 (solve_rec_tac ())]

  | Compute (_, _, REmpty _) ->
      tclTHENLIST [intros_reducing; to82 (find_empty_tac ())]
	
  | Compute (_, _, _) ->
      tclTHENLIST [intros_reducing; autorewrite_one info.base_id; eauto_with_below [info.base_id]]
	
  (* | Compute ((ctx,_,_), _, REmpty id) -> *)
  (*     let (na,_,_) = nth ctx (pred id) in *)
  (*     let id = out_name na in *)
  (* 	do_empty_tac id *)

let ind_fun_tac is_rec f info fid split ind =
  if is_structural is_rec then
    let c = constant_value_in (Global.env ()) (destConst f) in
    let i = let (inds, _), _ = destFix c in inds.(0) in
    let recid = add_suffix fid "_rec" in
      (* tclCOMPLETE  *)
      (tclTHENLIST
	  [fix (Some recid) (succ i);
	   onLastDecl (fun (n,b,t) gl ->
	     let sort = pf_type_of gl t in
	     let fixprot = mkApp ((*FIXME*)Universes.constr_of_global (Lazy.force coq_fix_proto), [|sort; t|]) in
	       Proofview.V82.of_tactic (change_in_hyp None (make_change_arg fixprot) (n, Locus.InHyp)) gl);
	   to82 intros; aux_ind_fun info split])
  else tclCOMPLETE (tclTHEN (to82 intros) (aux_ind_fun info split))

let subst_rec_split redefine f prob s split = 
  let subst_rec cutprob s (ctx, p, _ as lhs) =
    let subst = 
      fold_left (fun (ctx, _, _ as lhs') (id, b) ->
	  let rel, _, ty = lookup_rel_id id ctx in
	  let fK = 
	    if redefine then
	      let lctx, ty = decompose_prod_assum (lift rel ty) in
	      let fcomp, args = decompose_app ty in
		it_mkLambda_or_LetIn (applistc f args) lctx
	    else f
	  in
	  let substf = single_subst Evd.empty rel (PInac fK) ctx (* ctx[n := f] |- _ : ctx *) in
	    compose_subst substf lhs') (id_subst ctx) s
    in
      subst, compose_subst (compose_subst subst lhs) cutprob
  in
  let rec aux cutprob s path = function
    | Compute ((ctx,pats,del as lhs), ty, c) ->
	let subst, lhs' = subst_rec cutprob s lhs in	  
	  Compute (lhs', mapping_constr subst ty, mapping_rhs subst c)
	  
    | Split (lhs, n, ty, cs) -> 
	let subst, lhs' = subst_rec cutprob s lhs in
	let n' = destRel (mapping_constr subst (mkRel n)) in
	  Split (lhs', n', mapping_constr subst ty, Array.map (Option.map (aux cutprob s path)) cs)
	  
    | RecValid (id, c) ->
	RecValid (id, aux cutprob s path c)
	  
    | Refined (lhs, info, sp) -> 
	let (id, c, cty), ty, arg, ev, (fev, args), revctx, newprob, newty =
	  info.refined_obj, info.refined_rettyp,
	  info.refined_arg, info.refined_ex, info.refined_app,
	  info.refined_revctx, info.refined_newprob, info.refined_newty
	in
	let subst, lhs' = subst_rec cutprob s lhs in
	let cutprob ctx' = 
	  let pats, cutctx', _, _ =
	    (* From Γ |- ps, prec, ps' : Δ, rec, Δ', build
	       Γ |- ps, ps' : Δ, Δ' *)
	    fold_right (fun (n, b, t) (pats, ctx', i, subs) ->
			match n with
			| Name n when mem_assoc n s ->
			  let term = assoc n s in
			    (pats, ctx', pred i, term :: subs)
			| _ -> (i :: pats, (n, Option.map (substl subs) b, substl subs t) :: ctx', 
				pred i, mkRel 1 :: map (lift 1) subs))
	    ctx' ([], [], length ctx', [])
 	  in (ctx', map (fun i -> PRel i) pats, cutctx')
	in
        let _, revctx' = subst_rec (cutprob (pi3 revctx)) s revctx in
	let cutnewprob = cutprob (pi3 newprob) in
	let subst', newprob' = subst_rec cutnewprob s newprob in
	let _, newprob_to_prob' = 
	  subst_rec (cutprob (pi3 info.refined_newprob_to_lhs)) s info.refined_newprob_to_lhs in
	let ev' = if redefine then new_untyped_evar () else ev in
	let path' = ev' :: path in
	let app', arg' =
	  if redefine then
	    let refarg = ref 0 in
  	    let args' = List.fold_left_i
	      (fun i acc c -> 
		 if i == arg then (refarg := List.length acc);
		 if isRel c then
		   let (n, _, ty) = List.nth (pi1 lhs) (pred (destRel c)) in
		     if mem_assoc (out_name n) s then acc
		     else (mapping_constr subst c) :: acc
		 else (mapping_constr subst c) :: acc) 0 [] args 
	    in (mkEvar (ev', [||]), rev args'), !refarg
	  else 
	    let first, last = List.chop (length s) (map (mapping_constr subst) args) in
	      (applistc (mapping_constr subst fev) first, last), arg - length s (* FIXME , needs substituted position too *)
	in
	let info =
	  { refined_obj = (id, mapping_constr subst c, mapping_constr subst cty);
	    refined_rettyp = mapping_constr subst ty;
	    refined_arg = arg';
	    refined_path = path';
	    refined_ex = ev';
	    refined_app = app';
	    refined_revctx = revctx';
	    refined_newprob = newprob';
	    refined_newprob_to_lhs = newprob_to_prob';
	    refined_newty = mapping_constr subst' newty }
	in Refined (lhs', info, aux cutnewprob s path' sp)

    | Valid (lhs, x, y, w, u, cs) -> 
	let subst, lhs' = subst_rec cutprob s lhs in
	  Valid (lhs', x, y, w, u, 
		List.map (fun (g, l, subst, sp) -> (g, l, subst, aux cutprob s path sp)) cs)
  in aux prob s [] split

type statement = constr * types option
type statements = statement list

let subst_app f fn c = 
  let rec aux n c =
    match kind_of_term c with
    | App (f', args) when eq_constr f f' -> 
      let args' = Array.map (map_constr_with_binders succ aux n) args in
	fn n f' args'
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
	    let (ind', _), _ = destInd t in
	      if eq_mind ind' ind then (
		assert(not (dependent (mkRel 1) c));
		clear_assums (subst1 mkProp c))
	      else mkProd (na, b, clear_assums c)
	  else mkProd (na, b, clear_assums c)
    | LetIn (na, b, t, c) ->
	mkLetIn (na, b, t, clear_assums c)
    | _ -> c
  in map_rel_context clear_assums ctx

let unfold s = Tactics.unfold_in_concl [Locus.AllOccurrences, s]

let ind_elim_tac indid inds info gl = 
  let eauto = Class_tactics.typeclasses_eauto [info.base_id; "funelim"] in
  let _nhyps = List.length (pf_hyps gl) in
  let prove_methods tac gl = 
    tclTHEN tac (tclTHEN simpl_in_concl eauto) gl
  in
  let rec applyind args gl =
    match kind_of_term (pf_concl gl) with
    | LetIn (Name id, b, t, t') ->
	tclTHENLIST [Proofview.V82.of_tactic (convert_concl_no_check (subst1 b t') DEFAULTcast);
		     applyind (b :: args)] gl
    | _ -> tclTHENLIST [simpl_in_concl; to82 intros; 
			prove_methods (Proofview.V82.of_tactic (apply (nf_beta (project gl) (applistc indid (rev args)))))] gl
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
	
    | Refined (lhs, info, cs) ->
	let (id, c, t) = info.refined_obj in
	let (ctx', pats', _ as s) = compose_subst lhs prob in
	let patsconstrs = rev_map pat_constr pats' in
	  [pi1 lhs, patsconstrs, info.refined_rettyp, f, true, RProgram (applist info.refined_app),
	   Some (fst (info.refined_app), info.refined_path, pi1 info.refined_newprob,  info.refined_newty,
	         rev_map pat_constr (pi2 (compose_subst info.refined_newprob_to_lhs s)), 
		 [mapping_constr info.refined_newprob_to_lhs c, info.refined_arg],
		 computations info.refined_newprob (fst info.refined_app) cs)]
	   
    | Valid ((ctx,pats,del), _, _, _, _, cs) -> 
	List.fold_left (fun acc (_, _, subst, c) ->
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
    List.map_i (fun i (f', path, sign, arity, pats, args) -> 
      (f', (if eq_constr f' f then Option.map pi1 alias else None), lenprotos - i, arity))
      1 protos
  in
  let evd = ref (Evd.from_env env) in
  let rec statement i f (ctx, pats, ty, f', refine, c) =
    let comp = applistc f pats in
    let body =
      let b = match c with
	| RProgram c ->
	    mkEq evd ty comp (nf_beta Evd.empty c)
	| REmpty i ->
	    (* mkLetIn (Anonymous, comp, ty,  *)
	  let t = mkApp (Lazy.force coq_ImpossibleCall, [| ty; comp |]) in
	    t
      in it_mkProd_or_LetIn b ctx
    in
    let cstr = 
      match c with
      | RProgram c ->
	  let len = List.length ctx in
	  let hyps, hypslen, c' = abstract_rec_calls is_rec len protos (nf_beta Evd.empty c) in
	    Some (it_mkProd_or_clear
		     (it_mkProd_or_clean
			 (applistc (mkRel (len + (lenprotos - i) + hypslen))
			     (lift_constrs hypslen pats @ [c']))
			 hyps) ctx)
      | REmpty i -> None
    in (refine, body, cstr)
  in
  let statements i ((f', path, sign, arity, pats, args as fs), c) = 
    let fs, f', unftac = 
      if eq_constr f' f then 
	match alias with
	| Some (f', unf, split) -> 
	    (f', path, sign, arity, pats, args), f', Equality.rewriteLR unf
	| None -> fs, f', Tacticals.New.tclIDTAC
      else fs, f', Tacticals.New.tclIDTAC
    in fs, unftac, map (statement i f') c in
  let stmts = List.map_i statements 0 comps in
  let ind_stmts = List.map_i 
    (fun i (f, unf, c) -> i, f, unf, List.map_i (fun j x -> j, x) 1 c) 0 stmts 
  in
  let all_stmts = concat (map (fun (f, unf, c) -> c) stmts) in 
  let declare_one_ind (i, (f, path, sign, arity, pats, refs), unf, stmts) = 
    let indid = add_suffix id (if i == 0 then "_ind" else ("_ind_" ^ string_of_int i)) in
    let constructors = List.map_filter (fun (_, (_, _, n)) -> n) stmts in
    let consnames = List.map_filter (fun (i, (r, _, n)) -> 
      Option.map (fun _ -> 
	let suff = (if not r then "_equation_" else "_refinement_") ^ string_of_int i in
	  add_suffix indid suff) n) stmts
    in
      { mind_entry_typename = indid;
	mind_entry_arity = it_mkProd_or_LetIn (mkProd (Anonymous, arity, mkProp)) sign;
	mind_entry_consnames = consnames;	      
	mind_entry_lc = constructors;
	mind_entry_template = false }
  in
  let declare_ind () =
    let inds = map declare_one_ind ind_stmts in
    let inductive =
      { mind_entry_record = None;
	mind_entry_polymorphic = false;
	mind_entry_universes = Evd.universe_context !evd;
	mind_entry_private = None;
	mind_entry_finite = Finite;
	mind_entry_params = []; (* (identifier * local_entry) list; *)
	mind_entry_inds = inds }
    in
    let k = Command.declare_mutual_inductive_with_eliminations inductive [] in
    let ind = mkInd (k,0) in
    let _ =
      List.iteri (fun i ind ->
	let constrs = 
	  List.map_i (fun j _ -> None, info.polymorphic, true, Hints.PathAny, 
	    Hints.IsGlobRef (ConstructRef ((k,i),j))) 1 ind.mind_entry_lc in
	  Hints.add_hints false [info.base_id] (Hints.HintsResolveEntry constrs))
	inds
    in
    let indid = add_suffix id "_ind_fun" in
    let args = rel_list 0 (List.length sign) in
    let f, split = match alias with Some (f, _, split) -> f, split | None -> f, split in
    let app = applist (f, args) in
    let statement = it_mkProd_or_subst (applist (ind, args @ [app])) sign in
    let evd = Evd.empty in
    let hookind subst gr = 
      let env = Global.env () in (* refresh *)
      Hints.add_hints false [info.base_id] 
	(Hints.HintsImmediateEntry [Hints.PathAny, info.polymorphic, Hints.IsGlobRef gr]);
      let _funind_stmt =
	let evd = ref Evd.empty in
	let leninds = List.length inds in
	let elim =
	  if leninds > 1 then
	    (Indschemes.do_mutual_induction_scheme
		(List.map_i (fun i ind ->
		  let id = (dummy_loc, add_suffix ind.mind_entry_typename "_mut") in
		    (id, false, (k, i), Misctypes.GProp)) 0 inds);
	     let elimid = 
	       add_suffix (List.hd inds).mind_entry_typename "_mut"
	     in Smartlocate.global_with_alias (reference_of_id elimid))
	  else 
	    let elimid = add_suffix id "_ind_ind" in
	      Smartlocate.global_with_alias (reference_of_id elimid) 
	in
	let elimty = Global.type_of_global_unsafe elim in
	let ctx, arity = decompose_prod_assum elimty in
	let newctx = List.skipn (length sign + 2) ctx in
	let newarity = it_mkProd_or_LetIn (substl [mkProp; app] arity) sign in
	let newctx' = clear_ind_assums k newctx in
	let newty =
	  if leninds == 1 then it_mkProd_or_LetIn newarity newctx'
	  else
	    let methods, preds = List.chop (List.length newctx - leninds) newctx' in
	    let ppred, preds = List.sep_last preds in
	    let newpreds =
	      List.map2_i (fun i (n, b, t) (idx, (f', path, sign, arity, pats, args), _, _) ->
		let signlen = List.length sign in
		let ctx = (Anonymous, None, arity) :: sign in
		let app =
		  let argsinfo =
		    List.map_i (fun i (c, arg) -> 
				  let idx = signlen - arg + 1 in (* lift 1, over return value *)
				  let ty = lift (idx (* 1 for return value *)) 
				    (pi3 (List.nth sign (pred (pred idx)))) 
				  in
				    (idx, ty, lift 1 c, mkRel idx)) 
		      0 args
		  in
		  let lenargs = length argsinfo in
		  let result, _ = 
		    fold_left
  		      (fun (acc, pred) (i, ty, c, rel) -> 
		       let idx = i + 2 * lenargs in
			 if dependent (mkRel idx) pred then
			   let app = 
			     mkApp (global_reference (id_of_string "eq_rect_r"),
				    [| lift lenargs ty; lift lenargs rel;
				       mkLambda (Name (id_of_string "refine"), lift lenargs ty, 
						 (replace_term (mkRel idx) (mkRel 1) pred)); 
				       acc; (lift lenargs c); mkRel 1 (* equality *) |])
			   in (app, subst1 c pred)
			 else (acc, subst1 c pred))
		    (mkRel (succ lenargs), lift (succ (lenargs * 2)) arity)
		    argsinfo
		  in
		  let ppath = (* The preceding P *) 
		    match path with
		    | [] -> assert false
		    | ev :: path -> 
			let res = 
			  list_find_map_i (fun i' (_, (_, path', _, _, _, _), _, _) ->
			    if eq_path path' path then Some (idx + 1 - i')
			    else None) 1 ind_stmts
			in match res with None -> assert false | Some i -> i
		  in
		  let papp =
		    applistc (lift (succ signlen + lenargs) (mkRel ppath)) 
		      (map (lift (lenargs + 1)) pats (* for equalities + return value *))
		  in
		  let papp = fold_right 
		    (fun (i, ty, c, rel) app -> 
		      replace_term (lift (lenargs) c) (lift (lenargs) rel) app) 
		    argsinfo papp 
		  in
		  let papp = applistc papp [result] in
		  let refeqs = map (fun (i, ty, c, rel) -> mkEq evd ty c rel) argsinfo in
		  let app c = fold_right
		    (fun c acc ->
		      mkProd (Name (id_of_string "Heq"), c, acc))
		    refeqs c
		  in
		  let indhyps =
		    concat
		      (map (fun (c, _) ->
			let hyps, hypslen, c' = 
			  abstract_rec_calls ~do_subst:false
			    is_rec signlen protos (nf_beta Evd.empty (lift 1 c)) 
			in 
			let lifthyps = lift_rel_contextn (signlen + 2) (- (pred i)) hyps in
			  lifthyps) args)
		  in
		    it_mkLambda_or_LetIn
		      (app (it_mkProd_or_clean (lift (length indhyps) papp) 
			       (lift_rel_context lenargs indhyps)))
		      ctx
		in
		let ty = it_mkProd_or_LetIn mkProp ctx in
		  (n, Some app, ty)) 
		1 preds (rev (List.tl ind_stmts))
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
		| [], decls -> n, List.rev decls @ meths'
		| _, _ -> assert false
	      in aux all_stmts (rev methods) 0 []
	    in
	      it_mkProd_or_LetIn (lift (-skipped) newarity)
		(methods' @ newpreds @ [ppred])
	in
	let hookelim _ elimgr =
	  let env = Global.env () in
	  let elimcgr = Universes.constr_of_global elimgr in
	  let cl = functional_elimination_class () in
	  let args = [Typing.type_of env Evd.empty f; f; 
		      Typing.type_of env Evd.empty elimcgr; elimcgr]
	  in
	  let instid = add_prefix "FunctionalElimination_" id in
	    ignore(declare_instance instid info.polymorphic 
		     (if info.polymorphic then !evd else Evd.empty) [] cl args)
	in
	  try 
	    (* Conv_oracle.set_strategy (ConstKey cst) Conv_oracle.Expand; *)
	    ignore(Obligations.add_definition (add_suffix id "_elim")
		     ~tactic:(of82 (ind_elim_tac (Universes.constr_of_global elim) leninds info))
		     ~hook:(Lemmas.mk_hook hookelim)
		     newty (Evd.evar_universe_context !evd) [||])
	  with e ->
	    msg_warning 
	      (str "Elimination principle could not be proved automatically: " ++ fnl () ++
		 Errors.print e)
      in
      let cl = functional_induction_class () in
      let evd = Evd.empty in
      let args = [Typing.type_of env evd f; f; 
		  Global.type_of_global_unsafe gr; Universes.constr_of_global gr]
      in
      let instid = add_prefix "FunctionalInduction_" id in
	ignore(declare_instance instid info.polymorphic 
		 (if info.polymorphic then evd else Evd.empty) [] cl args)
    in
      try ignore(Obligations.add_definition ~hook:(Lemmas.mk_hook hookind)
		   indid statement ~tactic:(of82 (ind_fun_tac is_rec f info id split ind))
		   (Evd.evar_universe_context (if info.polymorphic then evd else Evd.empty))
		    [||])
      with e ->
	msg_warning (str "Induction principle could not be proved automatically: " ++ fnl () ++
		Errors.print e)
	  (* ignore(Subtac_obligations.add_definition ~hook:hookind indid statement [||]) *)
  in
  let proof (j, f, unf, stmts) =
    let eqns = Array.make (List.length stmts) false in
    let id = if j != 0 then add_suffix id ("_helper_" ^ string_of_int j) else id in
    let proof (i, (r, c, n)) = 
      let ideq = add_suffix id ("_equation_" ^ string_of_int i) in
      let hook subst gr = 
	if n != None then
	  Autorewrite.add_rew_rules info.base_id 
	    [dummy_loc, Universes.fresh_global_instance (Global.env()) gr, true, None]
	else (Typeclasses.declare_instance None true gr;
	      Hints.add_hints false [info.base_id] 
		(Hints.HintsExternEntry (0, None, impossible_call_tac (ConstRef cst))));
	eqns.(pred i) <- true;
	if Array.for_all (fun x -> x) eqns then (
	  (* From now on, we don't need the reduction behavior of the constant anymore *)
	  Typeclasses.set_typeclass_transparency (EvalConstRef cst) false false;
	  Global.set_strategy (ConstKey cst) Conv_oracle.Opaque;
	  if with_ind && succ j == List.length ind_stmts then declare_ind ())
      in
      let tac = 
	tclTHENLIST [to82 intros; to82 unf; to82 (solve_equation_tac (ConstRef cst) [])]
      in
      let evd = ref Evd.empty in
      let _ = Evarutil.evd_comb1 (Typing.e_type_of (Global.env ())) evd c in
	ignore(Obligations.add_definition
		  ideq c ~tactic:(of82 tac) ~hook:(Lemmas.mk_hook hook)
		  (Evd.evar_universe_context !evd) [||])
    in iter proof stmts
  in iter proof ind_stmts

open Typeclasses

let hintdb_set_transparency cst b db =
  Hints.add_hints false [db] 
    (Hints.HintsTransparencyEntry ([EvalConstRef cst], b))


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
    else Proofview.V82.of_tactic (convert_concl_no_check concl' DEFAULTcast) gl

let unfold_constr c = 
  unfold_in_concl [(Locus.AllOccurrences, EvalConstRef (fst (destConst c)))]

let simpl_except (ids, csts) =
  let csts = Cset.fold Cpred.remove csts Cpred.full in
  let ids = Idset.fold Idpred.remove ids Idpred.full in
    Closure.RedFlags.red_add_transparent Closure.betadeltaiota
      (ids, csts)
      
let simpl_of csts =
  (* let (ids, csts) = Hints.Hint_db.unfolds (Hints.searchtable_map db) in *)
  (* let (ids', csts') = Hints.Hint_db.unfolds (Hints.searchtable_map (db ^ "_unfold")) in *)
  (* let ids, csts = (Idset.union ids ids', Cset.union csts csts') in *)
  let opacify () = List.iter (fun cst -> 
    Global.set_strategy (ConstKey cst) Conv_oracle.Opaque) csts
  and transp () = List.iter (fun cst -> 
    Global.set_strategy (ConstKey cst) Conv_oracle.Expand) csts
  in opacify, transp

  (* let flags = simpl_except  in *)
  (*   reduct_in_concl (Tacred.cbv_norm_flags flags, DEFAULTcast) *)

let prove_unfolding_lemma info proj f_cst funf_cst split gl =
  let depelim h = depelim_tac h in
  let helpercsts = List.map (fun (_, _, i) -> fst (destConst (global_reference i))) info.helpers_info in
  let opacify, transp = simpl_of helpercsts in
  let simpltac gl = opacify ();
    let res = to82 (simpl_equations_tac ()) gl in
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
	      [((Locus.OnlyOccurrences [1]), EvalConstRef f_cst); 
	       ((Locus.OnlyOccurrences [1]), EvalConstRef (fst (destConst proj)))]
	    in 
	      tclTHENLIST [unfolds; simpltac; to82 (pi_tac ())] gl
	  else to82 reflexivity gl
    | _ -> to82 reflexivity gl
  in
  let solve_eq =
    tclORELSE (to82 reflexivity)
      (tclTHEN (tclTRY (to82 Cctac.f_equal)) solve_rec_eq)
  in
  let abstract tac = tclABSTRACT None tac in
  let rec aux = function
    | Split ((ctx,pats,_), var, _, splits) ->
	(fun gl ->
	  match kind_of_term (pf_concl gl) with
	  | App (eq, [| ty; x; y |]) -> 
	      let f, pats' = decompose_app y in
	      let id = find_splitting_var pats var pats' in
	      let splits = List.map_filter (fun x -> x) (Array.to_list splits) in
		to82 (abstract (of82 (tclTHEN_i (to82 (depelim id))
				  (fun i -> let split = nth splits (pred i) in
					      tclTHENLIST [aux split])))) gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding goal") gl)
	    
    | Valid ((ctx, _, _), ty, substc, tac, valid, rest) ->
	tclTHEN_i tac (fun i -> let _, _, subst, split = nth rest (pred i) in
				  tclTHEN (Lazy.force unfold_add_pattern) (aux split))

    | RecValid (id, cs) -> 
	tclTHEN (to82 (unfold_recursor_tac ())) (aux cs)
	  
    | Refined ((ctx, _, _), refinfo, s) ->
	let id = pi1 refinfo.refined_obj in
	let ev = refinfo.refined_ex in
	let rec reftac gl = 
	  match kind_of_term (pf_concl gl) with
	  | App (f, [| ty; term1; term2 |]) ->
	      let f1, arg1 = destApp term1 and f2, arg2 = destApp term2 in
	      let _, a1 = find_helper_arg info f1 arg1 
	      and ev2, a2 = find_helper_arg info f2 arg2 in
	      let id = pf_get_new_id id gl in
		if Evar.equal ev2 ev then 
	  	  tclTHENLIST
	  	    [to82 (Equality.replace_by a1 a2
	  		     (of82 (tclTHENLIST [solve_eq])));
	  	     to82 (letin_tac None (Name id) a2 None Locusops.allHypsAndConcl);
	  	     Proofview.V82.of_tactic (clear_body [id]); aux s] gl
		else tclTHENLIST [unfolds; simpltac; reftac] gl
	  | _ -> tclFAIL 0 (str"Unexpected unfolding lemma goal") gl
	in
	  to82 (abstract (of82 (tclTHENLIST [to82 intros; simpltac; reftac])))
	    
    | Compute (_, _, RProgram c) ->
      to82 (abstract (of82 (tclTHENLIST [to82 intros; tclTRY unfolds; simpltac; solve_eq])))
	  
    | Compute ((ctx,_,_), _, REmpty id) ->
	let (na,_,_) = nth ctx (pred id) in
	let id = out_name na in
	  to82 (abstract (depelim id))
  in
    try
      let unfolds = unfold_in_concl
	[Locus.OnlyOccurrences [1], EvalConstRef f_cst; 
	 (Locus.OnlyOccurrences [1], EvalConstRef funf_cst)]
      in
      let res =
	tclTHENLIST 
	  [to82 (set_eos_tac ()); to82 intros; unfolds; simpl_in_concl; 
	   to82 (unfold_recursor_tac ());
	   (fun gl -> 
	     Global.set_strategy (ConstKey f_cst) Conv_oracle.Opaque;
	     Global.set_strategy (ConstKey funf_cst) Conv_oracle.Opaque;
	     aux split gl)] gl
      in Global.set_strategy (ConstKey f_cst) Conv_oracle.Expand;
	Global.set_strategy (ConstKey funf_cst) Conv_oracle.Expand;
	res
    with e ->
      Global.set_strategy (ConstKey f_cst) Conv_oracle.Expand;
      Global.set_strategy (ConstKey funf_cst) Conv_oracle.Expand;
      raise e
      
let update_split is_rec cmap f prob id split =
  let split' = map_evars_in_split cmap split in
    match is_rec with
    | Some (Structural _) -> subst_rec_split false f prob [(id, f)] split'
    | Some (Logical r) -> 
      let split' = subst_comp_proj_split f (mkConst r.comp_proj) split' in
      let rec aux = function
	| RecValid (_, Valid (ctx, ty, args, tac, view, 
			       [ctx', _, newprob, rest])) ->	  
	    aux (subst_rec_split true f newprob [(id, f)] rest)
	| Split (lhs, y, z, cs) -> Split (lhs, y, z, Array.map (Option.map aux) cs)
	| RecValid (id, c) -> RecValid (id, aux c)
	| Valid (lhs, y, z, w, u, cs) ->
	  Valid (lhs, y, z, w, u, 
		 List.map (fun (gl, cl, subst, s) -> (gl, cl, subst, aux s)) cs)
	| Refined (lhs, info, s) -> Refined (lhs, info, aux s)
	| (Compute _) as x -> x
      in aux split'
    | _ -> split'

	
let make_ref dir s = Coqlib.gen_reference "Program" dir s

let fix_proto_ref () = 
  match make_ref ["Program";"Tactics"] "fix_proto" with
  | ConstRef c -> c
  | _ -> assert false

let constr_of_global = Universes.constr_of_global

let define_by_eqs opts i (l,ann) t nt eqs =
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
      try_bool_opt (OComp false), irec,
      try_bool_opt (OEquations false), try_bool_opt (OInd false)
  in
  let env = Global.env () in
  let poly = Flags.is_universe_polymorphism () in
  let isevar = ref (create_evar_defs Evd.empty) in
  let ienv, ((env', sign), impls) = interp_context_evars env isevar l in
  let arity = interp_type_evars env' isevar t in
  let sign = nf_rel_context_evar ( !isevar) sign in
  let arity = nf_evar ( !isevar) arity in
  let arity, comp = 
    let body = it_mkLambda_or_LetIn arity sign in
    let _ = check_evars env Evd.empty !isevar body in
      if with_comp then
	let compid = add_suffix i "_comp" in
	let ce = make_definition isevar body in
	let comp =
	  Declare.declare_constant compid (DefinitionEntry ce, IsDefinition Definition)
	in (*Typeclasses.add_constant_class c;*)
	let compapp = mkApp (mkConst comp, rel_vect 0 (length sign)) in
	let projid = add_suffix i "_comp_proj" in
	let compproj = 
	  let body = it_mkLambda_or_LetIn (mkRel 1)
	    ((Name (id_of_string "comp"), None, compapp) :: sign)
	  in
	  let ce = Declare.definition_entry body in
	    Declare.declare_constant projid (DefinitionEntry ce, IsDefinition Definition)
	in
	  Impargs.declare_manual_implicits true (ConstRef comp) [impls];
	  Impargs.declare_manual_implicits true (ConstRef compproj) 
	    [(impls @ [ExplByPos (succ (List.length sign), None), (true, false, true)])];
	  Table.extraction_inline true [Ident (dummy_loc, compid); Ident (dummy_loc, projid)];
	  hintdb_set_transparency comp false "Below";
	  hintdb_set_transparency comp false "program";
	  hintdb_set_transparency comp false "subterm_relation";
	  compapp, Some { comp = comp; comp_app = compapp; 
			  comp_proj = compproj; comp_recarg = succ (length sign) }
      else arity, None
  in
  let env = Global.env () in (* To find the comp constant *)
  let ty = it_mkProd_or_LetIn arity sign in
  let data = Constrintern.compute_internalization_env
    env Constrintern.Recursive [i] [ty] [impls] 
  in
  let sort = Retyping.get_type_of env !isevar ty in
  let sort = Evarutil.evd_comb1 (Evarsolve.refresh_universes (Some false) env) isevar sort in
  let fixprot = mkApp (Universes.constr_of_global (Lazy.force coq_fix_proto), [|sort; ty|]) in
  let _fixprot_ty = Evarutil.evd_comb1 (Typing.e_type_of env) isevar fixprot in
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
	if for_all Option.is_empty occurs then None
	else if exists (function Some true -> true | _ -> false) occurs then Some true
	else Some false
    in 
      match occur_eqns eqs with
      | None -> None 
      | Some true -> Option.map (fun c -> Logical c) comp
      | Some false -> Some (Structural with_rec)
  in
  let equations = 
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation data) nt;
      map (interp_eqn i is_recursive isevar env data sign arity None) eqs)
      ()
  in
  let sign = nf_rel_context_evar ( !isevar) sign in
  let arity = nf_evar ( !isevar) arity in
  let fixdecls = nf_rel_context_evar ( !isevar) fixdecls in
    (*   let ce = check_evars fixenv Evd.empty !isevar in *)
    (*   List.iter (function (_, _, Program rhs) -> ce rhs | _ -> ()) equations; *)
  let prob = 
    if is_structural is_recursive then
      id_subst (sign @ fixdecls)
    else id_subst sign
  in
  let split = covering env isevar (i,with_comp,data) equations prob arity in
    (* if valid_tree prob split then *)
  let status = (* if is_recursive then Expand else *) Define false in
  let baseid = string_of_id i in
  let (ids, csts) = full_transparent_state in
  let fix_proto_ref = destConstRef (Lazy.force coq_fix_proto) in
  Hints.create_hint_db false baseid (ids, Cpred.remove fix_proto_ref csts) true;
  let hook cmap helpers subst gr = 
    let info = { base_id = baseid; helpers_info = helpers; polymorphic = poly } in
    let () = inline_helpers info in
    let f_cst = match gr with ConstRef c -> c | _ -> assert false in
    let env = Global.env () in
    let f = constr_of_global gr in
      if with_eqns || with_ind then
	match is_recursive with
	| Some (Structural _) ->
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
	| Some (Logical r) ->
	    let unfold_split = update_split is_recursive cmap f prob i split in
	    (* We first define the unfolding and show the fixpoint equation. *)
	    isevar := Evd.empty;
	    let unfoldi = add_suffix i "_unfold" in
	    let hook_unfold cmap helpers' vis gr' = 
	      let info = { base_id = baseid; helpers_info = helpers @ helpers'; 
			   polymorphic = poly } in
	      let () = inline_helpers info in
	      let funf_cst = match gr' with ConstRef c -> c | _ -> assert false in
	      let funfc =  mkConst funf_cst in
	      let unfold_split = map_evars_in_split cmap unfold_split in
	      let hook_eqs subst grunfold =
		Global.set_strategy (ConstKey funf_cst) Conv_oracle.transparent;
		build_equations with_ind env i info data sign None arity
		  funf_cst funfc ~alias:(f, constr_of_global grunfold, split) prob unfold_split
	      in
	      let evd = ref Evd.empty in
	      let stmt = it_mkProd_or_LetIn 
		(mkEq evd arity (mkApp (f, extended_rel_vect 0 sign))
		    (mkApp (mkConst funf_cst, extended_rel_vect 0 sign))) sign 
	      in
	      let tac = prove_unfolding_lemma info (mkConst r.comp_proj) f_cst funf_cst unfold_split in
	      let unfold_eq_id = add_suffix unfoldi "_eq" in
		ignore(Obligations.add_definition ~hook:(Lemmas.mk_hook hook_eqs)
			 ~reduce:(fun x -> x)
			 ~implicits:impls unfold_eq_id stmt ~tactic:(of82 tac)
			  (Evd.evar_universe_context !evd) [||])
	    in
	      define_tree None impls status isevar env (unfoldi, sign, arity) None ann unfold_split hook_unfold
      else ()
  in define_tree is_recursive impls status isevar env (i, sign, arity) comp ann split hook

let with_rollback f x =
  (* States.with_heavy_rollback f *)
  (*   Cerrors.process_vernac_interp_error x *)
  f x
(*   let st = States.freeze () in *)
(*     try f x with e -> msg (Toplevel.print_toplevel_error e); States.unfreeze st *)

let equations opts (loc, i) l t nt eqs =
  Dumpglob.dump_definition (loc, i) false "def";
  with_rollback (define_by_eqs opts i l t nt) eqs

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
      if n == 0 then [], c
      else match kind_of_term c with
      | LetIn (Name id, br, brt, b) ->
	  let rest, b = aux (pred n) b in
	    (id, br, brt) :: rest, b
      | _ -> error "Unnexpected goal"
    in aux brs b
  in
  let ids = targetn :: branchesn :: map pi1 branches in
  let cleantac = tclTHEN (to82 (intros_using ids)) (thin ids) in
  let dotac = tclDO (succ targ) intro in
  let letintac (id, br, brt) = 
    tclTHEN (to82 (letin_tac None (Name id) br (Some brt) nowhere)) tac 
  in
  let subtacs =
    tclTHENS destruct_tac (map letintac branches)
  in tclTHENLIST [cleantac ; dotac ; subtacs] gl

let dependencies env c ctx =
  let init = global_vars_set env c in
  let deps =
    Context.fold_named_context_reverse 
      (fun variables (n, _, _ as decl) ->
	let dvars = global_vars_set_of_decl env decl in
	  if Idset.mem n variables then Idset.union dvars variables
	  else variables)
      ~init:init ctx
  in
    (init, Idset.diff deps init)
