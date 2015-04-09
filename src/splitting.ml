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
open Covering

let helper_evar evm evar env typ src =
  let sign, typ', instance, _, _ = push_rel_context_to_named_context env typ in
  let evm' = evar_declare sign evar typ' ~src evm in
    evm', mkEvar (evar, Array.of_list instance)

let term_of_tree status isevar env (i, delta, ty) ann tree =
  let oblevars = ref Evar.Set.empty in
  let helpers = ref [] in
  let rec aux evm = function
    | Compute ((ctx, _, _), ty, RProgram rhs) -> 
	let body = it_mkLambda_or_LetIn rhs ctx and typ = it_mkProd_or_subst ty ctx in
	  evm, body, typ

    | Compute ((ctx, _, _), ty, REmpty split) ->
	let split = (Name (id_of_string "split"), 
		    Some (coq_nat_of_int (succ (length ctx - split))),
		    Lazy.force coq_nat)
	in
	let ty' = it_mkProd_or_LetIn ty ctx in
	let let_ty' = mkLambda_or_LetIn split (lift 1 ty') in
	let evm, term = new_evar env evm ~src:(dummy_loc, QuestionMark (Define true)) let_ty' in
	let ev = fst (destEvar term) in
	  oblevars := Evar.Set.add ev !oblevars;
	  evm, term, ty'
	   
    | RecValid (id, rest) -> aux evm rest

    | Refined ((ctx, _, _), info, rest) ->
	let (id, _, _), ty, rarg, path, ev, (f, args), newprob, newty =
	  info.refined_obj, info.refined_rettyp,
	  info.refined_arg, info.refined_path,
	  info.refined_ex, info.refined_app, info.refined_newprob, info.refined_newty
	in
	let evm, sterm, sty = aux evm rest in
	let evm, term, ty = 
	  let term = mkLetIn (Name (id_of_string "prog"), sterm, sty, lift 1 sty) in
	  let evm, term = helper_evar evm ev (Global.env ()) term
	    (dummy_loc, QuestionMark (Define false)) 
	  in
	    oblevars := Evar.Set.add ev !oblevars;
	    helpers := (ev, rarg) :: !helpers;
	    evm, term, ty
	in
	let term = applist (f, args) in
	let term = it_mkLambda_or_LetIn term ctx in
	let ty = it_mkProd_or_subst ty ctx in
	  evm, term, ty

    | Valid ((ctx, _, _), ty, substc, tac, (entry, pv), rest) ->
	let tac = Proofview.tclDISPATCH 
	  (map (fun (goal, args, subst, x) -> 
	    Proofview.Refine.refine (fun evm -> 
	      let evm, term, ty = aux evm x in
		evm, applistc term args)) rest)
	in
	let pv : Proofview_monad.proofview = Obj.magic pv in
	let pv = { pv with Proofview_monad.solution = evm } in
	let _, pv', _, _ = Proofview.apply env tac (Obj.magic pv) in
	let c = List.hd (Proofview.partial_proof entry pv') in
	  Proofview.return pv', 
	  it_mkLambda_or_LetIn (subst_vars substc c) ctx, it_mkProd_or_LetIn ty ctx
	      
    | Split ((ctx, _, _), rel, ty, sp) -> 
	let before, decl, after = split_tele (pred rel) ctx in
	let evd = ref evm in
	let branches = 
	  Array.map (fun split -> 
	    match split with
	    | Some s -> let evm', c, t = aux !evd s in evd := evm'; c,t
	    | None ->
		(* dead code, inversion will find a proof of False by splitting on the rel'th hyp *)
	      coq_nat_of_int rel, Lazy.force coq_nat)
	    sp 
	in
	let evm = !evd in
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
	let evm, case =
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
	  let evm, term = new_evar env evm ~src:(dummy_loc, QuestionMark status) ty in
	  let ev = fst (destEvar term) in
	    oblevars := Evar.Set.add ev !oblevars;
	    evm, term
	in       
	let casetyp = it_mkProd_or_subst ty ctx in
	  evm, mkCast(case, DEFAULTcast, casetyp), casetyp
  in 
  let evm, term, typ = aux !isevar tree in
    isevar := evm;
    !helpers, !oblevars, term, typ

let is_comp_obl comp hole_kind =
  match comp with
  | None -> false
  | Some r -> 
      match hole_kind with 
      | ImplicitArg (ConstRef c, (n, _), _) ->
	Constant.equal c r.comp_proj && n == r.comp_recarg 
      | _ -> false

let zeta_red =
  let red = Tacred.cbv_norm_flags
    (Closure.RedFlags.red_add Closure.RedFlags.no_red Closure.RedFlags.fZETA)
  in
    reduct_in_concl (red, DEFAULTcast)

let define_tree is_recursive impls status isevar env (i, sign, arity) comp ann split hook =
  let _ = isevar := Evarutil.nf_evar_map_undefined !isevar in
  let helpers, oblevs, t, ty = term_of_tree status isevar env (i, sign, arity) ann split in
  let obls, (emap, cmap), t', ty' = 
    Obligations.eterm_obligations env i !isevar
      0 ~status t (whd_betalet !isevar ty)
  in
  let obls = 
    Array.map (fun (id, ty, loc, s, d, t) ->
      let tac = 
	if Evar.Set.mem (rev_assoc Id.equal id emap) oblevs 
	then Some (equations_tac ()) 
	else if is_comp_obl comp (snd loc) then
	  let unfolds = unfold_in_concl 
	    [((Locus.AllOccurrencesBut [1]), EvalConstRef (Option.get comp).comp)]
	  in
	    Some (of82 (tclTRY 
			  (tclTHENLIST [zeta_red; to82 Tactics.intros; unfolds;
					(to82 (solve_rec_tac ()))])))
	else Some (snd (Obligations.get_default_tactic ()))
      in (id, ty, loc, s, d, tac)) obls
  in
  let term_info = map (fun (ev, arg) ->
    (ev, arg, List.assoc ev emap)) helpers
  in
  let hook x y = 
    let l = Array.map_to_list (fun (id, ty, loc, s, d, tac) -> Ident (dummy_loc, id)) obls in
      Table.extraction_inline true l;
      hook cmap term_info x y
  in
  let hook = Lemmas.mk_hook hook in
    match is_recursive with
    | Some (Structural id) ->
	ignore(Obligations.add_mutual_definitions [(i, t', ty', impls, obls)] 
		 (Evd.evar_universe_context !isevar) [] 
		 ~hook (Obligations.IsFixpoint [id, CStructRec]))
    | _ ->
      ignore(Obligations.add_definition ~hook
	       ~implicits:impls i ~term:t' ty' 
	       (Evd.evar_universe_context !isevar) obls)


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
  evar_map (fun id -> Universes.constr_of_global (Nametab.global (Qualid (dummy_loc, qualid_of_ident id)))) c
(*  list_try_find  *)
(* 	      (fun (id', c, filter) ->  *)
(* 		 if id = id' then (c, filter) else failwith "") subst) c *)

let map_split f split =
  let rec aux = function
    | Compute (lhs, ty, RProgram c) -> Compute (lhs, ty, RProgram (f c))
    | Split (lhs, y, z, cs) -> Split (lhs, y, z, Array.map (Option.map aux) cs)
    | RecValid (id, c) -> RecValid (id, aux c)
    | Valid (lhs, y, z, w, u, cs) ->
	Valid (lhs, y, z, w, u, List.map (fun (gl, cl, subst, s) -> (gl, cl, subst, aux s)) cs)
    | Refined (lhs, info, s) ->
	let (id, c, cty) = info.refined_obj in
	let (scf, scargs) = info.refined_app in
	  Refined (lhs, { info with refined_obj = (id, f c, f cty);
			    refined_app = (f scf, List.map f scargs);
			    refined_newprob_to_lhs = map_ctx_map f info.refined_newprob_to_lhs }, 
		   aux s)
    | Compute (_, _, REmpty _) as c -> c
  in aux split


let map_evars_in_split m = map_split (map_evars_in_constr m)
