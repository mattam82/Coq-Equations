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
