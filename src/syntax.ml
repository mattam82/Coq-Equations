(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term
open Context
open Environ
open Names
open Printer
open Ppconstr


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

open Constrintern
open Decl_kinds

(** User-level patterns *)
type user_pat =
    PUVar of identifier
  | PUCstr of constructor * int * user_pat list
  | PUInac of Constrexpr.constr_expr
type user_pats = user_pat list

(** AST *)
type program = 
  signature * clause list

and signature = identifier * rel_context * constr
  
and clause = lhs * clause rhs
  
and lhs = user_pats

and 'a rhs = 
  | Program of constr_expr
  | Empty of identifier Loc.located
  | Rec of identifier Loc.located * constr_expr option * 'a list
  | Refine of constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) union * 'a list


let rec pr_user_pat env = function
  | PUVar i -> pr_id i
  | PUCstr (c, i, f) -> 
      let pc = pr_constructor env c in
	if not (List.is_empty f) then str "(" ++ pc ++ spc () ++ pr_user_pats env f ++ str ")"
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
  | By (Inl tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_raw_tactic tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")
  | By (Inr tac, s) -> spc () ++ str "by" ++ spc () ++ Pptactic.pr_glob_tactic env tac
      ++ spc () ++ hov 1 (str "{" ++ pr_clauses env s ++ str "}")
      
and pr_clause env (lhs, rhs) =
  pr_lhs env lhs ++ pr_rhs env rhs

and pr_clauses env =
  prlist_with_sep fnl (pr_clause env)

let ppclause clause = pp(pr_clause (Global.env ()) clause)

type pat_expr = 
  | PEApp of reference Misctypes.or_by_notation located * pat_expr located list
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

type equation_option = | OInd of bool | ORec of Id.t located option 
		       | OComp of bool | OEquations of bool
    
type equation_user_option = equation_option

type equation_options = equation_option list

let pr_r_equation_user_option _prc _prlc _prt l =
  mt ()

let pr_equation_options  _prc _prlc _prt l =
  mt ()

type rec_type = 
  | Structural of Id.t located option
  | Logical of rec_info

and rec_info = {
  comp : constant;
  comp_app : constr;
  comp_proj : constant;
  comp_recarg : int;
}

let is_structural = function Some (Structural _) -> true | _ -> false


let rec translate_cases_pattern env avoid = function
  | PatVar (loc, Name id) -> PUVar id
  | PatVar (loc, Anonymous) -> 
      let n = next_ident_away (id_of_string "wildcard") avoid in
	avoid := n :: !avoid; PUVar n
  | PatCstr (loc, (ind, _ as cstr), pats, Anonymous) ->
      PUCstr (cstr, (Inductiveops.inductive_nparams ind), map (translate_cases_pattern env avoid) pats)
  | PatCstr (loc, cstr, pats, Name id) ->
      user_err_loc (loc, "interp_pats", str "Aliases not supported by Equations")

let rec ids_of_pats pats =
  fold_left (fun ids (_,p) ->
    match p with
    | PEApp ((loc,f), l) -> 
	let lids = ids_of_pats l in
	  (try ident_of_smart_global f :: lids with _ -> lids) @ ids
    | PEWildcard -> ids
    | PEInac _ -> ids
    | PEPat _ -> ids)
    [] pats

let interp_eqn i is_rec isevar env impls sign arity recu eqn =
  let avoid = ref [] in
  let rec interp_pat (loc, p) =
    match p with
    | PEApp ((loc,f), l) -> 
	let r =
	  try Inl (Smartlocate.smart_global f)
	  with e -> Inr (PUVar (ident_of_smart_global f))
	in
	  (match r with
	   | Inl (ConstructRef c) ->
	       let (ind,_) = c in
	       let nparams = Inductiveops.inductive_nparams ind in
	       let nargs = constructor_nrealargs c in
	       let len = List.length l in
	       let l' =
		 if len < nargs then 
		   List.make (nargs - len) (loc,PEWildcard) @ l
		 else l
	       in 
		 Dumpglob.add_glob loc (ConstructRef c);
		 PUCstr (c, nparams, map interp_pat l')
	   | Inl _ ->
	       if l != [] then 
		 user_err_loc (loc, "interp_pats",
			       str "Pattern variable " ++ pr_smart_global f ++ str" cannot be applied ")
	       else PUVar (ident_of_smart_global f)
	   | Inr p -> p)
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
      if not (Id.equal id i) then
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
      | Some (Structural _) -> (PUVar i :: pats, interp_rhs curpats' None rhs)
      | Some (Logical r) -> (pats, interp_rhs curpats' (Some (ConstRef r.comp_proj)) rhs)
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
    | CApp (loc, (None, CRef (Ident (loc',id'), _)), args), Some cproj when Id.equal i id' ->
	let qidproj = Nametab.shortest_qualid_of_global Idset.empty cproj in
	  CApp (loc, (None, CRef (Qualid (loc', qidproj), None)),
		List.map (fun (c, expl) -> interp_constr_expr compproj ids c, expl) args)
    | _ -> map_constr_expr_with_binders (fun id l -> id :: l) 
	(interp_constr_expr compproj) ids c
  in aux [] eqn
