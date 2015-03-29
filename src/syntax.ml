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

type 'a located = 'a Loc.located

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


