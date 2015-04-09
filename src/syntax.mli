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
open Equations_common

(** User-level patterns *)
type user_pat =
    PUVar of identifier
  | PUCstr of constructor * int * user_pat list
  | PUInac of Constrexpr.constr_expr
type user_pats = user_pat list


(** Globalized syntax *)

type program = signature * clause list

and signature = identifier * rel_context * constr (* f : Π Δ. τ *)

and clause = lhs * clause rhs (* lhs rhs *)
and lhs = user_pats (* p1 ... pn *)
and 'a rhs =
    Program of Constrexpr.constr_expr
  | Empty of identifier Loc.located
  | Rec of identifier Loc.located * Constrexpr.constr_expr option *
      'a list
  | Refine of Constrexpr.constr_expr * 'a list
  | By of (Tacexpr.raw_tactic_expr, Tacexpr.glob_tactic_expr) Util.union *
      'a list


val pr_user_pat : env -> user_pat -> Pp.std_ppcmds
val pr_user_pats : env -> user_pat list -> Pp.std_ppcmds

val pr_lhs : env -> user_pat list -> Pp.std_ppcmds
val pplhs : user_pat list -> unit
val pr_rhs : env -> clause rhs -> Pp.std_ppcmds
val pr_clause :
  env -> clause -> Pp.std_ppcmds
val pr_clauses :
  env -> clause list -> Pp.std_ppcmds
val ppclause : clause -> unit


(** Raw syntax *)
type pat_expr =
    PEApp of Libnames.reference Misctypes.or_by_notation located *
      pat_expr located list
  | PEWildcard
  | PEInac of Constrexpr.constr_expr
  | PEPat of Constrexpr.cases_pattern_expr
type user_pat_expr = pat_expr located
type user_pat_exprs = user_pat_expr located
type input_pats =
    SignPats of user_pat_expr list
  | RefinePats of user_pat_expr list
type pre_equation =
    identifier located option * input_pats * pre_equation rhs


type rec_type = 
  | Structural of Id.t located option
  | Logical of rec_info
and rec_info = {
  comp : constant;
  comp_app : constr;
  comp_proj : constant;
  comp_recarg : int;
}
val is_structural : rec_type option -> bool

val next_ident_away : Id.t -> Id.t list ref -> Id.t

type equation_option = OInd of bool | ORec of Id.t located option | OComp of bool | OEquations of bool

type equation_user_option = equation_option

val pr_r_equation_user_option : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds

type equation_options = equation_option list

val pr_equation_options : 'a -> 'b -> 'c -> 'd -> Pp.std_ppcmds

val translate_cases_pattern :
  'a -> Id.t list ref -> Glob_term.cases_pattern -> user_pat

val ids_of_pats : pat_expr located list -> identifier list

val interp_eqn :
  identifier ->
  rec_type option ->
  'a ->
  env ->
  'b ->
  'c ->
  'd ->
  'e ->
  ((Loc.t * identifier) option * input_pats * 'f rhs as 'f) ->
  clause
