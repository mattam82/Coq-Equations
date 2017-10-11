(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Term
open Context
open Environ
open Names

open Equations_common
open Syntax
open Covering
open Splitting

val make_ref : string list -> string -> Globnames.global_reference
val fix_proto_ref : unit -> constant
val constr_of_global : Globnames.global_reference -> constr

val define_by_eqs :
  Syntax.equation_option list ->
  identifier ->
  Constrexpr.local_binder list ->
  Constrexpr.constr_expr ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  ((Loc.t * identifier) option * input_pats * 'b rhs as 'b) list ->
  unit

val with_rollback : ('a -> 'b) -> 'a -> 'b

val equations :
  Syntax.equation_option list ->
  Loc.t * identifier ->
  Constrexpr.local_binder list ->
  Constrexpr.constr_expr ->
  (Vernacexpr.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list -> pre_equation list -> unit


val solve_equations_goal :
  Proof_type.tactic ->
  Proof_type.tactic ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma

val dependencies :
  env ->
  constr -> named_context -> Id.Set.t * Idset.t


