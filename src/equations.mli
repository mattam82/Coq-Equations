(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open Names
open Equations_common
open Syntax
open Splitting

val define_by_eqs : poly:bool ->
  Syntax.equation_option list ->
  Syntax.pre_equations ->
  (Names.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  unit

val define_principles :
  flags ->
  Syntax.rec_type option ->
  EConstr.t list ->
  (program_info * compiled_program_info) list -> unit

val equations : poly:bool ->
  Syntax.equation_option list ->
  Syntax.pre_equations ->
  (Names.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  unit

val solve_equations_goal :
  Proofview.V82.tac ->
  Proofview.V82.tac ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val dependencies :
  env -> Evd.evar_map ->
  Constr.t -> named_context -> Id.Set.t * Id.Set.t
