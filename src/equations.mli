(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open Names
open Equations_common
open Splitting

val define_by_eqs
  :  poly:bool
  -> program_mode:bool
  -> open_proof:bool
  -> Syntax.equation_options
  -> Syntax.pre_equations
  -> (Names.lstring * Constrexpr.constr_expr *
      Notation_term.scope_name option) list
  -> Lemmas.t option

val define_principles :
  flags ->
  Syntax.rec_type ->
  EConstr.t list ->
  (program * compiled_program_info) list -> unit

val equations : poly:bool -> program_mode:bool ->
  Syntax.equation_options ->
  Syntax.pre_equations ->
  (Names.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  unit

val equations_interactive : poly:bool -> program_mode:bool ->
  Syntax.equation_options ->
  Syntax.pre_equations ->
  (Names.lstring * Constrexpr.constr_expr *
   Notation_term.scope_name option)
  list ->
  Lemmas.t

val solve_equations_goal :
  Proofview.V82.tac ->
  Proofview.V82.tac ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val dependencies :
  env -> Evd.evar_map ->
  Constr.t -> named_context -> Id.Set.t * Id.Set.t
