(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Environ
open Names
open Equations_common
open Splitting

val define_by_eqs
  :  pm:Declare.OblState.t
  -> poly:bool
  -> program_mode:bool
  -> open_proof:bool
  -> Syntax.equation_options
  -> Syntax.pre_equations
  -> Vernacexpr.decl_notation list
  -> Declare.OblState.t * Declare.Proof.t option

val define_principles :
  pm:Declare.OblState.t ->
  flags ->
  Syntax.rec_type ->
  EConstr.t list ->
  (program * compiled_program_info) list -> Declare.OblState.t

val equations :
  pm:Declare.OblState.t ->
  poly:bool -> program_mode:bool ->
  Syntax.equation_options ->
  Syntax.pre_equations ->
  Vernacexpr.decl_notation list ->
  Declare.OblState.t

val equations_interactive :
  pm:Declare.OblState.t ->
  poly:bool -> program_mode:bool ->
  Syntax.equation_options ->
  Syntax.pre_equations ->
  Vernacexpr.decl_notation list ->
  Declare.OblState.t * Declare.Proof.t

val solve_equations_goal :
  Proofview.V82.tac ->
  Proofview.V82.tac ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma

val dependencies :
  env -> Evd.evar_map ->
  Constr.t -> named_context -> Id.Set.t * Id.Set.t
