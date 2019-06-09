(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Constr
open Environ
open Names
open EConstr

val hyps_of_vars :
  env -> Evd.evar_map ->
  named_context ->
  Id.Set.t -> Id.Set.t -> Id.Set.elt list

exception Seen

val linear : Evd.evar_map -> Id.Set.t -> constr array -> bool

val needs_generalization :
  Goal.goal Evd.sigma -> Id.t -> bool

val dependent_pattern :
  ?pattern_term:bool ->
  constr -> Goal.goal Evd.sigma -> Evar.t list Evd.sigma


val depcase
  :  poly:bool
  -> MutInd.t * int
  -> Environ.env * Evd.evar_map * rel_context * constr * Names.GlobRef.t

val derive_dep_elimination
  :  Environ.env
  -> Evd.evar_map
  -> poly:bool
  -> pinductive
  -> Constant.t * (Evd.evar_map * constr)

val pattern_call :
  ?pattern_term:bool ->
  constr -> Goal.goal Evd.sigma -> Evar.t list Evd.sigma

val specialize_eqs : with_block:bool -> Names.Id.t -> Proofview.V82.tac

val compare_upto_variables : Evd.evar_map -> constr -> constr -> bool

val dependent_elim_tac : ?patterns:Syntax.user_pat_loc list -> Names.Id.t Syntax.with_loc ->
  unit Proofview.tactic

val dependent_elim_tac_expr : ?patterns:Constrexpr.constr_expr list -> Names.Id.t Syntax.with_loc ->
  unit Proofview.tactic
