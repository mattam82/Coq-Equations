(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Constr
open Environ
open Names
open EConstr

val mk_term_eq :
  env ->
  Evd.evar_map ref ->
  constr ->
  constr -> constr -> constr -> constr * constr
val make_abstract_generalize :
  Goal.goal Evd.sigma ->
  Evd.evar_map ref ->
  Id.t ->
  constr ->
  bool ->
  rel_context ->
  constr option ->
  constr ->
  constr list -> constr list -> constr list -> constr
val hyps_of_vars :
  env -> Evd.evar_map ->
  named_context ->
  Id.Set.t -> Id.Set.t -> Id.Set.elt list
exception Seen
val linear : Evd.evar_map -> Id.Set.t -> constr array -> bool
val needs_generalization :
  Goal.goal Evd.sigma -> Id.t -> bool
val abstract_args :
  Goal.goal Evd.sigma ->
  bool ->
  bool ->
  Id.Set.elt ->
  bool ->
  constr ->
  constr array ->
  (constr * bool * int * Id.Set.elt list) option
val abstract_generalize :
  ?generalize_vars:bool ->
  ?force_dep:bool ->
  Id.Set.elt ->
  Goal.goal Evd.sigma -> Goal.goal list Evd.sigma
val dependent_pattern :
  ?pattern_term:bool ->
  constr -> Goal.goal Evd.sigma -> Evar.t list Evd.sigma


val depcase : Decl_kinds.polymorphic ->
  MutInd.t * int ->
  Environ.env * Evd.evar_map * rel_context * constr * Names.GlobRef.t
val derive_dep_elimination :
  Environ.env -> Evd.evar_map -> polymorphic:Decl_kinds.polymorphic -> pinductive ->
  Constant.t * (Evd.evar_map * constr)


val pattern_call :
  ?pattern_term:bool ->
  constr -> Goal.goal Evd.sigma -> Evar.t list Evd.sigma

val specialize_eqs : with_block:bool -> Names.Id.t -> Proofview.V82.tac

val compare_upto_variables : Evd.evar_map -> constr -> constr -> bool

val dependent_elim_tac : ?patterns:Syntax.user_pat_expr list -> Names.Id.t Syntax.with_loc ->
  unit Proofview.tactic
