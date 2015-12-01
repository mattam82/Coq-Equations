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

val mk_term_eq :
  env ->
  Evd.evar_map ref ->
  constr ->
  constr -> constr -> constr -> constr * constr
val make_abstract_generalize :
  Proof_type.goal Tacmach.sigma ->
  Evd.evar_map ref ->
  Id.t ->
  constr ->
  bool ->
  rel_context ->
  constr option ->
  constr ->
  constr list -> constr list -> constr list -> constr
val hyps_of_vars :
  env ->
  named_context ->
  Idset.t -> Idset.t -> Idset.elt list
exception Seen
val linear : Idset.t -> constr array -> bool
val needs_generalization :
  Proof_type.goal Tacmach.sigma -> Id.t -> bool
val abstract_args :
  Proof_type.goal Tacmach.sigma ->
  bool ->
  bool ->
  Idset.elt ->
  bool ->
  constr ->
  constr array ->
  (constr * bool * int * Idset.elt list) option
val intro : Proofview.V82.tac
val abstract_generalize :
  ?generalize_vars:bool ->
  ?force_dep:bool ->
  Idset.elt ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma
val dependent_pattern :
  ?pattern_term:bool ->
  constr -> Proof_type.goal Tacmach.sigma -> Evar.t list Evd.sigma


val depcase :
  MutInd.t * int ->
  Evd.evar_map * rel_context * constr * Globnames.global_reference
val derive_dep_elimination :
  Evd.evar_universe_context -> inductive * 'a -> 'b -> constr


val pattern_call :
  ?pattern_term:bool ->
  constr -> Proof_type.goal Tacmach.sigma -> Evar.t list Evd.sigma
