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

val lift_togethern : int -> Constr.constr list -> Constr.constr list
val lift_together : Constr.constr list -> Constr.constr list
val lift_list : Constr.constr list -> Constr.constr list
val ids_of_constr :
  ?all:bool -> Names.Idset.t -> Term.constr -> Names.Idset.t
val decompose_indapp :
  Term.constr -> Term.constr array -> Term.constr * Term.constr array
val e_conv :
  Environ.env -> Evd.evar_map ref -> Term.constr -> Term.constr -> bool
val mk_term_eq :
  Environ.env ->
  Evd.evar_map ref ->
  Term.constr ->
  Term.constr -> Term.constr -> Term.constr -> Term.constr * Term.constr
val make_abstract_generalize :
  Proof_type.goal Tacmach.sigma ->
  Evd.evar_map ref ->
  Names.Id.t ->
  Constr.constr ->
  bool ->
  Context.rel_context ->
  Constr.t option ->
  Constr.constr ->
  Constr.constr list -> Term.constr list -> Term.constr list -> Term.constr
val deps_of_var : Names.Id.t -> Environ.env -> Names.Idset.t
val idset_of_list : Names.Idset.elt list -> Names.Idset.t
val hyps_of_vars :
  Environ.env ->
  Context.named_context ->
  Names.Idset.t -> Names.Idset.t -> Names.Idset.elt list
exception Seen
val linear : Names.Idset.t -> Term.constr array -> bool
val needs_generalization :
  Proof_type.goal Tacmach.sigma -> Names.Id.t -> bool
val abstract_args :
  Proof_type.goal Tacmach.sigma ->
  bool ->
  bool ->
  Names.Idset.elt ->
  bool ->
  Term.constr ->
  Term.constr array ->
  (Term.constr * bool * int * Names.Idset.elt list) option
val intro : Proofview.V82.tac
val abstract_generalize :
  ?generalize_vars:bool ->
  ?force_dep:bool ->
  Names.Idset.elt ->
  Proof_type.goal Tacmach.sigma -> Proof_type.goal list Evd.sigma
val dependent_pattern :
  ?pattern_term:bool ->
  Term.constr -> Proof_type.goal Tacmach.sigma -> Evar.t list Evd.sigma


val depcase :
  MutInd.t * int ->
  rel_context * constr * Globnames.global_reference
val derive_dep_elimination :
  Evd.evar_universe_context -> inductive * 'a -> 'b -> constr


val pattern_call :
  ?pattern_term:bool ->
  constr -> Proof_type.goal Tacmach.sigma -> Evar.t list Evd.sigma
