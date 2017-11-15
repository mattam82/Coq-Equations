(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open Equations_common

val mkAppG :
  Evd.evar_map ref ->
  Globnames.global_reference -> Term.constr array -> Term.constr
val applistG :
  Evd.evar_map ref ->
  Globnames.global_reference -> Term.constr list -> Term.constr
val mkSig :
  Evd.evar_map ref -> Names.Name.t * Term.types * Term.constr -> Term.constr
val constrs_of_coq_sigma : 
  Environ.env ->
  Evd.evar_map ref ->
  Term.constr ->
  Term.constr -> (Names.name * Term.constr * Term.constr * Term.constr) list
val decompose_coq_sigma : Term.constr -> (Univ.Instance.t * Term.constr * Term.constr) option
val decompose_indapp :
  Term.constr -> Term.constr array -> Term.constr * Term.constr array
val telescope :
  Evd.evar_map ref ->
  rel_context ->
  Term.constr * rel_context * Term.constr
val sigmaize :
  ?liftty:int ->
  Environ.env ->
  Evd.evar_map ref ->
  rel_context ->
  Term.constr ->
  Term.constr * Term.constr * rel_context * Constr.constr list * Names.projection *
  Names.projection * Term.constr * Term.constr
val ind_name : Names.inductive -> Names.Id.t
val declare_sig_of_ind : Environ.env -> Evd.evar_map -> bool -> Term.pinductive -> Term.constr
val get_signature :
  Environ.env -> Evd.evar_map -> Term.constr -> Evd.evar_map * Term.constr * Term.constr
val pattern_sigma : assoc_right:bool ->
  Term.constr ->
  Names.Id.t -> Environ.env -> Evd.evar_map -> unit Proofview.tactic

(* Unused for now *)
val curry_left_hyp : Environ.env -> Evd.evar_map ->
  Term.constr -> Term.types -> (Term.constr * Term.types) option

val build_sig_of_ind : Environ.env ->
                       Evd.evar_map ->
                       Term.pinductive ->
                       Evd.evar_map * Term.constr * rel_context * Term.constr *
                         Term.constr * rel_context * int * Term.constr

(** Pack all hypotheses into a new one using sigmas *)
val uncurry_hyps : Names.Id.t -> unit Proofview.tactic

(** Curry a term starting with a quantification on a sigma type,
    associated to the right. *)
val curry : Names.Name.t -> Term.constr ->
            rel_context * Term.constr

val uncurry_call : Environ.env -> Evd.evar_map -> Term.constr ->
                   Evd.evar_map * Term.constr * Term.types

val smart_case : Environ.env -> Evd.evar_map ref -> rel_context ->
  int -> Term.types ->
  rel_context * Term.types *
  (Term.types * int * Covering.context_map) array *
  int * Covering.context_map * Term.constr list * bool

module Tactics : sig
  val curry_hyp : Names.Id.t -> unit Proofview.tactic
  val curry : unit Proofview.tactic
  val uncurry_call : Constr.t -> Names.Id.t -> unit Proofview.tactic

  val pattern_sigma : Names.Id.t -> unit Proofview.tactic
  val get_signature_pack : Names.Id.t -> Names.Id.t -> unit Proofview.tactic
end
