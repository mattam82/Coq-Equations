(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open EConstr

val mkAppG :
  Evd.evar_map ref ->
  Names.GlobRef.t -> constr array -> constr
val applistG :
  Evd.evar_map ref ->
  Names.GlobRef.t -> constr list -> constr
val mkSig :
  Evd.evar_map ref -> Names.Name.t * types * constr -> constr
val constrs_of_coq_sigma : 
  Environ.env ->
  Evd.evar_map ref ->
  constr ->
  constr -> (Names.Name.t * constr * constr * constr) list
val decompose_coq_sigma : Evd.evar_map -> constr -> (EInstance.t * constr * constr) option
val decompose_indapp : Evd.evar_map ->
  constr -> constr array -> constr * constr array
val telescope :
  Evd.evar_map ref ->
  Sorts.family ->
  rel_context ->
  constr * rel_context * constr
val sigmaize :
  ?liftty:int ->
  Environ.env ->
  Evd.evar_map ref ->
  rel_context ->
  constr ->
  Sorts.family ->
  constr * constr * rel_context * constr list * Names.Projection.t *
  Names.Projection.t * constr * constr
val ind_name : Names.inductive -> Names.Id.t
val declare_sig_of_ind : Environ.env -> Evd.evar_map -> bool -> Names.inductive * EConstr.EInstance.t -> constr
val get_signature :
  Environ.env -> Evd.evar_map -> constr -> Evd.evar_map * constr * constr
val pattern_sigma : assoc_right:bool ->
  constr ->
  Names.Id.t -> Environ.env -> Evd.evar_map -> unit Proofview.tactic

(* Unused for now *)
val curry_left_hyp : Environ.env -> Evd.evar_map ->
  constr -> types -> (constr * types) option

val build_sig_of_ind : Environ.env ->
                       Evd.evar_map ->
                       Names.inductive Equations_common.peuniverses ->
                       Evd.evar_map * constr * rel_context * constr *
                         constr * rel_context * int * constr

(** Pack all hypotheses into a new one using sigmas *)
val uncurry_hyps : Names.Id.t -> unit Proofview.tactic

(** Curry a term starting with a quantification on a sigma type,
    associated to the right. *)
val curry : Evd.evar_map -> Names.Name.t -> constr ->
            rel_context * constr

val uncurry_call : Environ.env -> Evd.evar_map -> constr ->
                   Evd.evar_map * constr * types

val smart_case : Environ.env -> Evd.evar_map ref -> rel_context ->
  int -> types ->
  rel_context * types *
  (types * int * Covering.context_map) array *
  int * Covering.context_map * constr list * bool

module Tactics : sig
  val curry_hyp : Names.Id.t -> unit Proofview.tactic
  val curry : unit Proofview.tactic
  val uncurry_call : constr -> Names.Id.t -> unit Proofview.tactic

  val pattern_sigma : Names.Id.t -> unit Proofview.tactic
  val get_signature_pack : Names.Id.t -> Names.Id.t -> unit Proofview.tactic
end
