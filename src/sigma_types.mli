(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

open EConstr

val mkAppG :
  Environ.env -> Evd.evar_map ref ->
  Names.GlobRef.t -> constr array -> constr
val applistG :
  Environ.env -> Evd.evar_map ref ->
  Names.GlobRef.t -> constr list -> constr
val mkSig :
  Environ.env -> Evd.evar_map ref -> Names.Name.t binder_annot * types * constr -> constr
val constrs_of_coq_sigma : 
  Environ.env ->
  Evd.evar_map ref ->
  constr ->
  constr -> (Names.Name.t binder_annot * constr * constr * constr) list
val decompose_coq_sigma : Environ.env -> Evd.evar_map -> constr -> (EInstance.t * constr * constr) option
val decompose_indapp : Evd.evar_map ->
  constr -> constr array -> constr * constr array

val telescope_intro : Environ.env -> Evd.evar_map -> int -> constr (* interpreted telescope *)
  -> constr (* introduction *)

val telescope_of_context :
  Environ.env ->
  Evd.evar_map ->
  rel_context ->
  Evd.evar_map * constr (* telescope *) * constr (* interp tele *)

val telescope : Environ.env ->
  Evd.evar_map ref ->
  rel_context ->
  constr * rel_context * constr
val sigmaize :
  ?liftty:int ->
  Environ.env ->
  Evd.evar_map ref ->
  rel_context ->
  constr ->
  constr * constr * rel_context * constr list * Names.Projection.t *
  Names.Projection.t * constr * constr
val ind_name : Names.inductive -> Names.Id.t
val declare_sig_of_ind : Environ.env -> Evd.evar_map -> poly:bool -> Names.inductive * EConstr.EInstance.t ->
  Names.Constant.t * (Evd.evar_map * EConstr.t)
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
val curry : Environ.env -> Evd.evar_map -> Names.Name.t binder_annot -> constr ->
            rel_context * constr

val uncurry_call : Environ.env -> Evd.evar_map -> constr -> constr ->
                   Evd.evar_map * constr * constr * types

val smart_case : Environ.env -> Evd.evar_map ref -> rel_context ->
  int -> types ->
  rel_context * types *
  (types * int * Context_map.context_map) array *
  int * Context_map.context_map * constr list * bool

module Tactics : sig
  val curry_hyp : Names.Id.t -> unit Proofview.tactic
  val curry : unit Proofview.tactic
  val uncurry_call : constr -> constr -> Names.Id.t -> Names.Id.t -> unit Proofview.tactic

  val pattern_sigma : Names.Id.t -> unit Proofview.tactic
  val get_signature_pack : Names.Id.t -> Names.Id.t -> unit Proofview.tactic
end
