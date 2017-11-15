(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2017 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Additional general purpose tactics *)

val decompose_app : Names.Id.t -> Names.Id.t -> Constr.t -> unit Proofview.tactic

val autounfold_ref : Globnames.global_reference -> unit Proofview.tactic

(** [refine_ho c]

  Matches a lemma [c] of type [∀ ctx, ty] with a conclusion of the form
  [∀ ctx, ?P args] using second-order matching on the problem
  [ctx |- ?P args = ty] and then refines the goal with [c]. *)

val refine_ho : Constr.t -> unit Proofview.tactic
