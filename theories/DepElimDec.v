(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations Require Import Init Signature DepElim EqDec HSetInstances.

(** Alternative implementation of generalization using sigma types only,
   allowing to use K on decidable domains. *)

(* Use the new simplification. *)
(* FIXME Temporary location? *)
Ltac simplify_one_dep_elim' :=
match goal with
(* Do not put any part of the rhs in the hypotheses. *)
| |- let _ := block in _ => fail 1
| |- _ => simplify ?
(* Trying with more primitive tactics. *)
| |- ?f ?x = ?g ?y -> _ => let H := fresh in progress (intros H ; injection H ; clear H)
| |- Id (?f ?x) (?g ?y) -> _ => let H := fresh in progress (intros H ; inversion H ; clear H)
| |- ?t = ?u -> _ => let hyp := fresh in
  intros hyp ; elimtype False ; discriminate
| |- Id ?t ?u -> _ => let hyp := fresh in
  intros hyp ; elimtype False ; solve [inversion hyp]
| |- ?x = ?y -> _ => let hyp := fresh in
  intros hyp ; (try (clear hyp ; (* If non dependent, don't clear it! *) fail 1)) ;
    case hyp
| |- Id _ ?x ?y -> _ => let hyp := fresh in
  intros hyp ; (try (clear hyp ; (* If non dependent, don't clear it! *) fail 1)) ;
    case hyp
| |- _ -> ?B => let ty := type of B in (* Works only with non-dependent products *)
  intro || (let H := fresh in intro H)
| |- forall x, _ =>
  let H := fresh x in intro H
| |- _ => intro
end.

(* Ltac simplify_dep_elim ::= repeat simplify_one_dep_elim'. *)
