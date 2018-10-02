Require Import HoTT.Basics.Overture.
Require Import Coq.Init.Wf.

(** A class for well foundedness proofs.
   Instances can be derived automatically using [Derive Subterm for ind]. *)

Class WellFounded {A : Type} (R : relation A) :=
  wellfounded : well_founded R.

Inductive transitive_closure {A} (R : relation A) (x : A) : A -> Type :=
| t_step (y : A) : R x y -> transitive_closure R x y
| t_trans (y z : A) :
    transitive_closure R x y -> transitive_closure R y z ->
    transitive_closure R x z.

Lemma wf_transitive_closure {A} (R : relation A) : well_founded R -> well_founded (transitive_closure R).
Proof.
  intros.
  intro a. induction (X a).
  constructor. intros.
  induction X1. apply X0. auto.
  apply IHX1_2. auto. auto. auto.
Defined.