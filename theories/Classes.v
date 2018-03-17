Require Import HoTT.Basics.Overture.

(* TODO. Definitions of Acc* and well_founded should be in stdlib. *)

Inductive Acc {A : Type} (R : A -> A -> Type) (x : A) : Type :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.
Arguments Acc_intro {A} {R} _ _.
Definition well_founded {A : Type} (R : A -> A -> Type) := forall a : A, Acc R a.

(** A class for well foundedness proofs.
   Instances can be derived automatically using [Derive Subterm for ind]. *)

Class WellFounded {A : Type} (R : relation A) :=
  wellfounded : well_founded R.
