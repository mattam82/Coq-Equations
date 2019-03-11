From Equations Require Import Init.
Require Export HoTT.Basics.Overture.
Set Warnings "-notation-overridden".

(** The polymorphic equality type used by Equations when working with equality in Type. *)
Set Universe Polymorphism.

Definition BiImpl (A B : Type) : Type := (A -> B) * (B -> A).

Notation "A <-> B" := (BiImpl A B) (at level 95) : type_scope.

Definition transport_r {A} (P : A -> Type) {x y : A} (e : y = x) : P x -> P y :=
  fun x => match (inverse e) with 1%path => x end.

Lemma paths_elim_r {A} (x : A) (P : forall a, a = x -> Type) (p : P x 1%path)
      (y : A) (e : y = x) : P y e.
Proof. destruct e. apply p. Defined.
