From Equations Require Import Init.
Require Export HoTT.Basics.Overture.
Set Warnings "-notation-overridden".

(** The polymorphic equality type used by Equations when working with equality in Type. *)
Set Universe Polymorphism.

Definition BiImpl (A B : Type) : Type := (A -> B) * (B -> A).

Notation "A <-> B" := (BiImpl A B) (at level 95) : type_scope.
