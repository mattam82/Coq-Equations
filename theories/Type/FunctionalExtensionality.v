Set Warnings "-notation-overridden".
From Equations Require Import Init.
From Stdlib Require Import CRelationClasses.
From Equations.Type Require Import Logic.

(** The polymorphic equality type used by Equations when working with equality in Type. *)

Set Universe Polymorphism.
Import Id_Notations.
Section FunExt.
  Context (A : Type) (B : A -> Type).

  Definition functional_extensionality :=
    forall (f g : forall x, B x), (forall x, f x = g x) -> f = g.

End FunExt.

Axiom funext : forall A B, functional_extensionality A B.
