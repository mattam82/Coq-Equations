(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Corelib Require Import Relation_Definitions.
Set Warnings "-notation-overridden".
From Equations Require Import Init.
From Equations.Prop Require Import Logic.

(** The polymorphic equality type used by Equations when working with equality in Type. *)

Section FunExt.
  Context (A : Type) (B : A -> Type).

  Definition functional_extensionality :=
    forall (f g : forall x, B x), (forall x, f x = g x) -> f = g.

End FunExt.

Axiom funext : forall A B, functional_extensionality A B.

Ltac extensionality x := eapply funext; intros x.