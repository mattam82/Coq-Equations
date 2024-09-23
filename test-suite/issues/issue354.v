(* From Stdlib Require Import Logic.StrictProp. *)
From Equations Require Import Equations.

Inductive Ssig {A : Type} (P : A -> SProp) :=
  | Sexists (a : A) (b : P a) : Ssig P.

Set Warnings "+bad-relevance".

Equations Spr1 {A : Type} {P : A -> SProp} (s : Ssig P) : A :=
  Spr1 (Sexists _ a b) := a.

Equations Spr2 {A : Type} {P : A -> SProp} (s : Ssig P) : P (Spr1 s) :=
  Spr2 (Sexists _ a b) := b.
