From Equations Require Import CoreTactics.
From Equations Require Import Equations.

Inductive Squash (A : Type) : SProp :=
  | sq : A -> Squash A.

Class Positive (n : nat) : SProp :=
  is_positive : Squash (0 < n).

Record positive := mkpos {
  pos : nat ;
  cond_pos : Positive pos
}.

Derive NoConfusion NoConfusionHom for positive.
