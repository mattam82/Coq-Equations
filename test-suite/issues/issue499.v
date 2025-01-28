From Equations.Prop Require Import Equations.

Equations bla (n : nat) : nat -> nat by wf n lt :=
  bla 0 := fun m => 0;
  bla (S n) := fun m => S (bla n m).
