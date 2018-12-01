Require Import Program.Basics Program.Tactics.
Require Import Equations.Equations.

Equations foo (n : nat) : nat :=
foo n := n + k 0

  where k (x : nat) : nat :=
  { k x := x }.
