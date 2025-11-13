From Equations Require Import Equations.

Equations foo (n : nat) : nat :=
  | 0 => 0 ;
  | S x => 1.
  (* | S x => foo x. *)