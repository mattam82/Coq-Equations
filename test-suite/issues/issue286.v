From Equations.Prop Require Import Equations.

Axiom P : nat -> Type.

Inductive foo : nat -> Type :=
| foo_let n (j := n) (k : P n) : nat -> let m := n + j + 2 in P m -> foo m.

Equations bar (n : nat) (x : foo n) : nat :=
  bar _ (foo_let x k n y) := n.
