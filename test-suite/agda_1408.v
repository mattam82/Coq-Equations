From Equations.Prop Require Import Equations.

Axiom  I     : Set.
Axiom i1 i2 : I.

Inductive D : I -> Set :=
| d1 : D i1
| d2 : D i2.
Derive Signature NoConfusion for D.

(** This would require general K or deciding i1 = i2. *)
Fail Derive NoConfusionHom for D.

Inductive P : forall {i}, D i -> Set :=
  p1 : P d1
| p2 : P d2.
Derive Signature for P.
Derive NoConfusionHom for P.

#[warning="-solve_obligation_error,-functional-induction-derivation-failure"]
Equations Foo (p : P d1) : Set :=
  Foo p1 := nat.
