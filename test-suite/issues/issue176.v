From Equations.Prop Require Import Equations.

Equations foo (n : nat) : nat :=
  foo x := let x := 0 in x.

Goal forall x, foo x = let x := 0 in x.
Proof.
  intros x. rewrite foo_equation_1.
  match goal with
    |- ?x = ?y => constr_eq x y
  end.
Abort.