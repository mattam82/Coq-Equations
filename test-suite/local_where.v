Require Import Program.Basics Program.Tactics.
Require Import Equations.Equations.

Equations foo (n : nat) : nat :=
foo n := n + k 0

  where k (x : nat) : nat :=
          { k 0 := 0 ; k (S n') := n }.

Variable f : nat -> (nat * nat).

Equations foo' (n : nat) : nat :=
foo' 0 := 0;
foo' (S n) := n + k (f 0) (0, 0)

  where k (x : nat * nat) (y : nat * nat) : nat :=
  { k (x, y) (x', y') := x }.

Variable kont : ((nat * nat) -> nat) -> nat.

Equations foo'' (n : nat) : nat :=
foo'' 0 := 0;
foo'' (S n) := n + kont absw

  where absw : (nat * nat) -> nat :=
  absw (x, y) := x.

Equations foo3 (n : nat) : nat :=
foo3 0 := 0;
foo3 (S n) := n + kont (#{ | (x, y) := x }).

Variant index : Set := i1 | i2.

Derive NoConfusion for index.

Inductive expr : index -> Set :=
| e1 : expr i1
| e2 {i} : expr i -> expr i2.

Derive Signature NoConfusion NoConfusionHom for expr.

Variable kont' : forall x : index, (expr x -> nat) -> nat.

Equations foo4 {i} (n : expr i) : nat :=
foo4 e1 := 0;
foo4 (@e2 i e) := absw e

  where absw : forall {i}, expr i -> nat :=
  absw e1 := 0;
  absw (e2 _) := 0.

Equations foo5 {i} (n : expr i) : nat :=
foo5 e1 := 0;
foo5 (@e2 i e) := absw e

  where absw : expr i -> nat :=
  absw e1 := 0;
  absw (e2 e') := 0.
