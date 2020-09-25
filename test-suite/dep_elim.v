From Equations Require Import Equations.

(* Testing the [dep_elim] tactic that leaves everything
   (that it didn't simplify) on the goal
   so that hypothesis can be explicitly named *)

Goal forall x : nat, let y := S x in let z := S y in x = x.
Proof.
  intros.
  dep_elim x.
  exact eq_refl.
  intro n ; exact eq_refl.
Defined.

Inductive le : nat -> nat -> Prop :=
| le_eq (n:nat) : le n n
| le_S {n m : nat} : le n m -> le n (S m).

Goal forall (x y : nat) (i : le x y), y = y.
Proof.
  intros.
  dep_elim i.
  - intro n ; exact eq_refl.
  - intros n m lenm; exact eq_refl.
Defined.
