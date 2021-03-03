From Equations Require Import Equations.

(* Testing the [depcase] tactic that does a dependent case analysis
   on its argument leaving the hypothesis on the goal
   so that they can be explicitly named *)

Goal forall x : nat, let y := S x in let z := S y in x = x.
Proof.
  intros.
  depcase x.
  exact eq_refl.
  intros n ; exact eq_refl.
Defined.

Inductive le : nat -> nat -> Prop :=
| le_eq (n:nat) : le n n
| le_S {n m : nat} : le n m -> le n (S m).

Goal forall (x y : nat) (i : le x y), y = y.
Proof.
  intros.
  depcase i.
  - intro n ; exact eq_refl.
  - intros n m lenm ; exact eq_refl.
Defined.

(* Testing the [dep_elim] tactic that does a dependent induction
   on its argumente leaving the hypothesis on the goal
   so that they can be explicitly named *)

Goal forall x : nat, let y := S x in let z := S y in x = x.
Proof.
  intros.
  dep_elim x.
  exact eq_refl.
  intros n IH ; exact eq_refl.
Defined.

Inductive le : nat -> nat -> Prop :=
| le_eq (n:nat) : le n n
| le_S {n m : nat} : le n m -> le n (S m).

Goal forall (x y : nat) (i : le x y), y = y.
Proof.
  intros.
  dep_elim i.
  - intro n ; exact eq_refl.
  - intros n m lenm IH ; exact eq_refl.
Defined.
