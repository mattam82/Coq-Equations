From Equations.Prop Require Import Equations.

Goal forall x : nat, let y := S x in let z := S y in x = x.
Proof.
  intros.
  dependent elimination x.
  exact eq_refl.
  exact eq_refl.
Defined.

Inductive ind : nat -> Set := cstr : ind 0.


Goal forall (x : nat) (i : ind x), let y := S x in let z := S y in x = x.
Proof.
  intros.
  set(foo := 0). move foo after x.
  dependent elimination i.
  exact eq_refl.
Defined.