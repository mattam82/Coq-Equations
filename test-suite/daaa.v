From Equations Require Import Equations.
Inductive A : Set :=
  a : A
| d : A -> A -> A -> A.

Equations action (x : A) : A :=
action (d a a a) := (d a a a);
action (d x y z) := a;
action a := a.

Equations lem (x : A) (p : x <> d a a a) : action x = a :=
lem (d a a a) p := False_rect _ (p eq_refl);
lem (d x y z) p := eq_refl;
lem a p := eq_refl.