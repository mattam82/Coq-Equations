From Stdlib Require Import List.
From Equations.Prop Require Import Equations.

Equations app {A} : list A -> list A -> list A :=
app xs ys := fold_right cons ys xs.