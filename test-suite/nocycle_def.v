From Equations Require Import Equations.
From Equations.Prop Require Import Subterm.

Derive Subterm for nat.

Equations noCycle (n : nat) (H : n = S n) : False := { }.
Equations noCycle' (n : nat) (H : S n = n) : False := { }.
