From Equations Require Import Equations.
Require Import Equations.Prop.Subterm.

Derive Subterm for nat.

Equations noCycle (n : nat) (H : n = S n) : False := { }.
Equations noCycle' (n : nat) (H : S n = n) : False := { }.
