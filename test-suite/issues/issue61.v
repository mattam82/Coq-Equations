From Equations Require Import Equations.

Fail Equations bug (x : nat) : nat :=
  bug O := O;
  bug (S n) <= 2 => {
   | x <= 3 => {
     | x => x
   }
  }.

Equations bug (x : nat) : nat :=
  bug O := O;
  bug (S n) <= 2 => {
   | y <= 3 => {
     | x => x
   }
  }.

Definition check := eq_refl : bug 1 = 3.