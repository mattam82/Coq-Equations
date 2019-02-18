From Equations Require Import Equations.

Require Import List.
Import ListNotations.

Equations test {A} (n : nat) (gs : list A) : unit by wf n lt :=
  test 0 _ := tt;
  test (S n) gs := aux gs []
     where aux (l : list A) (acc : list A) : unit by wf (length l) lt :=
     aux nil acc := tt;
     aux (g :: gs') acc with acc := {
                             | nil => tt;
                             | g' :: gs'' => aux gs' acc
                           }.
