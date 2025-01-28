From Equations.Prop Require Import Equations.


Fixpoint slow n : unit := match n with O => tt | S n => match slow n with tt => slow n end end.

#[local]
Obligation Tactic := idtac.
Goal slow  1 = tt /\ True -> True. intros H. dependent elimination H. assumption. Qed.
Goal slow 20 = tt /\ True -> True. intros H. dependent elimination H. assumption. Qed.
Goal slow 300 = tt /\ True -> True. intros H. Timeout 1 dependent elimination H. assumption. Qed.
Goal slow 5000 = tt /\ True -> True. intros H. Timeout 1 dependent elimination H. assumption. Qed.