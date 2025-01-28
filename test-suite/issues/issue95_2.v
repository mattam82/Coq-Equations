From Stdlib Require Import TestSuite.issues.issue95_1.
From Stdlib Require Import Lia.
From Equations.Prop Require Import Equations.


Lemma l:
  forall T t,
    transport t T ->
    forall t',
      transport t' T.
Proof.
  induction T; intuition auto; try lia.
  - Timeout 1 simp transport in *. intuition auto with *.
Qed.