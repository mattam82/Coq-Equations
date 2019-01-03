Require Import TestSuite.issues.issue95_1.
Require Import Omega.
Require Import Equations.Equations.

Lemma l:
  forall T t,
    transport t T ->
    forall t',
      transport t' T.
Proof.
  induction T; intuition auto; try omega.
  - Timeout 1 simp transport in *. intuition.
Qed.