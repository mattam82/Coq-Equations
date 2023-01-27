Require Import TestSuite.issues.issue95_1.
Require Import Lia.
Require Import Equations.Prop.Equations.

Lemma l:
  forall T t,
    transport t T ->
    forall t',
      transport t' T.
Proof.
  induction T; intuition auto; try lia.
  - Timeout 1 simp transport in *. intuition auto with *.
Qed.