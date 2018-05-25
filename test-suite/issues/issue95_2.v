Require Import issue95.
Require Import Omega.
Require Import Equations.Equations.

Lemma l:
  forall T t,
    transport t T ->
    forall t',
      transport t' T.
Proof.
  induction T; intuition auto; try omega.
  - 
    unfold transport.
    simp transport in *.
Abort.