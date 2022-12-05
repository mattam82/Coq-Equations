From Equations Require Import Equations.

Inductive le : nat -> nat -> Prop :=
  | le_0 n : le 0 n
  | le_S n m : le n m -> le (S n) (S m).
Inductive le' : nat -> nat -> Prop :=
  | le'_0 n : le' n n
  | le'_S n m : le' n m -> le' n (S m).
Derive Signature for le le'.
Scheme le_dep := Induction for le Sort Prop.
Scheme le'_dep := Induction for le' Sort Prop.

Lemma le_irrel n m (p q : le n m) : p = q.
Proof.
  revert p. induction p using le_dep.
  depelim q. reflexivity.
  depelim q. apply f_equal, IHp.
Defined.

Lemma leprf_nocycle n : le (S n) n -> False.
Proof.
  intros H. depind H. auto.
Qed.
Derive Subterm for nat.

Set Equations With UIP.

Lemma le_refl n : le n n.
Proof. induction n; constructor; auto. Qed.

Lemma le_n_Sm n m : le n m -> le n (S m).
Proof.
  induction 1; constructor; auto.
Qed.

Lemma le'_le n m : le' n m -> le n m.
Proof.
  induction 1. apply le_refl. now apply le_n_Sm.
Qed.

Lemma le'prf_nocycle n : le' (S n) n -> False.
Proof.
  intros H%le'_le. now apply leprf_nocycle in H.
Qed.

Lemma le'_irrel n m (p q : le' n m) : p = q.
Proof.
  revert q. induction p using le'_dep.
  intros q. depelim q. reflexivity.
  exfalso.
  now eapply le'prf_nocycle in q.
  intros q.
  depelim q.
  exfalso. clear IHp.
  now eapply le'prf_nocycle in p.
  f_equal. apply IHp.
Defined.
