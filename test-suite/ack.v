(* https://lawrencecpaulson.github.io/2022/08/31/Ackermann-not-PR-I.html *)
Require Import Arith Lia.
From Equations.Prop Require Import Equations.

Equations ack (p : nat * nat) : nat by wf p (lexprod _ _ lt lt) :=
ack (0, n) := S n;
ack (S m, 0) := ack (m, 1);
ack (S m, S n) := ack (m, ack (S m, n)).

Import Nat Peano.

Lemma lt_ack2 i j: j < ack(i,j).
Proof. funelim (ack (i, j)).
- constructor.
- eapply lt_trans. 2: exact H. constructor.
- exact (le_lt_trans _ _ _ H H0).
Qed.

Lemma ack_lt_ack_S2 i j: ack(i, j) < ack (i, S j).
Proof. induction i, j; simp ack; apply lt_ack2. Qed.

Lemma ack_lt_mono2 i j k: j < k -> ack(i,j) < ack(i,k).
Proof. intro H. induction H.
- apply ack_lt_ack_S2.
- eapply lt_trans. exact IHle. apply ack_lt_ack_S2.
Qed.

Lemma lt_mono_imp_le_mono f (LTM: forall n m, n < m -> f n < f m):
forall n m, n <= m -> f n <= f m.
Proof. intros n m H. induction H.
- constructor.
- eapply le_trans. exact IHle. apply lt_le_incl, LTM, lt_succ_diag_r.
Qed.

Lemma ack_le_mono2 k i j: j <= k -> ack(i,j) <= ack(i,k).
Proof. apply (lt_mono_imp_le_mono (fun n => ack(i,n))). apply ack_lt_mono2. Qed.

Lemma ack2_le_ack1 i j: ack (i, S j) <= ack (S i, j).
Proof. induction j; simp ack.
- constructor.
- apply ack_le_mono2. eapply le_trans. exact (lt_ack2 i (S j)). exact IHj.
Qed.

Lemma S_less_ack_S1 i j: S j < ack(S i, j).
Proof. induction j; simp ack.
- apply lt_ack2.
- eapply lt_le_trans. apply lt_ack2. exact (ack_le_mono2 _ _ _ IHj).
Qed.

Lemma ack_lt_ack_S1 i j: ack(i,j) < ack(S i, j).
Proof. induction j; simp ack; apply ack_lt_mono2.
- exact lt_0_1.
- apply S_less_ack_S1.
Qed.

Lemma lt_ack1 i j: i < ack(i,j).
Proof. induction i; simp ack.
- apply lt_0_succ.
- eapply le_lt_trans. exact IHi. apply ack_lt_ack_S1.
Qed.

Lemma ack_1 j: ack(1,j) = j + 2.
Proof. induction j; simp ack.
- constructor.
- now rewrite IHj.
Qed.

Lemma ack_2 j: ack(2,j) = 2 * j + 3.
Proof. induction j; simp ack.
- trivial.
- rewrite IHj, ack_1. lia.
Qed.

Lemma ack_lt_mono1 k i j: i < j -> ack(i, k) < ack(j, k).
Proof. intro H. induction H.
- apply ack_lt_ack_S1.
- eapply lt_trans. apply IHle. apply ack_lt_ack_S1.
Qed.

Lemma ack_le_mono1 k i j: i <= j -> ack(i, k) <= ack(j, k).
Proof. apply (lt_mono_imp_le_mono (fun n => ack(n, k))). apply ack_lt_mono1. Qed.

Lemma ack_nest_bound i1 i2 j: ack(i1, ack(i2,j)) < ack(2 + i1 + i2, j).
Proof.
assert (ack (i1, ack (i2, j)) < ack(i1 + i2, ack(S (i1 + i2), j))). {
eapply Nat.le_lt_trans. apply ack_le_mono1. 2: apply ack_lt_mono2.
- apply le_add_r.
- apply ack_lt_mono1. auto with arith.
}
eapply Nat.lt_le_trans. apply H. rewrite <- ack_equation_3.
apply ack2_le_ack1.
Qed.

Lemma ack_add_bound i1 i2 j: ack(i1,j) + ack(i2,j) < ack (4 + i1 + i2, j).
Proof.
apply (lt_trans _ (ack(2, ack(i1 + i2, j))) _).
- rewrite ack_2.
pose (H1 := ack_le_mono1 j i1 (i1 + i2)).
pose (H2 := ack_le_mono1 j i2 (i1 + i2)).
lia.
- apply ack_nest_bound.
Qed.

Lemma ack_add_bound2 i j k (H: i < ack(k,j)): i + j < ack (4 + k, j).
Proof.
replace (4 + k) with (4 + k + 0) by apply add_0_r.
eapply lt_trans. 2: apply (ack_add_bound k 0 j).
rewrite ack_equation_1. apply add_lt_mono.
- exact H.
- apply lt_succ_diag_r.
Qed.
