(** Proving Termination of Normalization Functions for Conditional Expressions, L. Paulson *)
From Equations Require Import Equations.

Require Import List Program.Syntax Arith Lia.

Inductive exp := At | If : exp -> exp -> exp -> exp.

Equations exp_size : exp -> nat :=
  exp_size At := 1;
  exp_size (If e1 e2 e3) := exp_size e1 * (1 + exp_size e2 + exp_size e3).
Transparent exp_size.

Lemma exp_size_pos (x : exp) : (0 < exp_size x)%nat.
Proof. funelim (exp_size x); auto; try lia. apply Nat.mul_pos_pos; auto. lia. Qed.
Hint Resolve exp_size_pos : core.

Set Program Mode.

Lemma size_1:
  forall y z : exp, exp_size y < S (exp_size y + exp_size z + 0).
Proof.
  intros y z. lia.
Qed.

Lemma size_2:
  forall y z : exp, exp_size z < S (exp_size y + exp_size z + 0).
Proof.
  intros y z. lia.
Qed.

Lemma size_3 u v w y z : exp_size (If v y z) < exp_size (If (If u v w) y z).
Proof.
  simp exp_size.
  assert (1 + exp_size y + exp_size z > 0) by lia. revert H.
  generalize (1 + exp_size y + exp_size z). intros n Hn.
  generalize (exp_size_pos u). intros.
  rewrite 2 Nat.mul_add_distr_l.
  nia.
Qed.

Lemma size_4 u v w y z : exp_size (If w y z) < exp_size (If (If u v w) y z).
Proof.
  simp exp_size.
  assert (1 + exp_size y + exp_size z > 0) by lia. revert H.
  generalize (1 + exp_size y + exp_size z). intros n Hn.
  generalize (exp_size_pos u). intros.
  rewrite 2 Nat.mul_add_distr_l.
  nia.
Qed.

Lemma size_5:
  forall u v w y z x : exp,
    exp_size x <= exp_size (If v y z) ->
    forall x0 : exp, exp_size x0 <= exp_size (If w y z) -> exp_size (If u x x0) < exp_size (If (If u v w) y z).
Proof.
  intros u v w y z x l x0 l0.
  simp exp_size. rewrite <- Nat.mul_assoc. apply mult_lt_compat_l; auto.
  eapply Nat.le_lt_trans with (1 + exp_size (If v y z) + exp_size (If w y z)). lia.
  simp exp_size. simpl. rewrite Nat.mul_add_distr_r.
  generalize (exp_size_pos y). lia.
Qed.

Lemma size_6:
  forall u v w y z x : exp,
    exp_size x <= exp_size (If v y z) ->
    forall x0 : exp,
      exp_size x0 <= exp_size (If w y z) ->
      forall x1 : exp, exp_size x1 <= exp_size (If u x x0) -> exp_size x1 <= exp_size (If (If u v w) y z).
Proof.
  intros u v w y z x l x0 l0 x1 l1.
  simp exp_size. transitivity (exp_size (If u x x0)); auto.
  simp exp_size. simp exp_size in *. rewrite <- Nat.mul_assoc. apply mult_le_compat_l.
  transitivity (1 + (exp_size v * (1 + exp_size y + exp_size z)) + (exp_size w * (1 + exp_size y + exp_size z))).
  lia. lia.
Defined.

Equations? nm_dep (e : exp) : { e' : exp | exp_size e' <= exp_size e } by wf (exp_size e) lt :=
  nm_dep At := At;
  nm_dep (If At y z) := If At (nm_dep y) (nm_dep z);
  nm_dep (If (If u v w) y z) with nm_dep (If v y z), nm_dep (If w y z) :=
  { | exist _ t Ht | exist _ e He := nm_dep (If u t e) }.
Proof.
  apply size_1. apply size_2.
  all:repeat destruct nm_dep; simpl; try solve [simp exp_size; simpl; try lia].
  apply size_3. apply size_4. apply size_5; auto. simpl in *. eapply size_6; eauto.
Defined.

Equations nm (e : exp) : exp :=
  nm At := At;
  nm (If At y z) := If At (nm_dep y) (nm_dep z);
  nm (If (If u v w) y z) := nm_dep (If u (nm_dep (If v y z)) (nm_dep (If w y z))).

Lemma nm_eq e : nm e = nm_dep e.
Proof. funelim (nm_dep e); simp nm. simpl. rewrite Heq, Heq0. simpl. reflexivity. Qed.

Extraction nm_dep.
Transparent nm.
Eval vm_compute in nm (If (If At At At) At At).
