Require Import Arith List Lia.
From Equations Require Import CoreTactics.
From Equations.Prop Require Import Logic DepElim FunctionalInduction.
From Equations Require Import Equations.
Import ListNotations.

Inductive Subseq {A : Type} : list A -> list A -> Prop :=
| Subseq_nil : Subseq [] []
| Subseq_take : forall a xs ys, Subseq xs ys -> Subseq (a :: xs) (a :: ys)
| Subseq_drop : forall a xs ys, Subseq xs ys -> Subseq xs (a :: ys).

Definition IsLCS {A : Type} (zs xs ys : list A) : Prop :=
  Subseq zs xs /\ Subseq zs ys /\
  forall zs', Subseq zs' xs -> Subseq zs' ys -> length zs' <= length zs.

Section lcs.
  Context {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}).

  Equations lcs 
          (l1 l2 : list A) : list A by wf (length l1 + length l2) lt :=
  lcs [] _ := [];
  lcs _ [] := [];
  lcs (x :: l1) (y :: l2) := 
    if eq_dec x y then x :: lcs l1 l2 else
      let s1 := lcs (x :: l1) l2 in
      let s2 := lcs l1 (y :: l2) in
      if length s1 <? length s2 then s2 else s1.
Next Obligation. simpl; lia. Qed.
Next Obligation. simpl; lia. Qed.
End lcs.

Lemma Subseq_nil_l : forall {A} (l : list A), Subseq [] l.
Proof.
  induction l.
  - constructor.
  - constructor. assumption.
Qed.

Lemma Subseq_elim_cons_l : forall {A} a (l1 l2 : list A),
  Subseq (a :: l1) l2 -> Subseq l1 l2.
Proof.
  intros. revert dependent a. induction l2; intros.
  - inversion H.
  - inversion H; subst.
    + constructor. assumption.
    + constructor. eapply IHl2. eassumption.
Qed.

Lemma Subseq_elim_cons : forall {A} a1 a2 (l1 l2 : list A),
  Subseq (a1 :: l1) (a2 :: l2) -> Subseq l1 l2.
Proof.
  intros. inversion H; subst.
  - assumption.
  - apply Subseq_elim_cons_l in H2. assumption.
Qed.

Lemma Subseq_elim_cons_neq : forall {A} a1 a2 (l1 l2 : list A),
  a1 <> a2 ->
  Subseq (a1 :: l1) (a2 :: l2) -> Subseq (a1 :: l1) l2.
Proof.
  intros. inversion H0; subst.
  - contradiction.
  - assumption.
Qed.

Theorem lcs_correct : forall {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) xs ys,
  IsLCS (lcs eq_dec xs ys) xs ys.
Proof.
  intros A eq_dec xs ys.
  funelim_constr (lcs eq_dec xs ys).
  - split; [|split].
  + constructor.
  + simp lcs. apply Subseq_nil_l.
  + intros. inversion H; subst. apply le_0_n.
- split; [|split].
  + simp lcs; apply Subseq_nil_l.
  + constructor.
  + intros. inversion H0; subst. apply le_n.
- simp lcs. destruct (eq_dec x y).
  + specialize (H e). destruct H as (HH1 & HH2 & HH3).
    subst.
    split; [|split].
    * constructor. simp lcs.
    * constructor. assumption.
    * intros. destruct zs'.
      -- apply le_0_n.
      -- apply Subseq_elim_cons in H.
         apply Subseq_elim_cons in H2.
         cbn. apply le_n_S. eauto.
  + specialize (H0 n). specialize (H1 n).
    set (s1 := lcs eq_dec (x::l1) l2) in *.
    set (s2 := lcs eq_dec l1 (y::l2)) in *.
    destruct H0 as (H01 & H02 & H03).
    destruct H1 as (H11 & H12 & H13).
    cbn zeta.
    destruct (Nat.ltb_spec (length s1) (length s2)).
    * split; [|split].
      -- constructor. assumption.
      -- assumption.
      -- intros. inversion H1; subst.
         ++ apply Subseq_elim_cons_neq in H2; try assumption.
            specialize (H03 _ H1 H2). lia.
         ++ auto.
    * split; [|split].
      -- assumption.
      -- constructor. assumption.
      -- intros. inversion H1; subst.
         ++ apply Subseq_elim_cons_neq in H2; try assumption.
            specialize (H03 _ H1 H2). assumption.
         ++ rewrite <- H0. eauto.
  Qed.
  