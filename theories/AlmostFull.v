Require Import Equations.
Require Import Relations Utf8.
Set Asymmetric Patterns.

Definition dec_rel {X:Type} (R : X → X → Prop) := ∀ x y, {not (R y x)} + {R y x}.

Section AlmostFull.
  Context {X : Type}.

  Inductive WFT : Type :=
  | ZT : WFT
  | SUP : (X -> WFT) -> WFT.

  Fixpoint SecureBy (R : X -> X -> Prop) (p : WFT) : Prop :=
    match p with
    | ZT => forall x y, R x y
    | SUP f => forall x, SecureBy (fun y z => R y z \/ R x y) (f x)
    end.

  Lemma SecureBy_mon p (R' S : X -> X -> Prop) (H : forall x y, R' x y -> S x y) :
    SecureBy R' p -> SecureBy S p.
  Proof.
    revert R' S H.
    induction p. simpl. intros. apply H. apply H0.
    simpl. intros.
    eapply H. 2:apply H1.
    intros. simpl in H2. intuition.
  Defined.

  Definition almost_full (R : X -> X -> Prop) := exists p, SecureBy R p.

  Context (R : X -> X -> Prop) (decR : dec_rel R).

  Fixpoint af_tree_iter {x : X} (accX : Acc R x) :=
    match accX with
    | Acc_intro f => SUP (fun y =>
                            match decR x y with
                            | left _ => ZT
                            | right Ry => af_tree_iter (f y Ry)
                            end)
    end.

  Context (wfR : well_founded R).
  Definition af_tree : X → WFT :=
    fun x => af_tree_iter (wfR x).

  Scheme Acc_ind_dep := Induction for Acc Sort Prop.

  Lemma secure_from_wf : SecureBy (fun x y => not (R y x)) (SUP af_tree).
  Proof.
    intro x. unfold af_tree. generalize (wfR x).
    induction a using Acc_ind_dep. simpl.
    intros y. destruct (decR x y). simpl.
    intuition. specialize (H y r).
    eapply SecureBy_mon; eauto. simpl; intros.
    intuition.
  Defined.

  Corollary af_from_wf : almost_full (fun x y => not (R y x)).
  Proof. exists (SUP af_tree). apply secure_from_wf. Defined.

End AlmostFull.

Corollary almost_full_le : almost_full le.
Admitted.

Arguments WFT X : clear implicits.

Section WfFromAF.
  Context {X : Type}.

  Lemma clos_trans_n1_left {R : X -> X -> Prop} x y z : R x y -> clos_trans_n1 _ R y z -> clos_trans_n1 _ R x z.
  Proof.
    induction 2. econstructor 2; eauto. constructor; auto.
    econstructor 2. eauto. auto.
  Defined.

  Lemma clos_trans_1n_n1 {R : X -> X -> Prop} x y : clos_trans_1n _ R x y -> clos_trans_n1 _ R x y.
  Proof.
    induction 1. now constructor. eapply clos_trans_n1_left; eauto.
  Defined.

  Lemma clos_refl_trans_right {R : X -> X -> Prop} x y z :
    R y z -> clos_refl_trans _ R x y -> clos_trans_n1 _ R x z.
  Proof.
    intros Ryz Rxy. apply clos_rt_rtn1_iff in Rxy.
    induction Rxy in Ryz, z |- *. econstructor 1; eauto. econstructor 2; eauto.
  Defined.

  Lemma clos_trans_1n_right {R : X -> X -> Prop} x y z : R y z -> clos_trans_1n _ R x y -> clos_trans_1n _ R x z.
  Proof.
    induction 2. econstructor 2; eauto. constructor; auto.
    econstructor 2. eauto. auto.
  Defined.

  Lemma clos_trans_n1_1n {R : X -> X -> Prop} x y : clos_trans_n1 _ R x y -> clos_trans_1n _ R x y.
  Proof.
    induction 1. now constructor. eapply clos_trans_1n_right; eauto.
  Defined.

  Lemma acc_from_af (p : WFT X) (T R : X → X → Prop) y :
    (∀ x z, clos_refl_trans X T z y ->
            clos_trans_1n X T x z ∧ R z x → False)
    → SecureBy R p → Acc T y.
  Proof.
    induction p as [|p IHp] in T, R, y |- * .
    + simpl. intros. constructor.
      intros z Tz. specialize (H z y). elim H. constructor 2. split; auto.
      constructor. auto.
    + intros cond secure. constructor. intros z Tzy.
      simpl in secure.
      specialize (IHp y T (fun y0 z0 => R y0 z0 \/ R y y0) z). apply IHp; auto.
      intros x w wz.
      assert(wy: clos_refl_trans X T w y).
      { econstructor 3. eauto. now constructor. }
      pose proof (cond x w wy). intuition.
      specialize (cond w y). apply cond. constructor 2.
      intuition. apply clos_trans_n1_1n. eapply clos_refl_trans_right; eauto.
  Defined.

  Lemma wf_from_af (p : WFT X) (T R : X → X → Prop) :
    (∀ x y, clos_trans_1n X T x y ∧ R y x → False)
    → SecureBy R p → well_founded T.
  Proof.
    intros. intro x. eapply acc_from_af; eauto.
  Defined.

End WfFromAF.

Class AlmostFull {X} (R : X -> X -> Prop) :=
  is_almost_full : almost_full R.

Set Equations Transparent.
Section FixAF.
  Context {X : Type} (T R : X -> X -> Prop).
  Context {af : AlmostFull R}.
  Context (H : forall x y, clos_trans_1n X T x y /\ R y x -> False).

  Global Instance af_wf : WellFounded T.
  Proof. red. destruct af. eapply wf_from_af; eauto. Defined.
End FixAF.

Equations cofmap {X Y : Type} (f : Y -> X) (p : WFT X) : WFT Y :=
  cofmap f ZT := ZT;
  cofmap f (SUP w) := SUP (fun y => cofmap f (w (f y))).
Transparent cofmap.
Lemma cofmap_secures {X Y : Type} (f : Y -> X) (p : WFT X) (R : X -> X -> Prop) :
  SecureBy R p -> SecureBy (fun x y => R (f x) (f y)) (cofmap f p).
Proof.
  induction p in R |- *; simpl; auto.
  intros.
  specialize (H (f x) (fun y z : X => R y z \/ R (f x) y)). simpl in H.
  apply H. apply H0.
Defined.

Instance AlmostFull_MR {X Y} R (f : Y -> X) : AlmostFull R -> AlmostFull (MR R f).
Proof. intros [p sec]. exists (cofmap f p). apply (cofmap_secures f p _ sec). Defined.

Equations T (x y : nat * nat) : Prop :=
  T (x0, x1) (y0, y1) := (x0 = y1 /\ x1 < y1) \/
                         (x0 = y1 /\ x1 < y0).

Equations R (x y : nat * nat) : Prop :=
  R (x0, x1) (y0, y1) := x0 <= y0 /\ x1 <= y1.

Fixpoint oplus_nullary {X:Type} (p:WFT X) (q:WFT X) :=
  match p with
  | ZT => q
  | SUP f => SUP (fun x => oplus_nullary (f x) q)
  end.

Lemma oplus_nullary_sec_intersection {X} (p : WFT X) (q: WFT X)
      (C : X → X → Prop) (A : Prop) (B : Prop) :
  SecureBy (fun y z => C y z ∨ A) p →
  SecureBy (fun y z => C y z ∨ B) q →
  SecureBy (fun y z => C y z ∨ (A ∧ B)) (oplus_nullary p q).
Proof.
  revert C.
  induction p; simpl; intros; auto.
  induction q in C, H, H0 |- *; simpl in *; intuition.
  specialize (H x y). specialize (H0 x y). intuition.
  specialize (H1 x (fun y z => (C y z \/ A /\ B) \/ C x y)). simpl in *.
  eapply SecureBy_mon. 2:eapply H1. simpl. intuition. intuition. firstorder auto.
  eapply SecureBy_mon. 2:eapply H0. simpl. firstorder auto.
  eapply SecureBy_mon. 2:eapply H. simpl.
  2:{ eapply SecureBy_mon. 2:eapply H0. simpl. firstorder auto. left; eapply H2.





  firstorder.

Definition fib : nat -> nat.
  unshelve epose (af_wf T R).
  red.


  apply Subterm.FixWf