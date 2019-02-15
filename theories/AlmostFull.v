Require Import Equations.
Require Import Relations Utf8.
Set Asymmetric Patterns.

Definition dec_rel {X:Type} (R : X → X → Prop) := ∀ x y, {not (R y x)} + {R y x}.

Section AlmostFull.
  Context {X : Type}.

  Inductive WFT : Type :=
  | ZT : WFT
  | SUP : (X -> WFT) -> WFT.
  Derive NoConfusion Subterm for WFT.

  Definition sec_disj (R : X -> X -> Prop) x y z := R y z \/ R x y.

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

Class AlmostFull {X} (R : X -> X -> Prop) :=
  is_almost_full : almost_full R.

Require Import Setoid RelationClasses Morphisms.
Instance proper_af X : Proper (relation_equivalence ==> iff) (@AlmostFull X).
Proof.
  intros R S eqRS.
  split; intros.
  destruct H as [p Hp]. exists p.
  revert R S eqRS Hp. induction p; simpl in *; intros. now apply eqRS.
  apply (H x (fun y z => R y z \/ R x y)). repeat red; intuition.
  apply Hp.

  destruct H as [p Hp]. exists p.
  revert R S eqRS Hp. induction p; simpl in *; intros. now apply eqRS.
  apply (H x _ (fun y z => S y z \/ S x y)). repeat red; intuition.
  apply Hp.
Qed.

Instance almost_full_le : AlmostFull le.
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
    intros. intro x. eapply acc_from_af;eauto.
  Defined.

  Equations power (k : nat) (T : X -> X -> Prop) : X -> X -> Prop :=
    power 0 T := T;
    power (S k) T := fun x y => exists z, power k T x z /\ T z y.
  Transparent power.

  Lemma acc_incl (T T' : X -> X -> Prop) x : (forall x y, T' x y -> T x y) -> Acc T x -> Acc T' x.
  Proof.
    intros HT H; induction H in |- *.
    constructor. intros. apply HT in H1. now apply H0.
  Qed.
  Require Import Relations Wellfounded.

  Lemma power_clos_trans (T : X -> X -> Prop) k : inclusion _ (power k T) (clos_trans _ T).
  Proof.
    intros x y. induction k in x, y |- *. simpl. now constructor.
    simpl. intros [z [Pxz Tzy]]. econstructor 2. apply IHk; eauto. constructor. auto.
  Qed.

  Lemma acc_power (T : X -> X -> Prop) x k : Acc T x -> Acc (power k T) x.
  Proof.
    intros. apply Acc_clos_trans in H. revert H.
    apply acc_incl. intros. now apply (power_clos_trans _ k).
  Qed.

  Equations secure_power (k : nat) (p : WFT X) : WFT X :=
    secure_power 0 p := p;
    secure_power (S k) p := SUP (fun x => secure_power k p).
  Transparent secure_power.
  Lemma secure_by_power R p (H : SecureBy R p) k :
    SecureBy R (secure_power k p).
  Proof.
    induction k in R, p, H |- *; trivial.
    induction p. simpl in *. intros. apply IHk. simpl. intuition.
    simpl. intros.
    apply IHk. simpl. intros. simpl in H0. simpl in H.
    specialize (H x0). eapply SecureBy_mon. 2:eauto. simpl. intuition.
  Qed.

  Lemma acc_from_power_af (p : WFT X) (T R : X → X → Prop) y k :
    (∀ x z, clos_refl_trans _ T z y ->
            clos_trans_1n X (power k T) x z ∧ R z x → False)
    → SecureBy R (secure_power k p) → Acc T y.
  Proof.
    (* induction k in T, R, y |- *. simpl. intros. simp secure_power in H0. eapply acc_from_af; eauto. admit. *)
    (* intros. *)
    (* simp secure_power in H0. simpl in H0. *)
    (* constructor. intros x Txy. *)
    (* specialize (IHk T (sec_disj R x)). specialize (H0 x). *)
    (* apply IHk; auto. *)
    (* intros. destruct H1; subst. unfold sec_disj in *. *)
    (* intuition. *)
    (* intuition. red in H4. apply (H x z). *)





    induction p as [|p IHp] in T, R, y, k |- * .
  (*   + simpl. intros. constructor. *)
  (*     intros z Tz. specialize (H z y). elim H. constructor 2. split; auto. *)
  (*     constructor. auto. *)
  (*   + intros cond secure. constructor. intros z Tzy. *)
  (*     simpl in secure. *)
  (*     specialize (IHp y T (fun y0 z0 => R y0 z0 \/ R y y0) z). eapply (IHp k); auto. *)
  (*     intros x w wz. *)
  (*     assert(wy: clos_refl_trans X (power (S k) T) w y). *)
  (*     { econstructor 3. eauto. constructor.    now constructor. } *)
  (*     pose proof (cond x w wy). intuition. *)
  (*     specialize (cond w y). apply cond. constructor 2. *)
  (*     intuition. apply clos_trans_n1_1n. eapply clos_refl_trans_right; eauto. *)
  (* Defined. *)
    Admitted.

    (* induction k. eapply acc_from_af; eauto. *)
    (* apply IHk. intros. eapply H. eauto. *)
    (* constructor. intros. *)
    (* apply IHk; auto. intros x z Hzy [Hxz Rzx]. *)
    (* specialize (H x z). *)
    (* specialize (H x _ H2). apply H. split; intuition. *)
    (* induction H4. constructor. simpl. exists *)

(* eapply acc_power with 0. eapply acc_from_af; eauto. intros. intuition. *)
(*     simpl power in *. *)
(*     apply clos_trans_1n_n1 in H3. destruct H3. *)
(*     specialize (H x _ H1). apply H; split; auto. *)
(*     specialize (H *)
(*     induction p as [|p IHp] in T, R, y |- * . *)
(*     + simpl. intros. constructor. *)
(*       intros z Tz. specialize (H z y). elim H. constructor 2. split; auto. *)
(*       constructor. auto. *)
(*     + intros cond secure. constructor. intros z Tzy. *)
(*       simpl in secure. *)
(*       specialize (IHp y T (fun y0 z0 => R y0 z0 \/ R y y0) z). apply IHp; auto. *)
(*       intros x w wz. *)
(*       assert(wy: clos_refl_trans X T w y). *)
(*       { econstructor 3. eauto. now constructor. } *)
(*       pose proof (cond x w wy). intuition. *)
(*       specialize (cond w y). apply cond. constructor 2. *)
(*       intuition. apply clos_trans_n1_1n. eapply clos_refl_trans_right; eauto. *)
(*   Defined. *)

  Lemma wf_from_power_af (p : WFT X) (T R : X → X → Prop) k :
    (∀ x y, clos_trans_1n X (power k T) x y ∧ R y x → False)
    → SecureBy R p → well_founded T.
  Proof.
    intros. intro x. eapply acc_from_power_af; eauto. apply secure_by_power. apply H0.
  Defined.

End WfFromAF.

Set Equations Transparent.
Section FixAF.
  Context {X : Type} (T R : X -> X -> Prop).
  Context {af : AlmostFull R}.
  Context (H : forall x y, clos_trans_1n X T x y /\ R y x -> False).

  Global Instance af_wf : WellFounded T.
  Proof. red. destruct af. eapply wf_from_af; eauto. Defined.
End FixAF.

Section PowerAf.
  Context {X : Type}.
  Context (T R : X -> X -> Prop).
  Context {af : AlmostFull R}.
  Context (k : nat).
  Context (H : forall x y, clos_trans_1n X (power k T) x y /\ R y x -> False).

  Global Instance af_power_wf : WellFounded T.
  Proof.
    destruct af as [p Sp].
    eapply wf_from_power_af; eauto.
  Defined.
End PowerAf.

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
  revert C q.
  induction p; simpl; intros; auto.
  induction q in C, H, H0 |- *; simpl in *; intuition.
  specialize (H x y). specialize (H0 x y). intuition.
  specialize (H1 x (fun y z => (C y z \/ A /\ B) \/ C x y)). simpl in *.
  eapply SecureBy_mon. 2:eapply H1. simpl. intuition. intuition. firstorder auto.
  eapply SecureBy_mon. 2:eapply H0. simpl. firstorder auto.

  specialize (H x (fun y z => C y z \/ C x y)). simpl in *.
  eapply SecureBy_mon. 2:eapply H. all:simpl.
  intros. firstorder auto.
  eapply SecureBy_mon. 2:eapply H0. simpl. intros. intuition.
  eapply SecureBy_mon. 2:eapply H1. simpl. intros. intuition.
Qed.

Section OplusUnary.
  Context {X : Type}.

(*   Equations oplus_unary (p : WFT X) (q : WFT X) : WFT X by struct p := *)
(*   oplus_unary ZT q := q; *)
(*   oplus_unary (SUP f) g := SUP (fun x => oplus_unary_right g x) *)

(*     where oplus_unary_right (q : WFT X) (x : X) : WFT X by struct q := *)
(*     { oplus_unary_right ZT x := f x; *)
(*       oplus_unary_right (SUP g) x := *)
(*         oplus_nullary (oplus_unary (f x) (SUP g)) *)
(*                       (oplus_unary_right (g x) x) }. *)
(*   Next Obligation. *)
(*   Proof. revert p q. fix auxp 1. destruct p. intros. clear auxp; simp oplus_unary. *)
(*          destruct q. constructor. constructor. intros. *)
(*          intros. constructor. generalize (SUP w0) at 2 4. *)
(*          fix auxq 1. intros. destruct w1. clear auxp auxq. simp oplus_unary. *)
(*          Transparent oplus_unary. simpl. constructor. intros. apply auxp. *)
(*          intros. apply auxq. *)
(*   Defined. *)
(* End OplusUnary. *)
(* FIXME bug*)

  Equations? oplus_unary (p : WFT X) (q : WFT X) : WFT X
    by wf (p, q) (Subterm.lexprod _ _ WFT_subterm WFT_subterm) :=
  oplus_unary ZT q := q;
  oplus_unary p ZT := p;
  oplus_unary (SUP f) (SUP g) :=
      SUP (fun x => oplus_nullary (oplus_unary (f x) (SUP g))
                                  (oplus_unary (SUP f) (g x))).
  Proof. repeat constructor.
         constructor 2. repeat constructor.
  Defined.

  Equations? oplus_binary (p : WFT X) (q : WFT X) : WFT X
    by wf (p, q) (Subterm.lexprod _ _ WFT_subterm WFT_subterm) :=
  oplus_binary ZT q := q;
  oplus_binary p ZT := p;
  oplus_binary (SUP f) (SUP g) :=
      SUP (fun x => oplus_unary (oplus_binary (f x) (SUP g))
                                (oplus_binary (SUP f) (g x))).
  Proof. repeat constructor.
         constructor 2. repeat constructor.
  Defined.

End OplusUnary.
(* FIXME bug *)

(*   Equations oplus_unary (p : WFT X) : WFT X -> WFT X by struct p := *)
(*   oplus_unary ZT := fun q => q; *)
(*   oplus_unary (SUP f) := oplus_unary_right *)

(*     where oplus_unary_right (q : WFT X) : WFT X by struct q := *)
(*     { oplus_unary_right ZT := SUP f; *)
(*       oplus_unary_right (SUP g) := *)
(*         SUP (fun x => oplus_nullary (oplus_unary (f x) (SUP g)) *)
(*                                     (oplus_unary_right (g x))) }. *)
(*   Next Obligation. *)
(*   Proof. revert p. fix auxp 1. destruct p. intros. clear auxp; simp oplus_unary. *)
(*          intros. constructor. *)
(*          fix auxq 1. intros. destruct q. clear auxp auxq. simp oplus_unary. *)
(*          Transparent oplus_unary. simpl. constructor. intros; apply auxp. *)
(*          intros. apply auxq. *)
(*   Defined. *)
(* End OplusUnary. *)
(* (* FIXME bug *) *)

Set Firstorder Solver auto.

Lemma oplus_unary_sec_intersection {X} (p q : WFT X)
      (C : X -> X -> Prop) (A B : X -> Prop) :
  SecureBy (fun y z => C y z \/ A y) p ->
  SecureBy (fun y z => C y z \/ B y) q ->
  SecureBy (fun y z => C y z \/ (A y /\ B y)) (oplus_unary p q).
Proof.
  intros.
  revert H H0. revert q C. induction p.
  intros. simp oplus_unary. eapply SecureBy_mon; [|eapply H0]. firstorder.
  simpl. induction q. simpl. intros.
  eapply SecureBy_mon; [|eapply H0]. simpl. firstorder auto.
  intros.
  simp oplus_unary. simpl. intros x.
  eapply SecureBy_mon; [|eapply (oplus_nullary_sec_intersection _ _ _ (A x) (B x))]. simpl.
  intros. destruct H3; [|intuition]. rewrite <- or_assoc. left. eapply H3.
  - simpl. simpl in H2.
    eapply SecureBy_mon; [|eapply (H _ _ (fun y z => C y z \/ C x y \/ A x))]; auto. simpl; intros.
    intuition auto.
    eapply SecureBy_mon; [|eapply H1]; simpl. intros. intuition auto.
    simpl. intros.
    eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto.
  - simpl. eapply SecureBy_mon; [|eapply (H0 _ (fun y z => C y z \/ C x y \/ B x))]; simpl. intuition auto.
    intuition. simpl in H2. eapply SecureBy_mon; [|eapply H1]; simpl. intuition auto.
    eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto.
Defined.

Lemma oplus_unary_sec_intersection' {X} (p q : WFT X)
      (C : X -> X -> Prop) (A B : X -> Prop) :
  SecureBy (fun y z => C y z \/ A y) p ->
  SecureBy (fun y z => C y z \/ B y) q ->
  SecureBy (fun y z => C y z \/ (A y /\ B y)) (oplus_unary p q).
Proof.
  revert p q C A B; intros p q. funelim (oplus_unary p q); simpl; intros.
  eapply SecureBy_mon. 2:eapply H0. simpl. firstorder.
  eapply SecureBy_mon; [|eapply H]. simpl; firstorder.
  eapply SecureBy_mon. 2:eapply (oplus_nullary_sec_intersection _ _ _ (A x) (B x)). simpl.
  intros. destruct H3; [|intuition auto]. rewrite <- or_assoc. left. eapply H3.
  - simpl.
    eapply SecureBy_mon; [|eapply (H _ (fun y z => C y z \/ C x y \/ A x) A B)]. simpl.
    intuition auto.
    eapply SecureBy_mon; [|eapply H1]; simpl. intros. intuition auto.
    simpl. intros.
    eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto.
  - simpl. specialize (H0 x (SUP w) (w0 x)). simplify_IH_hyps. eapply SecureBy_mon; [|eapply (H0 (fun y z => C y z \/ C x y \/ B x) A B)]; simpl. intuition auto.
    intuition. simpl in H2. eapply SecureBy_mon; [|eapply H1]; simpl. intuition auto.
    eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto.
Qed.

Lemma oplus_binary_sec_intersection' {X} (p q : WFT X)
      (C : X -> X -> Prop) (A B : X -> X -> Prop) :
  SecureBy (fun y z => C y z \/ A y z) p ->
  SecureBy (fun y z => C y z \/ B y z) q ->
  SecureBy (fun y z => C y z \/ (A y z /\ B y z)) (oplus_binary p q).
Proof.
  revert p q C A B; intros p q. funelim (oplus_binary p q); simpl; intros.
  eapply SecureBy_mon. 2:eapply H0. simpl. firstorder.
  eapply SecureBy_mon; [|eapply H]. simpl; firstorder.
  eapply SecureBy_mon. 2:eapply (oplus_unary_sec_intersection _ _ _ (A x) (B x)). simpl.
  intros. destruct H3; [|intuition auto]. rewrite <- or_assoc. left. eapply H3.
  - simpl.
    eapply SecureBy_mon; [|eapply (H _ (fun y z => C y z \/ C x y \/ A x y) A B)]. simpl.
    intuition auto.
    eapply SecureBy_mon; [|eapply H1]; simpl. intros. intuition auto.
    simpl. intros.
    eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto.
  - simpl. specialize (H0 x (SUP w) (w0 x)). simplify_IH_hyps.
    eapply SecureBy_mon; [|eapply (H0 (fun y z => C y z \/ C x y \/ B x y) A B)]; simpl. intuition auto.
    intuition. simpl in H2. eapply SecureBy_mon; [|eapply H1]; simpl. intuition auto.
    eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto.
Defined.

Lemma oplus_binary_sec_intersection {X} (p q : WFT X)
      (A B : X -> X -> Prop) :
  SecureBy A p ->
  SecureBy B q ->
  SecureBy (fun y z => A y z /\ B y z) (oplus_binary p q).
Proof.
  revert p q A B; intros p q. funelim (oplus_binary p q); simpl; intros.
  eapply SecureBy_mon. 2:eapply H0. simpl. firstorder.
  eapply SecureBy_mon; [|eapply H]. simpl; firstorder.
  eapply SecureBy_mon. 2:eapply (oplus_unary_sec_intersection _ _ _ (A x) (B x)). simpl.
  intros. destruct H3; [|intuition auto]. left. eapply H3.
  - simpl.
    eapply SecureBy_mon; [|eapply (H _ (fun y z => A y z \/ A x y) B)]; simpl. unfold sec_disj.
    intuition auto.
    eapply SecureBy_mon; [|eapply H1]; simpl. intros. intuition auto.
    simpl. intros.
    eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto.
  - simpl. specialize (H0 x (SUP w) (w0 x)). simplify_IH_hyps.
    eapply SecureBy_mon; [|eapply (H0 A (fun y z => B y z \/ B x y))]; simpl. intuition auto.
    intuition. simpl in H2. apply H2.
Defined.

Definition inter_rel {X : Type} (A B : X -> X -> Prop) := fun x y => A x y /\ B x y.

Corollary af_interesection {X : Type} (A B : X -> X -> Prop) :
  AlmostFull A -> AlmostFull B -> AlmostFull (inter_rel A B).
Proof.
  intros [pa Ha] [pb Hb]. exists (oplus_binary pa pb). now apply oplus_binary_sec_intersection.
Defined.


(* Non-functional construction in intuition auto! *)
(* Lemma oplus_unary_sec_intersection' {X} (p q : WFT X) *)
(*       (C : X -> X -> Prop) (A B : X -> Prop) : *)
(*   SecureBy (fun y z => C y z \/ A y) p -> *)
(*   SecureBy (fun y z => C y z \/ B y) q -> *)
(*   SecureBy (fun y z => C y z \/ (A y /\ B y)) (oplus_unary p q). *)
(* Proof. *)
(*   revert p q C; intros p q. funelim (oplus_unary p q); simpl; intros. *)
(*   eapply SecureBy_mon. 2:eapply H0. simpl. firstorder. *)
(*   eapply SecureBy_mon; [|eapply H]. simpl; firstorder. *)
(*   eapply SecureBy_mon. 2:eapply (oplus_nullary_sec_intersection _ _ _ (A x) (B x)). simpl. *)
(*   intros. destruct H3; [|intuition auto]. rewrite <- or_assoc. left. eapply H3. *)
(*   - simpl. *)
(*     eapply SecureBy_mon; [|eapply (H _ (fun y z => C y z \/ C x y \/ A x))]. simpl. *)
(*     clear H H0. (* BUG *) intuition auto. *)
(*     eapply SecureBy_mon; [|eapply H1]; simpl. intros. intuition auto. *)
(*     simpl. intros. *)
(*     eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto. *)
(*   - simpl. eapply SecureBy_mon; [|eapply (H0 _ (fun y z => C y z \/ C x y \/ B x))]; simpl. intuition auto. *)
(*     intuition. simpl in H2. eapply SecureBy_mon; [|eapply H1]; simpl. intuition auto. *)
(*     eapply SecureBy_mon; [|eapply H2]; simpl. intros. intuition auto. *)
(* Qed. *)

Definition af_bool : AlmostFull (@eq bool).
Proof.
  exists (SUP (fun _ => SUP (fun _ => ZT))).
  simpl. intros x y z w. destruct x, y, z, w; intuition.
Defined.

Definition product_rel {X Y : Type} (A : X -> X -> Prop) (B : Y -> Y -> Prop) :=
  fun x y => A (fst x) (fst y) /\ B (snd x) (snd y).

Instance af_product {X Y : Type} (A : X -> X -> Prop) (B : Y -> Y -> Prop) :
  AlmostFull A -> AlmostFull B -> AlmostFull (product_rel A B).
Proof.
  intros. pose (af_interesection (MR A fst) (MR B snd)).
  assert (relation_equivalence (inter_rel (MR A fst) (MR B snd)) (product_rel A B)).
  repeat red; intuition. rewrite <- H1. apply a; typeclasses eauto.
Defined.

Definition T (x y : nat * nat) : Prop :=
  (fst x = snd y /\ snd x < snd y) \/
  (fst x = snd y /\ snd x < fst y).

Definition T' (x y : nat * nat) : Prop :=
  (fst x <= snd y /\ snd x <= snd y) \/
  (fst x <= snd y /\ snd x <= fst y).

Definition R := product_rel le le.
Require Import Lia.

Ltac destruct_pairs := repeat
  match goal with
    [ x : _ * _ |- _ ] => let x0 := fresh x in let x1 := fresh x in destruct x as [x0 x1]; simpl in *
  | [ x : exists _ : _, _ |- _ ] => destruct x
  | [ x : _ /\ _ |- _ ] => destruct x
end.

Derive Signature for clos_trans_1n.
(* Lemma clos_tra_prop n1 n2 n3 n4 : n1 <= n4 -> clos_trans_1n _ T (n3, n4) (n1, n2) -> n1 <= n3. *)

Lemma power_T_prop y z : (power 1 T) y z -> ((* (fst y) <= (fst z) /\ *) (snd y) < (snd z)) \/
                                                     (* (fst y) <= (fst z) /\ *) (snd y) < (fst z).
Proof.
  unfold T, T'; intros H. destruct H. destruct_pairs. repeat red in H; simpl in *; subst; auto; simp power in *;
    destruct_pairs. intuition.
Qed.

Definition power_T_inv (y z : nat * nat) :=
  ((fst y) < (snd z) /\ (snd y) < (snd z) \/ (fst y) < (fst z)). (* \/ (snd y < fst z)). *)

Lemma power_T_prop2 y z : (power 1 T) y z -> power_T_inv y z.
Proof.
  unfold power_T_inv, T, T'; intros H. destruct H. destruct_pairs. repeat red in H; simpl in *; subst; auto; simp power in *;
    destruct_pairs. intuition.
Qed.

Lemma clos_trans_incl {X} (R S : X -> X -> Prop) : inclusion _ R S ->
                                                   inclusion _ (clos_trans _ R) (clos_trans _ S).
Proof.
  intros H x y Hxy. induction Hxy; auto. constructor. auto. econstructor 2; eauto.
Qed.

Lemma power_T_clos_prop : inclusion _ (clos_trans _ (power 1 T)) (clos_trans _ power_T_inv).
Proof.
  apply clos_trans_incl. red. intros. now apply power_T_prop2.
Qed.


(* Lemma power_T_prop3 y z : (power 1 T) y z -> (snd y) <= (snd z). *)
(* Proof. *)
(*   unfold T, T'; intros H. destruct H. destruct_pairs. repeat red in H; simpl in *; subst; auto; simp power in *; *)
(*     destruct_pairs. intuition. subst. *)
(* Qed. *)

(* Lemma power_T_all_prop y z : (power 1 T) y z -> ((fst y) <= (snd z) /\ (snd y) <= (snd z)) \/ *)
(*                                               (fst y) <= (fst z) /\ (snd y) <= (fst z). *)
(* Proof. *)
(*   unfold T, T'; intros H. destruct_pairs. *)
(*   pose proof (power_T_prop _ _ H). *)
(*   pose proof (power_T_prop2 _ _ H). *)
(*   destruct_pairs. simpl in *. intuition. destruct H. destruct_pairs; intuition. subst. *)
(* Qed. *)


(* Lemma clos_trans_power_T_prop y z : clos_trans_1n _ (power 1 T) y z -> *)
(*  ((* (fst y) <= (fst z) /\ *) (snd y) <= (snd z)) \/ *)
(*  (* (fst y) <= (fst z) /\ *) (snd y) <= (fst z). *)
(* Proof. *)
(*   unfold T, T'; intros H. induction H. destruct_pairs. repeat red in H; simpl in *; subst; auto; simp power in *; *)
(*     destruct_pairs. intuition. apply power_T_prop in H. intuition. *)
(* Qed. *)

(* subst. *)
(*   repeat red in H. subst. *)
(*    destruct_pairs. simpl in *. intuition. subst. *)
(*    repeat red in H0. simpl in *; intuition. *)
(*    destruct_pairs. simpl in *. intuition. subst. *)
(*    repeat red in H1. simpl in *; intuition. *)

Lemma T_tra_prop y z : T y z -> product_rel le le z y -> False.
Proof.
  intros. unfold power_T_inv, T in *. destruct_pairs. red in H0. simpl in *. intuition.
Qed.

Lemma clos_tra_prop y z : (power 1 T) y z -> product_rel le le z y -> False.
Proof.
  intros. apply power_T_prop2 in H. unfold power_T_inv in *. destruct_pairs. red in H0. simpl in *. intuition.
Qed.

Lemma power_T_prop3 y z : T y z -> ((snd y) < (snd z) \/ (snd y) < (fst z)).
(* ((fst y) <= (snd z) /\ (snd y) <= (snd z)) \/ *)
(*                                    ((fst y) <= (snd z) /\ (snd y) <= (fst z)). *)
Proof.
  unfold T, T'; intros H. destruct_pairs. repeat red in H; simpl in *; subst; auto; simp power in *;
    destruct_pairs. intuition.
Qed.

Lemma power_T_prop4 y z : T y z -> (fst y <= snd z).
Proof.
  unfold T, T'; intros H. destruct_pairs. repeat red in H; simpl in *; subst; auto; simp power in *;
    destruct_pairs. intuition.
Qed.

Lemma power_1_T_enough n y z : power n T y z ->
                               (* ((fst y) <= (snd z) /\ (snd y) <= (snd z)) \/ *)
                               (* ((fst y) <= (snd z) /\ (snd y) <= (fst z)). *)
                               ((snd y) < (snd z) \/ (snd y) < (fst z)).
Proof.
  induction n in y, z |- *. apply power_T_prop3. auto. intros.
  simp power in *. destruct_pairs; unfold T in *. simpl in *.
  specialize (IHn _ _ H). destruct IHn. simpl in *. intuition. simpl in *. intuition.
Qed.


(* Lemma power_T_prop4_2 n y z : power n T y z -> (fst y <= snd z). *)
(* Proof. *)
(*   induction n in y, z |- *. apply power_T_prop4. auto. intros. *)
(*   simp power in *. destruct_pairs; unfold T in *. simpl in *. *)
(*   specialize (IHn _ _ H). *)
(*   apply power_1_T_enough in H. simpl in *. intuition. subst. *)
(*  destruct IHn. simpl in *. *)


(*  intuition. simpl in *. intuition. *)
(* Qed. *)

Lemma power_1_T_enough' n y z : power n T y z -> product_rel le le z y -> False.
Proof.
  induction n in y, z |- *. apply T_tra_prop. auto. intros.
  simp power in *. destruct_pairs; unfold T in *. simpl in *.
  specialize (IHn _ _ H). destruct IHn.
  red. red in H0. simpl in *. intuition. subst.
  apply power_1_T_enough in H. simpl in *. intuition. subst.
  apply power_1_T_enough in H. simpl in *. intuition. subst.
  apply power_1_T_enough in H. simpl in *. intuition. subst.



intros. inversion H.
  destruct n. intros; firstorder.
  intros. forward IHn. lia.
  intros x y Rxy. simp power in *. destruct_pairs. unfold T in *. simpl in *.
  exists (y1 , x0). simpl. intuition. subst.

Definition Tle (x y : nat * nat) : Prop :=
  (fst x <= snd y /\ snd x < snd y) \/
  (fst x <= snd y /\ snd x < fst y).
Lemma Tle_tra_prop y z : Tle y z -> product_rel le le z y -> False.
Proof.
  intros. unfold power_T_inv, Tle in *. destruct_pairs. red in H0. simpl in *. intuition.
Qed.

Lemma T_product_right x y z : Tle x y -> product_rel le le y z -> Tle x z.
Proof.
  intros. destruct H; unfold Tle in *; destruct_pairs; red in H0; simpl in *;
  intuition.
Qed.

Lemma clos_tra_prop_n n y z : (power n Tle) y z -> product_rel le le z y -> False.
Proof.
  induction n in y, z |- *; simp power. apply Tle_tra_prop.
  intros [z' [Tpz Tz]]. specialize (IHn _ _ Tpz).
  intros. apply IHn. clear IHn. clear Tpz.
  apply (T_product_right _ _ _ Tz) in H.
  red in H.

unfold product_rel, T in *. destruct_pairs.
  simpl in *. intuition. subst.
  intros. apply power_T_prop2 in H. unfold power_T_inv in *. destruct_pairs. red in H0. simpl in *. intuition.
Qed.

Lemma power_T_inv_prop y z : power_T_inv y z -> product_rel le le z y -> False.
Proof.
  intros. unfold power_T_inv in *. destruct_pairs. red in H0. simpl in *. intuition.
Qed.

Definition power_T_inv2 (y z : nat * nat) :=
  ((fst y) < (snd z) /\ (snd y) < (snd z)
                        \/ (fst y) < (fst z) /\ (snd y <= fst z)).

Lemma clos_power_T_inv_prop y z : clos_trans_1n _ power_T_inv2 y z -> power_T_inv2 y z.
Proof.
  intros. unfold power_T_inv2 in *. induction H. auto.
  destruct_pairs. simpl in *. intuition.
Qed.

Lemma power_T_inv2_powerT_inv : inclusion _ (power 2 T) power_T_inv2.
Proof. intros x y H. unfold power_T_inv2, power_T_inv in *. simp power in *. unfold T in *.
       destruct_pairs. intuition. subst. Qed.

Lemma clos_tra_prop_clos y z : clos_trans_n1 _ (power 1 T) y z -> product_rel le le z y -> False.
Proof.
  intros.
  rewrite <- clos_trans_tn1_iff in H.
  apply power_T_clos_prop in H.

  eapply clos_trans_incl in H.
  rewrite clos_trans_t1n_iff in H.
  eapply clos_power_T_inv_prop in H. admit. intros  ? ?.

 induction H in|- *. eapply clos_tra_prop; eauto.
  pose (clos_tra_prop' _ _ _ H H0). pose (power_T_product_right _ _ _ H H0).
  eapply (clos_trans_inter_false (power 1 T)). 2:eapply H1. 2:constructor; eapply p.
  intros.
  intuition.
Qed.




Lemma clos_tra_prop' x y z : (power 1 T) x y -> product_rel le le y z -> product_rel le le z x -> False.
Proof.
  intros. simp power in H. unfold T in *. repeat red in H0, H1. repeat red. destruct_pairs.
  intuition.
Qed.

Lemma power_T_product_right x y z : (power 1 T) x y -> product_rel le le y z -> (power 1 T) x z.
Proof.
  intros. destruct H. unfold T in *; destruct_pairs. red in H0. simp power. simpl in *.
  intuition. subst. exists (z1, x2). simpl. intuition. subst.
  exists (z1, x2); simpl; intuition.
  exists (z1, x0); simpl; intuition.
  exists (z1, x0); simpl; intuition.
Qed.

(* Lemma T_product_right' x y z : T x y -> product_rel le le y z -> product_rel le le x z. *)
(* Proof. *)
(*   intros. destruct H; unfold Tle in *; destruct_pairs; red in H0 |- *; simpl in *; *)
(*   intuition. subst. *)
(* Qed. *)

(* Lemma power_T_product_left x y z : (power 1 T) y z -> product_rel le le x y -> (power 1 T) x z. *)
(* Proof. *)
(*   intros. destruct H. unfold T in *; destruct_pairs. red in H0. simp power. simpl in *. *)
(*   intuition. subst. exists (z1, x0). simpl. intuition. subst. *)
(*   exists (z1, x0); simpl; intuition. *)
(*   exists (z1, x0); simpl; intuition. *)
(*   exists (z1, x0); simpl; intuition. *)
(* Qed. *)

  (* ~(x <= y /\ z <= w)
     <-> (~ x <= y \/ ~ (z <= w))
     <-> (y < x \/ w < z) *)

Definition antisym {X} (R : X -> X -> Prop) :=
  forall x y, R x y -> R y x -> False.

Lemma power_1_antisym : antisym (power 1 T).
Proof.
  intros x y. intros [] []. unfold T in *. destruct_pairs. simpl in *. intuition.
Qed.

(* Lemma clos_trans_antisym {X} (R : X -> X -> Prop) : antisym R -> antisym (clos_trans _ R). *)
(* Proof. *)
(*   intros. *)
(*   intros x y. rewrite !clos_trans_tn1_iff. induction 1. induction 1. *)
(*   eauto. *)
(* Qed. *)

Lemma clos_trans_inter_false {A} (R : A -> A -> Prop) : (* transitive _ R -> *)
  (forall x y, R x y -> clos_trans_n1 _ R y x -> False) ->
  (forall x y, clos_trans_n1 _ R x y -> clos_trans_n1 _ R y x -> False).
Proof.
  intros. induction H0; eauto. specialize (H y z). specialize (H H0).
  apply H. apply clos_trans_tn1. econstructor 2. apply clos_trans_tn1_iff. eauto.
  apply clos_trans_tn1_iff. eauto.
Defined.

Lemma clos_trans_inter_false' {A} (R : A -> A -> Prop) : (* transitive _ R -> *)
  (forall x y, R x y -> clos_trans_n1 _ R y x -> False) ->
  (forall x y, clos_trans_n1 _ R x y -> R y x -> False).
Proof.
  intros.
  pose (tn1_step _ _ _ _ H1).
  eapply clos_trans_inter_false. 2:eapply H0. 2:eauto.
  intros. eauto.
Qed.


Lemma clos_tra_prop_clos y z : clos_trans_n1 _ T y z -> product_rel le le z y -> False.
Proof.
  intros. unfold product_rel in *.
  induction H. unfold T in *. destruct_pairs. repeat red in H0. simpl in *. intuition.
  unfold T in *. destruct_pairs. repeat red in H0. simpl in *. intuition.
  subst. apply H3; intuition.
  destruct H2.
  unfold T in *. destruct_pairs. repeat red in H0. simpl in *. intuition.
  unfold T in *. destruct_pairs. repeat red in H0. simpl in *. intuition. subst.






  rewrite <- clos_trans_tn1_iff in H.
  apply power_T_clos_prop in H.
  unfold power_T_inv in H. unfold product_rel in *.
  rewrite clos_trans_tn1_iff in H.
  induction H; repeat red in H0; destruct_pairs. intuition.
  intuition.

Lemma clos_tra_prop_clos y z : clos_trans_n1 _ (power 1 T) y z -> product_rel le le z y -> False.
Proof.
  intros.
  rewrite <- clos_trans_tn1_iff in H.
  apply power_T_clos_prop in H.
  unfold power_T_inv in H. unfold product_rel in *.
  rewrite clos_trans_tn1_iff in H.
  induction H; repeat red in H0; destruct_pairs. intuition.
  intuition.




Lemma clos_tra_prop_clos y z : clos_trans_n1 _ (power 1 T) y z -> product_rel le le z y -> False.
Proof.
  intros. induction H in|- *. eapply clos_tra_prop; eauto.
  pose (clos_tra_prop' _ _ _ H H0). pose (power_T_product_right _ _ _ H H0).
  eapply (clos_trans_inter_false (power 1 T)). 2:eapply H1. 2:constructor; eapply p.
  intros.
  intuition.
Qed.

Definition gnlex : (nat * nat) -> nat.
  pose (af_power_wf T R 1).
  forward w. unfold R. intros [] [] [Ht Hr].
  eapply clos_tra_prop_clos; eauto. now apply clos_trans_1n_n1.
  refine (Subterm.FixWf (R:=T) (fun x => nat) _).
  refine (fun x =>
            match x as w return ((forall y, T y w -> nat) -> nat) with
              | (0, _) => fun _ => 1
              | (_, 0) => fun _ => 1
              | (S x, S y) => fun frec =>
                                frec (S y, y) _ +
                                frec (S y, x) _
            end).
  red. simpl. intuition lia. red. simpl. intuition lia.
Defined.

Require Import ExtrOcamlBasic.
Extraction gnlex.

Lemma gnlex_0_l y : gnlex (0, y) = 1.
Admitted.

Lemma gnlex_0_r x : gnlex (x, 0) = 1.
Admitted.


Lemma gnlex_S x y : gnlex (S x, S y) = gnlex (S y, y) + gnlex (S y, x).
Admitted.

Lemma gnlex_S_test x y : exists foo, gnlex (S x, S y) = foo.
  eexists. rewrite gnlex_S. destruct y. rewrite gnlex_0_r. destruct x. rewrite gnlex_0_r. reflexivity.
  rewrite gnlex_S. rewrite gnlex_0_r. destruct x. admit. rewrite gnlex_S.
Admitted.

Eval vm_compute in fun x y => gnlex (S x, S y).