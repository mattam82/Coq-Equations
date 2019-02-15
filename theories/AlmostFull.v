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
    intros. intro x. eapply acc_from_af; eauto.
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

Equations T (x y : nat * nat) : Prop :=
  T (x0, x1) (y0, y1) := (x0 = y1 /\ x1 < y1) \/
                         (x0 = y1 /\ x1 < y0).

Definition R := product_rel le le.
Require Import Lia.
Axiom cheat : forall A, A.
Definition gnlex : (nat * nat) -> nat.
  pose (af_wf T R).
  forward w.
  unfold T.
  destruct 1. induction H. simpl in H.
  destruct x as [x0 y0]. destruct y as [x1 y1]. simpl in H0.
  repeat red in H0. simpl in H0. intuition.
  destruct x as [x0 y0]. destruct y as [x1 y1].
  destruct z as [z0 z1]. simpl in *.
  repeat red in H0. simpl in H0; intuition.
  unfold R, product_rel in *. simpl in *.
  apply cheat. apply cheat.

  refine (Subterm.FixWf (R:=T) (fun x => nat) _).
  refine (fun x =>
            match x as w return ((forall y, T y w -> nat) -> nat) with
              | (0, _) => fun _ => 1
              | (_, 0) => fun _ => 1
              | (S x, S y) => fun frec =>
                                frec (S y, y) _ +
                                frec (S y, x) _
            end).
  red. intuition lia. red. intuition lia.
Defined.

Require Import ExtrOcamlBasic.
Extraction gnlex.