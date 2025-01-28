From Equations.Prop Require Import Equations.

From Stdlib Require Import Vector.
Notation vector := t.
Derive NoConfusion NoConfusionHom for vector.

Set Equations Transparent.

Arguments Vector.nil {A}.
Arguments Vector.cons {A} _ {n}.

Notation " x |:| y " := (@Vector.cons _ x _ y) (at level 20, right associativity) : vect_scope.
Notation " x |: n :| y " := (@Vector.cons _ x n y) (at level 20, right associativity) : vect_scope.
Notation "[]v" := Vector.nil (at level 0) : vect_scope.
Local Open Scope vect_scope.

Equations app {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  app []v w := w ;
  app (cons a v) w := a |:| app v w.

Equations In {A n} (x : A) (v : vector A n) : Prop :=
  In x nil := False;
  In x (cons a v) := (x = a) \/ In x v.

Inductive All {A : Type} (P : A -> Prop) : forall {n}, vector A n -> Prop :=
| All_nil : All P nil
| All_cons {a n} {v : vector A n} : P a -> All P v -> All P (a |:| v).

Lemma All_impl {A : Type} (P Q : A -> Prop) {n} (v : vector A n) : (forall x, P x -> Q x) -> All P v -> All Q v.
Proof. induction 2; constructor; auto. Qed.

Derive Signature for All.
Lemma All_app {A P n m} (v : vector A n) (w : vector A m) :
  @All A P _ v -> All P w -> All P (app v w).
Proof.
  funelim (app v w). auto.
  intros. depelim H0; simp app in *. econstructor; auto.
Qed.

Lemma In_All {A P n} (v : vector A n) : All P v <-> (forall x, In x v -> P x).
Proof.
  split. induction 1. intros. depelim H. auto. intros x; simpl. simp In. intuition. subst; auto.
  induction v; simpl; intros; auto; constructor. apply H; simp In; auto.
  firstorder.
Qed.

Lemma All_In_All {A P n m} (v : vector A n) (v' : vector A m) :
   All (fun x => In x v) v' -> All P v -> All P v'.
Proof.
  induction 1. simpl. constructor.
  intros. constructor; auto.
  eapply In_All; eauto.
Qed.

Inductive Sorted {A : Type} (R : A -> A -> Prop) : forall {n}, vector A n -> Prop :=
| Sorted_nil : Sorted R nil
| Sorted_cons {a n} {v : vector A n} : All (R a) v -> Sorted R v -> Sorted R (a |:| v).
Import Sigma_Notations.
Derive Signature for Sorted.

Lemma Sorted_app {A R n m} (v : vector A n) (w : vector A m) :
  @Sorted A R _ v -> Sorted R w ->
  Sorted R (app v w).
Proof.
Admitted.

Lemma In_app {A n m} (v : vector A n) (w : vector A m) (a : A) : In a v \/ In a w <-> In a (app v w).
Proof.
  funelim (app v w). intuition. depelim H0.
  split; intros; depelim H0; cbn; simp In app in *; intuition eauto with *; simp In in *.
  apply H in H0. intuition.
Qed.
From Stdlib Require Import Sumbool.

Notation dec x := (sumbool_of_bool x).

Section QuickSort.
  Context {A : Type} (leb : A -> A -> bool).
  Context (leb_inverse : forall x y, leb x y = false -> leb y x = true).
  Local Definition sorted {n} (v : vector A n) := Sorted (fun x y => leb x y = true) v.
  Set Program Mode.

  Equations? filter {n} (v : vector A n) (f : A -> bool) :
    Σ (k : nat), { v : vector A k | k <= n /\ All (fun x => f x = true) v } :=
    filter nil        f := (0, nil);
    filter (cons a v') f with dec (f a) :=
           { | left H => (_, cons a (filter v' f).2);
             | right H => (_, (filter v' f).2) }.
  Proof.
    split; auto. constructor.
    destruct filter as [n' [v'' [Hn' Hv']]]. simpl.
    split; auto with arith. constructor; auto.
    destruct filter as [n' [v'' [Hn' Hv']]]. simpl.
    split; auto with arith.
  Defined.

  Equations? pivot {n} (v : vector A n) (f : A -> bool) :
    Σ (k : nat) (l : nat) (v' : vector A k), { w : vector A l
    | (k + l = n)%nat
      /\ forall x, In x v <->
                   (if f x then In x v'
                    else In x w) } :=
                   (*   All (fun x => In x v /\ f x = true) v' *)
                   (* /\ All (fun x => In x v /\ f x = false) w } } } } := *)
    pivot nil        f := (0 , 0 , nil, nil);
    pivot (cons a v') f with dec (f a), pivot v' f :=
           { | left H | (k, l, v, w) => (_ , _, cons a v, w);
             | right H | (k, l, v, w) => (_ , _, v, cons a w) }.
  Proof.
    split; intros; simp In; auto. intuition. destruct (f x); auto. simpl.
    split; auto with arith. intros x. simp In. split; intros Hx.
    intuition; subst; try rewrite H; intuition. specialize (proj1 (i _) H0). destruct (f x); intuition.
    specialize (i x). destruct (f x); intuition.
    split; auto with arith. intros x. constructor; simp In; intuition auto.
    subst. rewrite H. auto. specialize (proj1 (i _) H1). destruct (f x); intuition.
    specialize (i x). destruct (f x); intuition.
  Defined.

  Equations? qs {n} (l : vector A n) : { v : vector A n | sorted v /\ (forall x, In x l <-> In x v) } by wf n lt :=
    qs nil := nil ;
    qs (cons a v) with pivot v (fun x => leb x a) :=
                { | (k, l, lower, higher) =>
                    app (qs lower) (a |:| qs higher) }.
  Proof.
    all:simpl. all:repeat (destruct qs; simpl).
    repeat constructor; trivial. auto with arith. auto with arith.
    simpl. destruct (eq_sym (plus_n_Sm k l)). simpl.
    intuition.
    apply Sorted_app; auto. constructor.
    apply In_All. intros x1 Inx1. apply H2 in Inx1.
    specialize (i x1).
    eapply leb_inverse.

    eapply All_In_All; eauto. eapply All_impl; eauto. simpl. intros x1 [inx1 lebx1].
    apply leb_inverse; assumption. intuition.
    eapply All_app. eapply All_In_All; eauto. eapply All_impl; eauto. simpl.
    intros x1 [inx1 lebx1]. constructor; auto.
    constructor; auto. constructor.
    eapply All_In_All; eauto.
    eapply All_impl; eauto. simpl. intros x1 [Inx1 lebx1]. constructor; auto.
  Defined.

  Definition qs_forget {n} (l : vector A n) : vector A n := qs l.

  (* Proof after the definition. *)

  Lemma All_In {n} (v : vector A n) P : All P v -> (forall x, In x v -> P x).
  Proof. induction 1. intros x Hx. depelim Hx. intros x Hx. depelim Hx. auto. auto. Qed.

  Lemma All_In_self {n} (v : vector A n) : All (fun x => In x v) v.
  Proof.
    induction v. constructor. constructor. constructor. eapply All_impl; eauto. simpl.
    intros. constructor; auto.
  Qed.

  Local Open Scope program_scope.

  Local Open Scope program_scope.
  Lemma qs_all {n} (l : vector A n) : forall x, In x (qs_forget l) -> In x l.
  Proof.
    intros x. unfold qs_forget. destruct (qs l). simpl; eauto. destruct a.
    eapply (All_In _ _ H0).
  Qed.

  Lemma all_qs {n} (l : vector A n) : forall x, In x l -> In x (qs_forget l).
  Proof.
    intros x. unfold qs_forget. funelim (qs l); simpl.
    + trivial.
    + destruct qs_obligation_4. simpl.
      clear H1.
      intros Hx. eapply In_app. destruct Hx.
      destruct pr6. simpl in *. destruct a. destruct a. simpl in *.

      constructor. clear Heq. eapply All_In in a. intuition eauto. auto.
      clear Heq; intuition; destruct pr6; intuition; simpl in *.
      depelim H1. constructor. constructor. simpl in H1. apply H0 in H1.
      intuition. eapply All_In in H5. intuition eauto. auto.
  Qed.
  Lemma qs_all {n} (l : vector A n) : forall x, In x (qs_forget l) -> In x l.
  Proof.
    intros x. unfold qs_forget. funelim (qs l); simpl.
    + trivial.
    + destruct qs_obligation_4. simpl.
      clear H1.
      intros Hx. apply In_app in Hx. destruct Hx. apply H in H1.
      destruct pr6. simpl in *. destruct a. destruct a. simpl in *.
      constructor. clear Heq. eapply All_In in a. intuition eauto. auto.
      clear Heq; intuition; destruct pr6; intuition; simpl in *.
      depelim H1. constructor. constructor. simpl in H1. apply H0 in H1.
      intuition. eapply All_In in H5. intuition eauto. auto.
  Qed.

  Lemma qs_equiv {n} (l : vector A n) : forall x, In x l <-> In x (qs_forget l).
  Proof.
    split; auto using qs_all. intros.
    unfold qs_forget. funelim (destruct qs. simpl. intuition.
    eapply (All_In in H1.
    pose (All_In_self x0). eapply All_In_All in a; eauto.


End QuickSort.

Extraction Inline pivot.
Extraction qs.
