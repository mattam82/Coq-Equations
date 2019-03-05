Require Import Equations.Equations.
Require Import Equations.Below.
Module NoCycle_nat.

Definition noSubterm x y :=
  Below_nat (fun y => x <> y) y.

Definition noLargeSubterm x y :=
  ((x <> y) * noSubterm x y)%type.

Lemma step_S x b : noSubterm x b -> noLargeSubterm (S x) b.
Proof.
  induction b; intros H.
  (* Non-recursive case. *)
  - split.
    (* Disjointness of constructors. *)
    + intros H'; noconf H'.
    (* No subterm in a non-recursive constructor. *)
    + simpl. exact tt.
  (* Recursive case. *)
  - split.
    (* Injectivity of constructors. *)
    + intros H'; noconf H'.
      apply (fst H); reflexivity.
    + apply (IHb (snd H)).
Qed.

Definition no_cycle x y : x = y -> noSubterm x y.
Proof.
  intros ->.
  induction y.

  (* Non-recursive case. *)
  - exact tt.
  (* Recursive case. *)
  - apply step_S; apply IHy.
Qed.

End NoCycle_nat.

Module NoCycle_ord.

  Inductive O : Set :=
    | zero | succ : O -> O | lim : (nat -> O) -> O.
  Derive Below for O.
  Derive NoConfusion for O.

  Definition noSubterm x y :=
    Below_O (fun y => x <> y) y.

  Definition noLargeSubterm x y :=
    ((x <> y) * noSubterm x y)%type.

  Lemma step_succ x b : noSubterm x b -> noLargeSubterm (succ x) b.
  Proof.
    induction b; intros H.
    (* Non-recursive case. *)
    - split.
      (* Disjointness of constructors. *)
      + intros H'; noconf H'.
      (* No subterm in a non-recursive constructor. *)
      + exact tt.
    (* Recursive and interesting case. *)
    - split.
      (* Injectivity of constructors. *)
      + intros H'; noconf H'.
        apply (fst H); reflexivity.
      + apply (IHb (snd H)).
    (* Recursive and non-interesting case. *)
    - split.
      (* Disjointness of constructors. *)
      + intros H'; noconf H'.
      (* No subterm in a non-recursive constructor. *)
      + intros x'. apply (X _ (snd (H _))).
  Qed.

  Lemma step_lim f b : forall x, noSubterm (f x) b -> noLargeSubterm (lim f) b.
  Proof.
    induction b; intros x H.
    (* Non-recursive case. *)
    - split.
      (* Disjointness of constructors. *)
      + intros H'; noconf H'.
      (* No subterm in a non-recursive constructor. *)
      + exact tt.
    (* Recursive and non-interesting case. *)
    - split.
      (* Disjointness of constructors. *)
      + intros H'; noconf H'.
      + apply (IHb _ (snd H)).
    (* Recursive and interesting case. *)
    - split.
      (* Injectivity of constructors. *)
      + intros H'; noconf H'.
        apply (fst (H x)); reflexivity.
      (* No subterm in a non-recursive constructor. *)
      + intros x'. apply (X _ _ (snd (H _))).
  Qed.
  
  Definition no_cycle x y : x = y -> noSubterm x y.
  Proof.
    intros ->.
    induction y.
    (* Non-recursive case. *)
    - exact tt.
    (* Recursive case. *)
    - apply step_succ; apply IHy.
    (* Recursive case. *)
    - intros x. apply step_lim with (x := x). apply X.
  Qed.
End NoCycle_ord.

Module NoCycle_tree.

  Inductive t :=
  | L | N (x y : t).
  Derive Below for t.
  Derive NoConfusion for t.

  Definition noSubterm x y :=
    Below_t (fun y => x <> y) y.

  Definition noLargeSubterm x y :=
    ((x <> y) * noSubterm x y)%type.

  Lemma step_N1 x y b : noSubterm x b -> noLargeSubterm (N x y) b.
  Proof.
    induction b; intros H.
    - split.
      + intros H'; noconf H'.
      + constructor.
    - split.
      + intros H'; noconf H'.
        apply (fst (snd H)); reflexivity.
      + split.
        * apply (IHb2 (snd (fst H))).
        * apply (IHb1 (snd (snd H))).
  Qed.

  Lemma step_N2 x y b : noSubterm y b -> noLargeSubterm (N x y) b.
  Proof.
    induction b; intros H.
    - split.
      + intros H'; noconf H'.
      + constructor.
    - split.
      + intros H'; noconf H'.
        apply (fst (fst H)); reflexivity.
      + split.
        * apply (IHb2 (snd (fst H))).
        * apply (IHb1 (snd (snd H))).
  Qed.

  Definition no_cycle x y : x = y -> noSubterm x y.
  Proof.
    intros ->.
    induction y.
    - constructor.
    - split.
      + apply step_N2. apply IHy2.
      + apply step_N1. apply IHy1.
  Qed.
End NoCycle_tree.

Module NoCycle_mut.

  Inductive T :=
  | L | N (x : R)
  with R :=
  | rnil | rcons : T -> R -> R.

  Section below.
    Variables (P : T -> Type) (Q : R -> Type).

    Fixpoint Below_T (t : T) : Type :=
      match t with
      | L => True
      | N x => Q x * Below_R x
      end
    with Below_R (r : R) : Type :=
      match r with
      | rnil => True
      | rcons t r => (P t * Below_T t) * (Q r * Below_R r)
      end.

    Variables (Ht : forall t', Below_T t' -> P t')
              (Hr : forall r', Below_R r' -> Q r').

    Lemma below_t : forall t, Below_T t
    with below_r : forall r, Below_R r.
    Proof.
      intros [|x].
      exact I.
      exact (Hr x (below_r x), below_r x).
      intros [|t rs].
      exact I.
      exact ((Ht t (below_t t), below_t t), (Hr rs (below_r rs), below_r rs)).
    Defined.
  End below.

  Derive NoConfusion for T R.

  Definition noSubterm_T x y :=
    Below_T (fun y => x <> y) (fun _ => True) y.

  Definition noSubterm_RT x y :=
    Below_T (fun _ => True) (fun y => x <> y) y.

  Definition noLargeSubterm_T x y :=
    ((x <> y) * noSubterm_T x y)%type.

  Definition noSubterm_R x y :=
    Below_R (fun _ => True) (fun y => x <> y) y.

  Definition noSubterm_TR x y :=
    Below_R (fun y => x <> y) (fun _ => True) y.

  Definition noLargeSubterm_R x y :=
    ((x <> y) * noSubterm_R x y)%type.

  Lemma step_N b : forall r, noSubterm_R r b -> noSubterm_TR (N r) b
  with  step_rcons1 b : forall t r, noSubterm_T t b -> noSubterm_RT (rcons t r) b
  with  step_rcons2 b : forall t r, noSubterm_R r b -> noLargeSubterm_R (rcons t r) b
  with  step_aux1 b : forall r, noSubterm_RT r b -> noLargeSubterm_T (N r) b
  with  step_aux2 b : forall t r, noSubterm_TR t b -> noLargeSubterm_R (rcons t r) b
  with  step_aux3 b : forall t r, noSubterm_RT r b -> noSubterm_RT (rcons t r) b.
  Proof.
    * destruct b; intros r H.
      - exact I.
      - split.
        + apply step_aux1. apply H.
        + refine (I, _).
          change (noSubterm_TR (N r) b).
          apply step_N. apply H.
    * destruct b; intros t r H.
      - exact I.
      - apply step_aux2. apply H.
    * destruct b; intros ? r H.
      - split.
        + intros H'; noconf H'.
        + exact I.
      - split.
        + intros H'; noconf H'.
          apply H; reflexivity.
        + split.
          -- refine (I, _).
             change (noSubterm_RT (rcons t0 r) t).
             apply step_aux3. apply H.
          -- apply step_rcons2. apply H.
    * destruct b; intros r H.
      - split.
        + intros H'; noconf H'.
        + exact I.
      - split.
        + intros H'; noconf H'.
          apply H; reflexivity.
        + refine (I, _).
          change (noSubterm_TR (N r) x).
          apply step_N. apply H.
    * destruct b; intros ? r H.
      - split.
        + intros H'; noconf H'.
        + exact I.
      - split.
        + intros H'; noconf H'.
          apply H; reflexivity.
        + split.
          -- refine (I, _).
             change (noSubterm_RT (rcons t0 r) t).
             apply step_rcons1. apply H.
          -- apply step_aux2. apply H.
    * destruct b; intros t r H.
      - exact I.
      - apply step_rcons2. apply H.
  Qed.

  Lemma noCycle_T x y : x = y -> noSubterm_T x y
  with  noCycle_R x y : x = y -> noSubterm_R x y.
  Proof.
    * intros ->. destruct y.
      - exact I.
      - refine (I, _).
        change (noSubterm_TR (N x) x).
        apply step_N. apply noCycle_R. reflexivity.
    * intros ->. destruct y.
      - exact I.
      - split.
        + refine (I, _).
          change (noSubterm_RT (rcons t y) t).
          apply step_rcons1. apply noCycle_T. reflexivity.
        + apply step_rcons2. apply noCycle_R. reflexivity.
  Qed.
End NoCycle_mut.

Require Import Eqdep_dec.

Theorem nat_dec (n m : nat) : {n = m} + {n <> m}.
Proof. decide equality. Defined.

Module DecidableType_nat <: DecidableType.
  Definition U := nat.
  Definition eq_dec := nat_dec.
End DecidableType_nat.

Module DecidableEqDep_nat := DecidableEqDep DecidableType_nat.

Module NoCycle_dep.
  Inductive vect (A : Type) : nat -> Type :=
  | nil : vect A O
  | cons : forall n, A -> vect A n -> vect A (S n).
  Arguments nil [A].
  Arguments cons [A n] _ _.

  Derive Below for vect.
  Derive NoConfusion for vect.

  Section noCycle_vect.
    Variable (A : Type).

    Definition cond_neq (n : nat) (x : vect A n) (m : nat) (y : vect A m) :=
      match nat_dec n m with
      | left e => eq_rect _ _ x _ e <> y
      | right _ => True
      end.

    Definition noSubterm n x m y :=
      Below_vect A (cond_neq n x) m y.

    Definition noLargeSubterm n x m y :=
      (cond_neq n x m y * noSubterm n x m y)%type.

    Lemma step_cons n x m b a : noSubterm n x m b -> noLargeSubterm (S n) (cons a x) m b.
    Proof.
      induction b; intros H.
      - split.
        + exact I.
        + constructor.
      - split.
        + pose proof (fst H). unfold cond_neq in H0.
          destruct (nat_dec n n0).
          * subst n. unfold cond_neq. destruct (nat_dec (S n0) (S n0)).
            -- rewrite <- DecidableEqDep_nat.eq_rect_eq in H0 |- *.
               intros H'; inversion H'.
               apply DecidableEqDep_nat.inj_pairT2 in H3.
               apply H0. apply H3.
            -- exact I.
          * unfold cond_neq. destruct (nat_dec (S n) (S n0)).
            -- inversion e. elim n1. apply H2.
            -- exact I.
        + apply (IHb (snd H)).
    Qed.

    Definition no_cycle n x y : x = y -> noSubterm n x n y.
    Proof.
      intros ->.
      induction y.

      - constructor.
      - apply step_cons; apply IHy.
    Qed.

    Definition no_cycle_dep n x m y : forall (e : n = m),
      eq_rect _ _ x _ e = y -> noSubterm n x m y.
    Proof.
      intros ->.
      rewrite <- DecidableEqDep_nat.eq_rect_eq.
      apply no_cycle.
    Qed.
  End noCycle_vect.
End NoCycle_dep.