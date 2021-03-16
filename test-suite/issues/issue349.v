Set Asymmetric Patterns.
Set Implicit Arguments.

From Coq Require Import Lia Lists.List.
Import ListNotations.
From Equations Require Import Equations.

Open Scope bool_scope.

Inductive label : Set :=
| arrow
| product
| top.

Inductive index : Set :=
| one
| two.

Scheme Equality for index.

Definition raw_tree_type : Set := list index -> option label.

Notation defined x := (exists l, x = Some l).

Notation undefined x := (~ defined x).

Definition is_tree_type (T : raw_tree_type) : Prop :=
  defined (T []) /\
  (forall π σ : list index, defined (T (π ++ σ)) -> defined (T π)) /\
  (forall π : list index,
      T π = Some product \/ T π = Some arrow ->
      defined (T (π ++ [one])) /\
      defined (T (π ++ [two]))) /\
  (forall π : list index,
      T π = Some top ->
      undefined (T (π ++ [one])) /\
      undefined (T (π ++ [two]))).

Definition has_domain (X Y : Type) (f : X -> option Y) (𝒟 : list X) : Prop :=
  forall x : X, defined (f x) <-> List.In x 𝒟.

Definition 𝒯 : Set := { T : raw_tree_type | is_tree_type T }.

Program Definition 𝒯__f : Type := { '(T, dom) : 𝒯 * list (list index) | has_domain T dom }.

Let inspect (X Y : Type) (f : X -> Y) (x : X) : {y | f x = y} :=
  exist _ (f x) eq_refl.

Inductive finite_tree_grammar : Type :=
| ftg_top : finite_tree_grammar
| ftg_product : finite_tree_grammar -> finite_tree_grammar -> finite_tree_grammar
| ftg_arrow : finite_tree_grammar -> finite_tree_grammar -> finite_tree_grammar.

Fixpoint is_prefix (A : Type) (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (xs ys : list A) : bool :=
  match xs, ys with
  | [], _ => true
  | x :: xs, y :: ys => proj1_sig (Sumbool.bool_of_sumbool (A_eq_dec x y)) && is_prefix A_eq_dec xs ys
  | _, _ => false
  end.

Program Definition finite_subtree_domain' (𝒟 : list (list index)) (π : list index) : list (list index) :=
  map (skipn (length π)) (filter (is_prefix index_eq_dec π) 𝒟).

Program Definition finite_subtree_domain (T : 𝒯__f) : list index -> list (list index) :=
  finite_subtree_domain' (snd T).

Definition subtree (T : raw_tree_type) (π : list index) (σ : list index) : option label :=
  T (π ++ σ).

Lemma skipn_length_after_prepended_is_noop :
  forall (A : Type) (l1 l2 : list A),
    skipn (length l1) (l1 ++ l2) = l2.
Proof. induction l1; intuition. Qed.

Lemma is_prefix_correct :
  forall (A : Type) (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (xs ys : list A),
    is_prefix A_eq_dec xs ys = true <-> exists zs : list A, xs ++ zs = ys.
Proof.
  intros.
  split; intro.
  - generalize dependent ys; induction xs; intros.
    + exists ys. intuition.
    + destruct ys.
      * inversion H.
      * apply andb_prop in H as []. fold is_prefix in H0.
        destruct (A_eq_dec a a0).
        -- apply IHxs in H0 as [].
            subst.
            exists x. cbn. subst. reflexivity.
        -- discriminate.
  - inversion H. subst.
    induction xs.
    + reflexivity.
    + cbn.
      destruct (A_eq_dec a a); intuition.
      apply IHxs. eauto.
Qed.

Lemma is_prefix_correct' :
  forall (A : Type) (A_eq_dec : forall x y, {x = y} + {x <> y}) (xs ys : list A),
    is_prefix A_eq_dec xs ys = true <-> xs ++ skipn (length xs) ys = ys.
Proof.
  intros.
  split; intro;
  generalize dependent ys; induction xs; intros; destruct ys;
  intuition; try discriminate.
  - apply andb_prop in H as [].
    fold is_prefix in H0.
    cbn.
    rewrite IHxs.
    + f_equal.
      destruct (A_eq_dec a a0).
      * intuition.
      * discriminate.
    + intuition.
  - cbn.
    destruct (A_eq_dec a a0); inversion H; subst.
    + subst. apply IHxs.
      rewrite H2.
      apply H2.
    + contradiction.
Qed.

Program Lemma finite_subtree_has_domain :
  forall (T : 𝒯__f) (π : list index),
    defined ((fst T) π) ->
    has_domain (subtree (fst T) π) (finite_subtree_domain T π).
Proof.
  intros (((? & ?) & ?) & ?) ?.
  split; intro.
  - replace x0 with (skipn (length π) (π ++ x0)) by apply skipn_length_after_prepended_is_noop.
    apply in_map.
    apply filter_In.
    split.
    + apply y.
      destruct (x π) eqn:?; inversion H; subst; intuition.
    + apply is_prefix_correct. eauto.
  - apply in_map_iff in H0 as (? & ? & ?).
    cbn in *.
    destruct (x π) eqn:?.
    + apply y.
      apply filter_In in H1 as [].
      apply is_prefix_correct' in H2.
      rewrite <- H0.
      rewrite H2.
      intuition.
    + inversion H. inversion H2.
Qed.

Program Lemma subtree_is_tree_type :
  forall (T : 𝒯) (π : list index),
    defined (T π) ->
    is_tree_type (subtree T π).
Proof.
  intros (? & ? & ? & ? & ?) ? ?.
  unfold is_tree_type, undefined, not in *.
  repeat split; cbn in *; intros;
  try (apply a in H0 as []; rewrite app_assoc in *; intuition);
  try (apply a0 in H0 as []; rewrite app_assoc in *; intuition).
  - rewrite <- app_nil_end.
    intuition.
  - rewrite app_assoc in H0.
    intuition.
Qed.

Definition safe_finite_subtree (T : 𝒯__f) (π : list index) (H : defined ((proj1_sig (fst (proj1_sig T))) π)) : 𝒯__f :=
  exist
    _
    (pair
        (exist
          _
          (subtree (proj1_sig (fst (proj1_sig T))) π)
          (subtree_is_tree_type (fst (proj1_sig T)) π H))
        (finite_subtree_domain T π))
    (finite_subtree_has_domain T π H).

Lemma filter_length_le :
  forall (X : Type) (l : list X) (f : X -> bool),
    length (filter f l) <= length l.
Proof.
  intros.
  induction l; intuition.
  cbn.
  destruct (f a) eqn:?; intuition.
  cbn.
  lia.
Qed.

Lemma filter_length_lt' :
  forall (X : Type) (f : X -> bool) (l : list X),
    (exists x : X, In x l /\ f x = false) ->
    length (filter f l) < length l.
Proof.
  intros ? ? ? (? & ? & ?).
  induction l; intros.
  - inversion H.
  - cbn in *.
    destruct (f a) eqn:?.
    + inversion H.
      * subst. rewrite Heqb in H0. inversion H0.
      * cbn in *.
        apply Lt.lt_n_S.
        intuition.
    + pose proof @filter_length_le _ l f.
      cbn. lia.
Qed.

Program Lemma finite_subtree_domain_length_lt :
  forall (T : 𝒯__f) (π : list index),
    π <> nil ->
    length (finite_subtree_domain T π) < length (snd T).
Proof.
  unfold finite_subtree_domain, finite_subtree_domain'.
  intros (((? & ? & ? & ? & ?) & ?) & ?) ? ?.
  rewrite map_length.
  apply filter_length_lt'.
  induction π.
  - intuition.
  - exists [].
    split.
    + apply y. intuition.
    + intuition.
Qed.
Axiom todo : forall {A}, A.

#[program]
Equations reify_finite_tree (T : 𝒯__f) : finite_tree_grammar by wf (length (snd (proj1_sig T))) lt :=
  reify_finite_tree T with inspect (fun T => (fst T) []) T := {
    | exist _ (Some top) _ => ftg_top;
    | exist _ (Some product) H__eq =>
      ftg_product
        (reify_finite_tree (safe_finite_subtree T [one] _))
        (reify_finite_tree (safe_finite_subtree T [two] _));
    | exist _ (Some arrow) H__eq =>
      ftg_arrow
        (reify_finite_tree (safe_finite_subtree T [one] _))
        (reify_finite_tree (safe_finite_subtree T [two] _));
    | exist _ None _ => ftg_top
  }.
  
Obligation 1.
  clear reify_finite_tree.
  destruct T as (((? & ? & ? & ? & ?) & ?) & ?).
  assert (x [] = Some product \/ x [] = Some arrow) by intuition.
  apply a in H as [].
  apply H.
Qed.
Next Obligation.
  clear reify_finite_tree.
  apply finite_subtree_domain_length_lt. intro. inversion H.
Qed.
Next Obligation.
clear reify_finite_tree.
destruct T as (((? & ? & ? & ? & ?) & ?) & ?).
  assert (x [] = Some product \/ x [] = Some arrow) by intuition.
  apply a in H as [].
  apply H0.
Qed.
Next Obligation.
clear reify_finite_tree.
apply finite_subtree_domain_length_lt. intro. inversion H.
Qed.
Next Obligation.
clear reify_finite_tree.
destruct T as (((? & ? & ? & ? & ?) & ?) & ?).
  assert (x [] = Some product \/ x [] = Some arrow) by intuition.
  apply a in H as [].
  apply H.
Qed.
Next Obligation.
clear reify_finite_tree.
apply finite_subtree_domain_length_lt. intro. inversion H.
Qed.
Next Obligation.
clear reify_finite_tree.
destruct T as (((? & ? & ? & ? & ?) & ?) & ?).
  assert (x [] = Some product \/ x [] = Some arrow) by intuition.
  apply a in H as [].
  apply H0.
Qed.
Next Obligation.
  clear reify_finite_tree.
  apply finite_subtree_domain_length_lt. intro. inversion H.
Qed.

Lemma reify_graph_elim (T : 𝒯__f) : reify_finite_tree T = reify_finite_tree T.
Proof.
  apply_funelim (reify_finite_tree T).
Abort.
