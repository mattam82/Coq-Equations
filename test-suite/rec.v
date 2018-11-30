(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
Require Import Program Utf8.
From Equations Require Import Equations DepElimDec.
Require Import Bvector List Relations.
Require Import Omega Arith Wf_nat.
Require Import Subterm.

Instance wf_nat : WellFounded lt := lt_wf.
Hint Resolve lt_n_Sn : Below.
Module RecRel.
  Equations id (n : nat) : nat
  by rec n lt :=
  id O := 0 ;
  id (S n) := S (id n).
  
End RecRel.

Section Nested.

  Ltac destruct_proj1_sig :=
    match goal with 
      | [ |- context [ ` (?x) ] ] => destruct x as [?x' ?H]; simpl
    end.
  (* with destruct_proj1_sigs x := *)
  (*     match x with *)
  (*     (* | context [ ` (?x') ] => destruct_proj1_sigs x' *) *)
  (*     | _ => *)
  (*       let x' := fresh in *)
  (*       let H' := fresh in *)
  (*         destruct x as [x' H'] ; simpl proj1_sig; destruct_proj1_sig *)
  (*   end. *)

  Hint Extern 3 => progress destruct_proj1_sig : Below.
  
  Hint Extern 3 => progress auto with arith : Below.

  Equations f (n : nat) : { x : nat | x <= n }
   by rec n lt :=
  f 0 := exist _ 0 _ ;
  f (S n) := exist _ (proj1_sig (f (proj1_sig (f n)))) _.

  Next Obligation. 
    unfold f_comp_proj. repeat destruct_proj1_sig.
    revert H. destruct_proj1_sig.
    intros. omega.
  Defined.

End Nested.

Require Import Coq.Lists.SetoidList.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutSetoid.

Instance filter_ext {A} : Morphisms.Proper (pointwise_relation A eq ==> eq ==> eq) (@filter A).
Proof.
  reduce. subst. induction y0; simpl; auto. generalize (H a). case_eq (x a). intros _ <-; congruence.
  intros _ <-; congruence.
Qed.

Lemma Permutation_filter {A} (l : list A)
  (p : A -> bool) : Permutation l (filter p l ++ filter (compose negb p) l).
Proof with simpl; intros.
  induction l; unfold compose; simpl; auto.
  case_eq (p a); simpl; intros;
  auto using Permutation_cons_app. 
Qed.

Inductive xor (A B : Prop) : Prop :=
| xor_left : A -> not B -> xor A B
| xor_right : B -> not A -> xor A B.

Require Import Bool.
Coercion Is_true : bool >-> Sortclass.

Lemma xor_reflect (x y : bool) : reflect (xor x y) (xorb x y).
Proof.
  destruct x; destruct y; simpl; auto;
  constructor; try (intro H; elim H); firstorder.
Qed.

Lemma Permutation_filter2 {A} (l : list A)
  (p q : A -> bool) : 
  (forall x, xorb (p x) (q x)) ->
  Permutation l (filter p l ++ filter q l).
Proof with simpl; intros. intros.
  induction l; unfold compose; simpl; auto.
  generalize (H a).
  case_eq (p a); simpl; intros.
  apply Permutation_cons; auto. revert H1. 
  case_eq (q a); intros qa; intros; try discriminate. elim H1. 
  apply IHl.

  revert H1. 
  case_eq (q a); intros qa; intros; try discriminate.
  auto using Permutation_cons_app. elim H1.
Qed.

Require Import EquivDec.
Require Import Permutation.

Module RecMeasure.

  Instance wf_MR {A R} `(WellFounded A R) {B} (f : B -> A) : WellFounded (MR R f).
  Proof. red. apply measure_wf. apply H. Defined.

  Hint Extern 0 (MR _ _ _ _) => red : Below.

  Equations id (n : nat) : nat
  by rec n (MR lt (fun n => n)) :=
  id O := 0 ;
  id (S n) := S (id n).

  Equations f (n m : nat) : nat
  by rec n (MR lt (fun n => n)) :=
  f O m := m ;
  f (S n) m := S (f n m) + m.

  Arguments length [A] _.

  Equations g (l : list nat) : nat
  by rec l (MR lt (@length nat)) :=
  g nil := 0 ;
  g (cons n l) := S (g l).
  
  Lemma filter_length {A} p (l : list A) : length (filter p l) <= length l.
  Proof. induction l ; simpl ; auto. destruct (p a); simpl; auto with arith. Qed.
    
  Hint Resolve @filter_length : datatypes.
  
  Section QuickSort.
    
    Hint Immediate gt_le_S : Below.
    Hint Resolve @filter_length : Below.
    Hint Unfold lt gt : Below.
    Hint Resolve le_lt_n_Sm : Below.

    Context {A : Type} (leb : A -> A -> bool) (ltb : A -> A -> bool).

    Equations qs (l : list A) : list A by rec l (MR lt (@length A)) :=
    qs nil := nil ;
    qs (cons a l) := 
      let lower := filter (fun x => ltb x a) l in
      let upper := filter (fun x => leb a x) l in
        qs lower ++ a :: qs upper.

    Context (le : relation A).
    Context (refl_le : forall x y, reflect (le x y) (leb x y)).

    Context (lt : relation A).
    Context (refl_lt : forall x y, reflect (lt x y) (ltb x y)).

    Context (compare : A -> A -> comparison).
    Context (compspec : forall x y, CompSpec eq lt x y (compare x y)).

    Context (leb_complete : forall x y, leb x y <-> (x = y \/ leb y x = false)).
    Context (leb_complete2 : forall x y, leb x y = false -> leb y x).

    Context (ltb_leb : forall x y, ltb x y -> leb x y).
    Context (nltb_leb : forall x y, ltb x y = false -> leb y x).
    Context (ltb_leb' : forall x y, leb x y = false <-> ltb y x).
    Context (ltb_leb'' : forall x y, ltb x y <-> ~ leb y x).

    Set Firstorder Solver auto.

    Lemma filter_In' :
      ∀ (A : Type) (f : A → bool) (x : A) (l : list A),
      In x (filter f l) ↔ In x l ∧ f x.
    Proof.
      intros. rewrite filter_In. intuition auto. apply Is_true_eq_true2. auto.
      apply Is_true_eq_true. auto.
    Qed.

    Lemma qs_same (l : list A) : forall a, In a l <-> In a (qs l).
    Proof.
      funelim (qs l).
      - simpl. reflexivity.
      - intros a'. simpl. rewrite in_app_iff. simpl.
        rewrite <- H, <- H0, !filter_In'. intuition auto.
        destruct (compspec a a'); intuition auto. right. right. intuition auto with arith.
        apply ltb_leb. destruct (refl_lt a a'); auto. constructor. contradiction.
        left. intuition auto.
        destruct (refl_lt a' a); auto. constructor. contradiction.
    Qed.

    Lemma sort_le_app :
      forall l1 l2, sort le l1 -> sort le l2 ->
        (forall x y, In x l1 -> In y l2 -> le x y) ->
        sort le (l1 ++ l2).
    Proof.
      induction l1; simpl in *; intuition auto.
      inversion_clear H.
      constructor; auto.
      apply InfA_app; auto.
      destruct l2; auto.
      constructor ; auto.
      auto with datatypes.
    Qed.
  
    Lemma hd_rel_all a l : (forall x, In x l -> le a x) -> HdRel le a l.
    Proof. intros H. induction l; auto.
      constructor. apply H. auto with datatypes.
    Qed.

    Lemma hdrel_filter a l : HdRel le a (qs (filter (λ x : A, leb a x) l)).
    Proof. apply hd_rel_all. 
      intros. rewrite <- qs_same in H. rewrite filter_In in H. destruct H.
      pose (refl_le a x). now depelim r.
    Qed.
   
    Context `(le_trans : Transitive A le).

    Lemma qs_sort (l : list A) : sort le (qs l).
    Proof. intros. funelim (qs l). constructor.
      apply sort_le_app; auto.
      constructor. auto. apply hdrel_filter.
      intros. simpl in H2.
      rewrite <- qs_same, filter_In' in H1, H2.
      intuition auto with arith. subst. pose (r:=refl_le x y); apply ltb_leb in H4; now depelim r.
      apply ltb_leb in H4.
      pose (r:=refl_le x a); pose (r':=refl_le a y); depelim r; depelim r'; reverse; simplify_dep_elim; auto. 
      transitivity a; auto.
    Qed.

    Lemma qs_perm l : Permutation l (qs l).
    Proof.
      funelim (qs l).
      constructor.
      intros. 
      rewrite <- H0, <- H.
      apply Permutation_cons_app.
      rewrite Permutation_app_comm.
      apply Permutation_filter2.
      intros. case_eq (leb a x). simpl.
      intros.
      case_eq (ltb x a). intros. 
      apply Is_true_eq_left in H2.
      apply Is_true_eq_left in H1.
      apply ltb_leb'' in H2. contradiction.
      constructor.
      simpl.
      intros.
      rewrite ltb_leb' in H1. case_eq (ltb x a). constructor.
      intros. rewrite H2 in H1. elim H1.
    Qed.
  
  End QuickSort.

  (* Recursive Extraction qs. *)

End RecMeasure.
