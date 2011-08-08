Require Import Program Equations Bvector List.
Require Import Relations.
Require Import DepElimDec.

Require Import Arith Wf_nat.
Instance wf_nat : WellFounded lt := lt_wf.
Hint Resolve lt_n_Sn : Below.
Ltac rec ::= rec_wf_eqns.

Module RecRel.

  Equations id (n : nat) : nat :=
  id n by rec n lt :=
  id O := 0 ;
  id (S n) := S (id n).

End RecRel.

Definition gt_bound n : relation nat :=
  fun x y => x > y /\ x < n.

Definition minus_12 n := 
  if le_lt_dec n 100 then n - 12 else n.

Instance gt_bound_wf n : WellFounded (gt_bound n).
Proof. red. red. intros.
  Admitted.

Equations foo (n : nat) : Prop :=
foo n by rec n (gt_bound 100) :=
foo n := _.

Admit Obligations.



Equations f91 n : { m : nat | n < m - 11 } :=
f91 n by rec n (gt_bound 100) :=
f91 n with le_lt_dec n 100 := {
  | left H := exist _ (proj1_sig (f91 (proj1_sig (f91 (n + 11))))) _ ;
  | right H := exist _ (n - 10) _ }.

Set Printing Depth 1000.

Admit Obligations.

Next Obligation. apply f91. red.
  unfold minus_12. destruct (le_lt_dec n 100).
  destruct le_lt_dec.
  simpl. admit.


Section Nested.

  Equations f (n : nat) : { x : nat | x <= n } :=
  f n by rec n lt :=
  f 0 := exist _ 0 _ ;
  f (S n) := exist _ (proj1_sig (f (proj1_sig (f n)))) _.

  Next Obligation. destruct_call f_comp_proj. simpl. exists x. auto. Defined.
  Next Obligation. do 2 destruct_call f_comp_proj. simpl in *. eauto with arith. Defined.

  Next Obligation. do 2 destruct_call f. simpl in *. eauto with arith. Defined.

  Next Obligation. admit. Defined. 

  Next Obligation. 
    rec_wf_rel n IH lt.
    destruct x. constructor. simp f.
    constructor. intros. subst recres. auto.
    auto. apply IH. destruct f. auto with arith.
  Defined.

About f_elim.

End Nested.
Require Import Coq.Lists.SetoidList.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.PermutSetoid.

Print Instances Morphisms.Proper.

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
  apply Permutation_cons. revert H1. 
  case_eq (q a); intros qa; intros; try discriminate. elim H1.
  apply IHl.

  revert H1. 
  case_eq (q a); intros qa; intros; try discriminate.
  auto using Permutation_cons_app. elim H1.
Qed.

Module RecMeasure.
  
  Equations id (n : nat) : nat :=
  id n by rec n (MR lt (fun n => n)) :=
  id O := 0 ;
  id (S n) := S (id n).

  Equations f (n m : nat) : nat :=
  f n m by rec n (MR lt (fun n => n)) :=
  f O m := m ;
  f (S n) m := S (f n m) + m.

  Implicit Arguments length [[A]].


  Instance wf_MR {A R} `(WellFounded A R) {B} (f : B -> A) : WellFounded (MR R f).
  Proof. red. apply measure_wf. apply H. Defined.

  Equations g (l : list nat) : nat :=
  g n by rec n (MR lt (@length nat)) :=
  g nil := 0 ;
  g (cons n l) := S (g l).
  
  Lemma filter_length {A} p (l : list A) : length (filter p l) <= length l.
  Proof. induction l ; simpl ; auto. destruct (p a); simpl; auto with arith. Qed.
    
  Hint Resolve @filter_length : datatypes.
  
  Section QuickSort.
    
    Hint Extern 3 (MR _ _ _ _) => unfold MR : Below.
    Hint Resolve gt_le_S : Below.
    Hint Resolve @filter_length : Below.
    Hint Unfold lt gt : Below.
    Hint Resolve le_lt_n_Sm : Below.

    Context {A : Type} (leb : A -> A -> bool) (ltb : A -> A -> bool).

    Equations qs (l : list A) : list A :=
    qs l by rec l (MR lt (@length A)) :=
    qs nil := nil ;
    qs (cons a l) := 
      let lower := filter (fun x => ltb x a) l in
      let upper := filter (fun x => leb a x) l in
        qs lower ++ a :: qs upper.

    Context (le : relation A).
    Context (refl_le : forall x y, reflect (le x y) (leb x y)).

    Context (lt : relation A).
    Context (refl_lt : forall x y, reflect (lt x y) (ltb x y)).

    Context (leb_complete : forall x y, leb x y <-> (x = y \/ leb y x = false)).
    Context (leb_complete2 : forall x y, leb x y = false -> leb y x).

    Context (ltb_leb : forall x y, ltb x y -> leb x y).
    Context (nltb_leb : forall x y, ltb x y = false -> leb y x).
(*     Context (ltb_leb' : forall x y, ltb x y = false -> (x = y \/ leb y x = true)). *)
    Context (ltb_leb' : forall x y, leb x y = false <-> ltb y x).
    Context (ltb_leb'' : forall x y, ltb x y <-> ~ leb y x).

    About filter_In.
    Lemma filter_In' :
      ∀ (A : Type) (f : A → bool) (x : A) (l : list A),
      In x (filter f l) ↔ In x l ∧ f x.
    Proof.
      intros. rewrite filter_In. intuition. apply Is_true_eq_true; auto.
    Qed.

    Lemma qs_same (l : list A) : forall a, In a l <-> In a (qs l).
    Proof. intros.
      pattern_call (qs l).
      let p := constr:(fun_elim (f:=@qs)) in apply p.
      reflexivity.

      intros.
      simpl. split; intros.
      destruct H1. subst. auto with datatypes.
      case_eq (leb a a0); intros eq. 
      apply Is_true_eq_left in eq.
      rewrite leb_complete in eq.
      destruct eq. subst. rewrite in_app_iff. right; left; auto.
      
      rewrite filter_In' in H.
      rewrite in_app_iff. left. apply H. rewrite ltb_leb' in H2. auto.
      
      rewrite filter_In' in H0. 
      rewrite in_app_iff. right. right. apply H0. auto.
      
      rewrite in_app_iff in H1. destruct H1. rewrite <- H, filter_In' in H1. tauto.
      apply in_inv in H1. destruct H1; auto. right. rewrite <- H0 in H1. rewrite filter_In' in H1. tauto.
    Qed.

    Lemma sort_le_app :
      forall l1 l2, sort le l1 -> sort le l2 ->
        (forall x y, In x l1 -> In y l2 -> le x y) ->
        sort le (l1 ++ l2).
    Proof.
      induction l1; simpl in *; intuition.
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
    Proof. intros.
      pattern_call (qs l).
      let p := constr:(fun_elim (f:=@qs)) in apply p.
      constructor.

      intros.
      apply sort_le_app; auto.
      constructor. auto. apply hdrel_filter.
      intros. simpl in H2.
      rewrite <- qs_same, filter_In' in H1, H2.
      intuition auto with arith. subst. pose (r:=refl_le x y); apply ltb_leb in H4; now depelim r.
      apply ltb_leb in H4.
      pose (r:=refl_le x a); pose (r':=refl_le a y); depelim r; depelim r'; reverse; simplify_dep_elim; auto. 
      transitivity a; auto. elim H5.  elim H4. elim H4.
    Qed.
    Require Import EquivDec.
    Require Import Permutation.
    Existing Instance Permutation_app'_Proper.

(*     Lemma leb_negb a : (fun x => leb a x) === compose negb (fun x => leb x a). *)
(*     Proof. *)
(*       unfold negb, compose. intros x.  *)
(*       case_eq (leb a x); intros H. *)
(*       apply leb_complete in H. destruct H. subst. admit. *)
(*       now rewrite H. *)
(*       apply leb_complete2 in H. *)
(*       now rewrite H. *)
(*     Qed. *)
(*     Typeclasses eauto :=. *)

(*     Lemma leb_negb' a : (fun x => leb x a) === compose negb (fun x => leb a x). *)
(*     Proof. *)
(*       unfold negb, compose. intros x.  *)
(*       case_eq (leb x a); intros H. *)
(*       apply leb_complete in H. destruct H. subst. admit. *)
(*       now rewrite H. *)
(*       apply leb_complete2 in H. *)
(*       now rewrite H. *)
(*     Qed. *)
(*     Typeclasses eauto :=. *)

    Lemma qs_perm l : Permutation l (qs l).
    Proof.
      pattern_call (qs l).
      let p := constr:(fun_elim (f:=@qs)) in apply p.
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

End RecMeasure.

Section Nested.

  Equations f (n : nat) : { x : nat | x <= n } :=
  f n by rec n lt :=
  f 0 := exist _ 0 _ ;
  f (S n) := exist _ (proj1_sig (f (proj1_sig (f n)))) _.

  Next Obligation. destruct_call f_comp_proj. simpl. exists x. auto. Defined.
  Next Obligation. do 2 destruct_call f_comp_proj. simpl in *. eauto with arith. Defined.
    Set Printing All.
  Print f_obligation_2.

  Next Obligation. do 2 destruct_call f. simpl in *. eauto with arith. Defined.

  Next Obligation. admit. Defined. 

  Next Obligation. 
    rec_wf_rel n IH lt.
    destruct x. constructor. simp f.
    constructor. intros. subst recres. auto.
    auto. apply IH. destruct f. auto with arith.
  Defined.

End Nested.