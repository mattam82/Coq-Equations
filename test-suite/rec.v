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

    Context {A : Type} (leb : A -> A -> bool).

    Equations qs (l : list A) : list A :=
    qs l by rec l (MR lt (@length A)) :=
    qs nil := nil ;
    qs (cons a l) := 
      let lower := filter (fun x => leb x a) l in
      let upper := filter (fun x => leb a x) l in
        qs lower ++ a :: qs upper.

    Context (R : relation A).
    Context (refl : forall x y, reflect (R x y) (leb x y)).

    Context (leb_complete : forall x y, leb x y = true <-> (x = y \/ leb y x = false)).
    Context (leb_complete2 : forall x y, leb x y = false -> leb y x = true).
    

    Lemma qs_same (l : list A) : forall a, In a l <-> In a (qs l).
    Proof. intros.
      pattern_call (qs l).
      let p := constr:(fun_elim (f:=@qs)) in apply p.
      reflexivity.

      intros.
      simpl. split; intros.
      destruct H1. subst. auto with datatypes.
      case_eq (leb a a0); intros eq.
      rewrite leb_complete in eq.
      destruct eq. subst. rewrite in_app_iff. right; left; auto.
      
      rewrite filter_In in H.
      rewrite in_app_iff. left. apply H. auto.
      
      rewrite filter_In in H0.
      rewrite in_app_iff. right. right. apply H0. auto.
      
      rewrite in_app_iff in H1. destruct H1. rewrite <- H, filter_In in H1. tauto.
      apply in_inv in H1. destruct H1; auto. right. rewrite <- H0 in H1. rewrite filter_In in H1. tauto.
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

  Next Obligation. do 2 destruct_call f. simpl in *. eauto with arith. Defined.

  Next Obligation. admit. Defined. 

  Next Obligation. 
    rec_wf_rel n IH lt.
    destruct x. constructor. simp f.
    constructor. intros. subst recres. auto.
    auto. apply IH. destruct f. auto with arith.
  Defined.


  About f_elim.
