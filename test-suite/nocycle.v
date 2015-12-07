Require Import Equations.Equations.

Module NoCycle_nat.
  
Definition noSubterm x y :=
  Below_nat (fun y => x <> y) y.

Definition noLargeSubterm x y :=
  ((x <> y) * noSubterm x y)%type.

Lemma step x b : noSubterm x b -> noLargeSubterm (S x) b.
Proof.
  induction b; simpl; red. intros.
  split; cbn. 
  intro H'; noconf H'.
  exact I.

  intros [H H'].
  split.

  intro He; noconf He. apply H; reflexivity.
  specialize (IHb H').
  split. red in IHb. intuition.
  apply IHb.
Qed.  
  
Definition no_cycle x y : x = y -> noSubterm x y.
Proof.
  intros ->. induction y.

  exact I.

  simpl.
  now apply step.
Qed.
End NoCycle_nat.

Module NoCycle_ord.

  Inductive O : Set :=
    | zero | succ : O -> O | lim : (nat -> O) -> O.
  Derive NoConfusion for O.

  Fixpoint Below_O (P : O -> Type) (c : O) : Type :=
    match c with
    | zero => True
    | succ o => P o * Below_O P o
    | lim f =>
      forall x : nat, (P (f x) * Below_O P (f x))
    end.

  Lemma below_O (P : O -> Type) (c : O)
        (f : forall x : O, Below_O P x -> P x) : Below_O P c.
  Proof.
    induction c; simpl.

    exact I.

    exact (f c IHc, IHc).

    intros.
    split;[|apply X].
    apply f. apply X.
  Qed.

  Definition noSubterm x y :=
    Below_O (fun y => x <> y) y.

  
  Definition noLargeSubterm x y :=
    ((x <> y) * noSubterm x y)%type.

  Lemma step_succ x b : noSubterm x b -> noLargeSubterm (succ x) b.
  Proof.
    revert x. induction b; simpl; red. intros.
    split; cbn. 
    intro H'; noconf H'.
    exact I.

    intros x Hf.
    split. intro He; noconf He.
    now apply (fst Hf).
    apply IHb. apply Hf.

    intros x Hf.
    split. intro He; noconf He.
    red. simpl.
    intros x0.
    apply X.
    apply Hf.
  Qed.      

  Lemma step f b : forall x, noSubterm (f x) b -> noLargeSubterm (lim f) b.
  Proof.
    revert f. induction b; simpl; red. intros.
    split; cbn. 
    intro H'; noconf H'.
    exact I.


    intros f x Hf.
    split. intro He; noconf He.
    specialize (IHb f x (snd Hf)).
    apply IHb.
    
    intros f x Hf.
    split.
    
    intro He. noconf He. red in Hf. simpl in Hf.
    destruct (Hf x). apply n; reflexivity.

    split. 
    apply (X x0 f x). specialize (Hf x0). apply Hf.
    red in Hf. intuition.
  Qed.
  
  Definition no_cycle x y : x = y -> noSubterm x y.
  Proof.
    intros ->. induction y.
    
    exact I.
    
    simpl.
    now apply step_succ.
    
    red. simpl. intros x.
    apply (step o (o x) x (X x)). 
  Qed.
End NoCycle_ord.

Inductive t :=
| L | N (x y : t).

Derive Below for t.
Derive NoConfusion for t.
Definition noSubterm x y :=
  Below_t (fun y => x <> y) y.

Definition noLargeSubterm x y :=
  ((x <> y) * noSubterm x y)%type.

Lemma step_l x y b : noSubterm x b -> noLargeSubterm (N x y) b.
Proof.
  induction b; red. intros.

  split; cbn. 
  intro H'; noconf H'.
  exact I.

  intros [H H'].
  split.

  intro He; noconf He. apply (fst H'); reflexivity.

  split.
  apply IHb2; intuition.
  apply IHb1; intuition.
Qed.  

Lemma step_r x y b : noSubterm y b -> noLargeSubterm (N x y) b.
Proof.
  induction b; red. intros.

  split; cbn. 
  intro H'; noconf H'.
  exact I.

  intros [H H'].
  split.

  intro He; noconf He. apply (fst H); reflexivity.

  split.
  apply IHb2; intuition.
  apply IHb1; intuition.
Qed.  

Definition no_cycle x y : x = y -> noSubterm x y.
Proof.
  intros ->. induction y.

  exact I.

  simpl.
  split.
Focus 2.  now apply step_l.
now apply step_r.
Qed.
