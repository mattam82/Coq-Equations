From Equations Require Import Equations.
Require Import Equations.Subterm.
Require Import Lia.

Section Tests.

  Context {A : Type}.

  Inductive forest : Type :=
  | emp : A -> forest
  | tree : list forest -> forest.

  Equations fweight (f : forest) : nat :=
    {
      fweight (emp _) := 1;
      fweight (tree l) := 1 + lweight l
    }
  where lweight (l : list forest) : nat :=
    {
      lweight nil := 1;
      lweight (cons f l') := fweight f + lweight l'
    }.

  Inductive tail_of {A} : list A -> list A -> Prop :=
  | t_refl : forall l, tail_of l l
  | t_cons : forall x l1 l2, tail_of l1 l2 -> tail_of l1 (cons x l2).
  Hint Constructors tail_of.
  Derive Signature for tail_of.

  Lemma tail_of_decons : forall {A} {x : A} {l1 l2},
      tail_of (cons x l1) l2 ->
      tail_of l1 l2.
  Proof.
    intros. remember (cons x l1) as l.
    revert Heql. revert l1.
    induction H; intros; subst; auto.
  Qed.

  Lemma fweight_neq_0 : forall f, fweight f <> 0.
  Proof.
    intros.
    destruct f.
    Fail funelim (fweight (emp a)).

    Restart.

    intros. destruct f; simp fweight; lia.
  Qed.

  Lemma lweight_neq_0 : forall l, lweight l <> 0.
  Proof.
    intros. destruct l; simpl.
    lia.
    pose proof (fweight_neq_0 f). lia.
  Qed.

  Lemma tail_of_fweight : forall l1 l2,
      tail_of l1 l2 ->
      lweight l1 <= lweight l2.
  Proof.
    induction 1; simp lweight; try lia.
    simpl. pose proof (fweight_neq_0 x).
    lia.
  Qed.
End Tests.

Hint Rewrite @fweight_equation_1 @fweight_equation_2 @lweight_equation_1 @lweight_equation_2 : fweight.


Arguments forest A : clear implicits.
Hint Constructors tail_of.

Module FlattenNestedWf.
  Set Equations Debug.
  Obligation Tactic := idtac.

  Equations? flatten {A} (f : forest A) : list A by rec (fweight f) lt :=
  flatten (emp _) := nil;
  flatten (tree l) := lflatten l (t_refl _)

  where lflatten (fs : list (forest A)) (t : tail_of fs l) : list A by struct fs :=
    {
      lflatten nil _ := nil;
      lflatten (cons f l') H := flatten f ++ lflatten l' (tail_of_decons H)
    }.
  Proof.
    intros. simp fweight. clear flatten lflatten. depind H. simpl. lia.
    simpl. lia.
  Defined.

End FlattenNestedWf.

Module FlattenNestedStruct.
  Section foo.
    Variable A : Type.

    Equations flatten (f : forest A) : list A by struct f :=
    flatten (emp _) := nil;
    flatten (tree l) := lflatten l (t_refl _)

    where lflatten (fs : list (forest A)) (t : tail_of fs l) : list A by struct fs := {
      lflatten nil _ := nil;
      lflatten (cons f l') H := flatten f ++ lflatten l' (tail_of_decons H) }.

  End foo.
End FlattenNestedStruct.