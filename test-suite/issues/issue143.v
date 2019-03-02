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
  Hint Constructors tail_of : core.
  Derive Signature for tail_of.

  Lemma tail_of_decons : forall {A} {x : A} {l1 l2},
      tail_of (cons x l1) l2 ->
      tail_of l1 l2.
  Proof.
    intros. remember (cons x l1) as l.
    revert Heql. revert l1.
    induction H; intros; subst; auto.
  Qed.

  Lemma prod_conj : forall (A B : Prop), A * B -> A /\ B.
  Proof. intuition. Defined.

  Lemma fweight_neq_0 : (forall f, fweight f <> 0) /\ forall l, lweight l <> 0.
  Proof.
    assert (fe:=fun_elim (f:=fweight)). apply prod_conj.
    apply (fe (fun l n => n <> 0) (fun l n => n <> 0)); intros; lia.
  Qed.

  Lemma lweight_neq_0 : forall l, lweight l <> 0.
  Proof. apply fweight_neq_0. Defined.

  Lemma tail_of_fweight : forall l1 l2,
      tail_of l1 l2 ->
      lweight l1 <= lweight l2.
  Proof.
    induction 1; simp lweight; try lia.
    simpl. pose proof (proj1 fweight_neq_0 x).
    lia.
  Qed.
End Tests.

Arguments forest A : clear implicits.
Hint Constructors tail_of : core.

Module FlattenNestedWf.
  Equations? flatten {A} (f : forest A) : list A by wf (fweight f) lt :=
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
  Qed.

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
