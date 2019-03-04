From Coq Require Import Extraction CRelationClasses.
From Equations Require Import Init.
Require Import Equations.Type.Logic
        Equations.Type.Relation Equations.Type.Relation_Properties.

Import Id_Notations.
Import Sigma_Notations.

(** Well-founded relations in Type *)

Section Wf.

  Context {A} (R : relation A).

  Inductive Acc (x : A) : Type :=
  | Acc_intro : (forall y, R y x -> Acc y) -> Acc x.

  Definition Acc_inv {x} (H : Acc x) : forall y, R y x -> Acc y.
  Proof. intros y Hy. destruct H. exact (a _ Hy). Defined.

  Definition well_founded := forall x, Acc x.

End Wf.

Section Wf_Transitive_Closure.

  (** Original author: Bruno Barras, adapted to Type *)
  Context {A : Type} (R : relation A).

  Notation trans_clos := (trans_clos R).

  Lemma incl_trans_clos : inclusion R trans_clos.
    red; auto with relations.
  Defined.

  Lemma Acc_trans_clos : forall x:A, Acc R x -> Acc trans_clos x.
    induction 1 as [x0 _ H1].
    apply Acc_intro.
    intros y H2.
    induction H2; auto with relations.
    apply Acc_inv with y; auto with relations.
  Defined.

  Hint Resolve Acc_trans_clos : core.

  Lemma Acc_inv_trans : forall x y:A, trans_clos y x -> Acc R x -> Acc R y.
  Proof.
    induction 1 as [| x y]; auto with relations.
    intro; apply Acc_inv with y; assumption.
  Defined.

  Theorem wf_trans_clos : well_founded R -> well_founded trans_clos.
  Proof.
    unfold well_founded; auto with relations.
  Defined.

End Wf_Transitive_Closure.

Lemma well_founded_irreflexive {A} {R : relation A} {wfR : well_founded R} :
  forall x y : A, R x y -> x = y -> Empty.
Proof.
  intros x y Ryy ->. red in wfR.
  induction (wfR y) as [y accy IHy].
  apply (IHy _ Ryy Ryy).
Qed.
