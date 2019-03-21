From Equations Require Import Equations.
(* Assuming UIP *)
From Coq.Logic Require Import Eqdep.

Section FreeMonad.

  Variable S : Type.
  Variable P : S -> Type.

  Inductive FreeF A : Type :=
  | retFree : A -> FreeF A
  | opr     : forall s, (P s -> FreeF A) -> FreeF A.

  Derive Signature for Relation_Operators.clos_trans.
  Derive Subterm for FreeF.

  Next Obligation.
    revert a.
    apply Transitive_Closure.wf_clos_trans.
    intro.
    induction a ; constructor.
    - intros ? H ; exfalso ; depelim H. discriminate H.
    - intros ? Hsub ; cbv in Hsub ; depind Hsub.
      injection H0. intro H1. intros ->.
      apply EqdepTheory.inj_pair2 in H1. subst. apply H.
  Defined.

End FreeMonad.
