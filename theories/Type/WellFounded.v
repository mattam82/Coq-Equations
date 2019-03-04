From Coq Require Import Extraction CRelationClasses.
From Equations Require Import Init.
Require Import Equations.Type.Relation.

(** Well-founded relations in Type *)

Section Wf.

  Context {A} (R : relation A).

  Inductive Acc (x : A) : Type :=
  | Acc_intro : (forall y, R y x -> Acc y) -> Acc x.

  Definition well_founded := forall x, Acc x.

End Wf.
