From Equations Require Import Equations.
(* Assuming UIP *)
From Stdlib.Logic Require Import Eqdep.

Section FreeMonad.

  Variable S : Type.
  Variable P : S -> Type.

  Inductive FreeF A : Type :=
  | retFree : A -> FreeF A
  | opr     : forall s, (P s -> FreeF A) -> FreeF A.

  Derive Signature for Relation_Operators.clos_trans.
  Derive NoConfusion Subterm for FreeF.

End FreeMonad.
