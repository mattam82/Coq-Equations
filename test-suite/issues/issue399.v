From Equations Require Import Equations.
From Stdlib Require Import Bool.
Inductive depInd : Type -> Type :=
| A : depInd bool
| B : depInd unit.
Derive Signature for depInd.

Equations bar {a} (d : depInd (id a)) : a -> bool :=
 | A => fun x => eqb x true
 | B => fun x => true.

About bar_elim.


