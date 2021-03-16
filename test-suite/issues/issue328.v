Set Implicit Arguments.
From Coq Require Import Omega.
From Equations Require Import Equations.

Parameter A : Type.

Inductive nonEmpty (A : Type) : Type :=
| singleton : A -> nonEmpty A
| consNE : A -> nonEmpty A -> nonEmpty A.

Equations? fromList (l : list A) : length l > 0 -> nonEmpty A :=
{ 
  fromList nil H := _;
  fromList (cons x nil) _ := singleton x;
  fromList (cons x (cons y l))  _ := consNE x (fromList (cons y l) _)
}.
Proof.
  - exfalso. abstract omega.
  - abstract omega.
Defined.
(* Error: <in exception printer>:<original exception:Anomaly "Uncaught exception Not_found." *)
(* Please report at http://coq.inria.fr/bugs/. *)
