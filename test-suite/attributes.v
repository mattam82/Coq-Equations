From Equations Require Import Equations.

Ltac solvetac := 
  match goal with |- ?T => exact 0 end.

Module WithProgram.
  #[tactic=idtac]
  Equations foo (x : nat) : nat :=
  | 0 => 0
  | S n => S _.

  Next Obligation. exact 0. Qed.

  #[tactic=solvetac]
  Equations foo' (x : nat) : nat :=
  | 0 => 0
  | S n => S _.
  Definition test := foo'.
End WithProgram.

Module WithProofMode.
  #[tactic=idtac]
  Equations? foo (x : nat) : nat :=
  | 0 => _
  | S n => S _.
  Proof. exact 0. abstract exact 1. Defined.
  
  #[tactic=solvetac]
  Equations foo' (x : nat) : nat :=
  | 0 => 0
  | S n => S _.

End WithProofMode.

