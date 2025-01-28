From Equations.Prop Require Import Equations.

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

Module QualifiedTactic.
  (* Program_simpl solves goals in nat *)
  #[tactic="Program.Tactics.program_simpl"]
  Equations foo (x : nat) : nat :=
    | x := _.

  (* equations_simpl doesn't *)
  #[tactic="Equations.CoreTactics.equations_simplify"]
  Equations bar (x : nat) : nat :=
    | x := _.
    Next Obligation. exact 0. Qed.

End QualifiedTactic.
