From Stdlib Require Import Lia NArith.NArith Program.Tactics.
From Equations Require Export Equations.
Ltac hidebody H ::= idtac.

Import Pos N.
Print Pos.compare.
Open Scope N_scope.

Instance lt_well_founded : WellFounded lt := Acc_intro_generator 100 lt_wf_0.

(* Ltac Init.hidebody H ::= idtac. *)

Equations? f (a : N) : N by wf a lt :=
  f N0 := 0;
  f (pos n) := succ (f (pred_N n)).
Proof. lia. Qed.

Compute f 42.
