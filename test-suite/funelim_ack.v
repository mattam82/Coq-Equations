
From Equations Require Import CoreTactics.
From Equations.Prop Require Import DepElim.
From Equations.Prop Require Import Equations.
Set Equations Transparent.
Equations ack (m n : nat) : nat by wf (m, n) (Equations.Prop.Subterm.lexprod _ _ lt lt) :=
ack 0 n := S n;
ack (S m) 0     := ack m 1;
ack (S m) (S n) := ack m (ack (S m) n).

Definition ack_incr {m n} : ack m n < ack m (n+1).
Proof.
  (* Was looping due to trying to reduce in the equality hypothesis *)
  funelim (ack m n) eqack. 
Admitted.