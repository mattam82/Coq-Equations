Require Import Equations.
Require Import Arith.Lt.
Hint Resolve lt_n_Sn : rec_decision.
Hint Constructors lexprod : rec_decision.

Equations ack (p : nat * nat) : nat :=
ack p by rec p (lexprod _ _ lt lt) :=
ack (pair 0 n) := 1;
ack (pair (S m) 0) := ack (m, 1);
ack (pair (S m) (S n)) := ack (m, ack (S m, n)).

Extraction Inline ack_comp_proj.
Extraction ack.
