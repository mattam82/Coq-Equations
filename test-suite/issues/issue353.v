Require Import Coq.Arith.Arith.
From Equations Require Import Equations.

Fixpoint Ack (n m : nat) : nat :=
match n with
| O => S m
| S p => let fix Ackn (m : nat) :=
match m with
| O => Ack p 1
| S q => Ack p (Ackn q)
end
in Ackn m
end.

Definition lex_nat (ab1 ab2 : nat * nat) : Prop :=
match ab1, ab2 with
| (a1, b1), (a2, b2) => (a1 < a2) \/ ((a1 = a2) /\ (b1 < b2))
end.
#[local] Hint Unfold lex_nat : rec_decision.
Lemma lex_nat_wf : well_founded lex_nat.
Admitted.

#[export]
Instance Lex_nat_wf : WellFounded lex_nat.
apply lex_nat_wf.
Defined.

(** Does not generate the induction principle *)
 
Module Alt.
Equations Ack (p : nat * nat) : nat by wf p lex_nat :=
Ack (0, n) := S n ;
Ack (S m, 0) := Ack (m, 1);
Ack (S m, S n) := Ack (m, Ack (S m, n)).
End Alt.

Module Alt2.
Equations Ack2 (p : nat * nat) : nat by wf p lex_nat :=
Ack2 (0, n) := S n ;
Ack2 (S m, 0) := Ack2 (m, 1);
Ack2 (S m, S n) := Ack2 (m, Ack2 (S m, n)).
End Alt2.

(* OK *)
