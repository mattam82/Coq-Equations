From Equations Require Import Equations.

Tactic Notation "delim" constr(c) "as" elim_patterns_or_var(p) :=
  dependent elimination c as p.

Tactic Notation "==>" elim_patterns_or_var(p) :=
  let H := fresh in intros H; dependent elimination H as p.

Inductive fin : nat -> Set :=
 | fin0 n : fin (S n)
 | finS n : fin n -> fin (S n).

Lemma foo : forall n, fin n -> fin n.
Proof.
  intros n f; delim f as [fin0 k|finS k f'].
  - exact (fin0 k).
  - exact (finS k f').
Qed.

Lemma bar : forall n, fin n -> fin n.
Proof.
  intros n; ==> [fin0 k|finS k f'].
  - exact (fin0 k).
  - exact (finS k f').
Qed.

(* Fix name clash bug **)
Inductive test := 
| testi (foo : nat).

Lemma global_clash : test -> nat.
Proof.
  ==> [testi foo].
  pose (baz:= custom_depelim.foo).
  exact foo.
Qed.

Lemma elim_nat : nat -> nat.
Proof.
  ==> [0 | S x].
  - exact 0.
  - exact (S x).
Qed.








