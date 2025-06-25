From Equations Require Import Equations.

Section test_equation.

Context {A : Type} (f : A -> option A) {lt : A -> A -> Prop}
 `{WellFounded A lt}.

Hypothesis decr_f : forall n p, f n = Some p -> lt p n.

(* An example using the "eqn:" notation in equations. *)

Equations f_sequence (n : A) : list A by wf n lt :=
  f_sequence n with inspect (f n) := {
    | Some p eqn: eq1 => p :: f_sequence p;
    | None eqn:_ => List.nil
    }.

End test_equation.

(* An example using destruct with eqn: *)

Goal forall b, negb b = true -> True.
Proof.
intros b nbeq.
destruct (negb b) eqn:nbv.
easy.
easy.
Qed.
