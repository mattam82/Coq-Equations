From Equations.Prop Require Import Equations.

Require Import List Program.Syntax Arith Lia.

Equations div2 (n : nat) : nat :=
  div2 0 := 0;
  div2 1 := 0;
  div2 (S (S n)) := S (div2 n).

Lemma div2_le : forall x, div2 x <= x.
Proof. intros x. funelim (div2 x); auto with arith. Defined.

Transparent div2.
Equations log_iter (fn : nat -> nat) (n : nat) : nat :=
  log_iter fn 0 := 0;
  log_iter fn 1 := 0;
  log_iter fn n := S (fn (div2 n)).
Transparent log_iter.
Equations iter {A} (n : nat) (f : A -> A) : A -> A :=
  iter 0 f x := x;
  iter (S n) f x := f (iter n f x).
Transparent iter.
Definition f_terminates {A} {B : A -> Type} (fn : (forall x : A, B x) -> (forall x : A, B x)) :=
  forall x : A, { y : B x | (exists p, forall k, p < k -> forall g : forall x : A, B x,
                                  iter k fn g x = y) }.

Lemma log_terminates : f_terminates log_iter.
Proof.
  intro.
  Subterm.rec_wf_rel IH x lt.
  destruct x. exists 0.  exists 0. intros. inversion H. simpl. reflexivity.
  simpl. reflexivity.
  destruct x. exists 0. exists 0. intros. inversion H; simpl; reflexivity.
  specialize (IH (div2 (S (S x)))). forward IH. simpl. auto using div2_le with arith.
  destruct IH as [y Hy].
  exists (S y). destruct Hy as [p Hp]. exists (S p). intros.
  destruct k. inversion H.
  simpl. rewrite Hp. auto. auto with arith.
Defined.

Definition log x := proj1_sig (log_terminates x).

Eval compute in log 109.

Equations? log' (n : nat) : nat by wf n lt :=
 log' 0 := 0;
 log' 1 := 0;
 log' n := S (log' (div2 n)).
Proof. subst n. simpl. auto using div2_le with arith. Defined.

