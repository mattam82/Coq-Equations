(* begin hide *)
(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations.Prop Require Import Equations.
From Stdlib Require Import List Syntax Arith Lia.
From Stdlib Require Import List.
Import ListNotations.
(* end hide *)
(** * Well-founded recursion

  Equations provide support for well-founded recursion, potentially nested and mutual.

  Here we show a standard example of the [nubBy] function from Haskell's prelude,
  which is naturally expressed using well-founded recursion on the length of the list.
  To show this, we however use the argument that [filter f l] always returns a sublist of [l].
 *)

Equations filter_length {A} (l : list A) (f : A -> bool) : length (filter f l) <= length l :=
 filter_length [] f := le_n 0;
 filter_length (x :: xs) f with f x :=
                         { | true => le_n_S _ _ (filter_length xs f);
                           | false => le_S _ _ (filter_length xs f) }.

Section nubBy.
  Context {A} (eq : A -> A -> bool).

  (** The proof that this function is well-founded uses simply the lemma [filter_length] and
      standard arithmetic reasoning. *)
  Equations? nubBy (l : list A) : list A by wf (length l) lt :=
  nubBy []        => [];
  nubBy (x :: xs) => x :: nubBy (filter (fun y => negb (eq x y)) xs).
  Proof. simpl. auto using filter_length with arith. Defined.
End nubBy.

(** Using functional elimination, we can show standard properties of [nubBy], without having
    to repeat the well-founded induction principle *)

Lemma nubBy_length {A} (eq : A -> A -> bool) (l : list A) : length (nubBy eq l) <= length l.
Proof.
  funelim (nubBy eq l); simpl; trivial.
  rewrite filter_length in H. auto with arith.
Qed.

Lemma In_filter {A} (f : A -> bool) (l : list A) a : In a (filter f l) -> In a l /\ f a = true.
Proof.
  induction l; simpl. intros [].
  destruct (f a0) eqn:Heq.
  simpl. intuition auto. now subst a0.
  intuition auto.
Qed.

Lemma In_nubBy {A} (eq : A -> A -> bool) (l : list A) (a : A) :
  In a (nubBy eq l) -> In a l.
Proof.
  funelim (nubBy eq l).
  + trivial.
  + intros H0.
    destruct H0 as [->|H0]; auto. simpl. auto.
    specialize (H _ H0). apply In_filter in H as [Inal eqa]. right; auto.
Qed.

(** This allows to show that [nubBy] returns a list without duplicates in a few
    lines of proof. *)
Lemma nuBy_nodup {A} (eq : A -> A -> bool) (l : list A) :
  (forall x y, (eq x y = true) <-> (x = y)) -> NoDup (nubBy eq l).
Proof.
  funelim (nubBy eq l). constructor. intros Heq; specialize (H Heq).
  constructor. intros Hi. apply In_nubBy, In_filter in Hi as [_ eqaa].
  specialize (Heq x x). destruct (eq x x). discriminate.
  destruct (proj2 Heq). reflexivity. discriminate.
  auto.
Qed.

Equations ack (m n : nat) : nat by wf (m, n) (Equations.Prop.Subterm.lexprod _ _ lt lt) :=
  ack 0 0         := 1;
  ack 0 (S n)     := S (S n);
  ack (S m) 0     := ack m 1;
  ack (S m) (S n) := ack m (ack (S m) n).
