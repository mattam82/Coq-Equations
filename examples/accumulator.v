(* begin hide *)
(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
(* end hide *)
(** * Working with accumulators

  A standard pattern of functional programming involves writting
  tail-recursive versions of an algorithm using an accumulator (also
  called wrapper/worker), we show how Equations makes this pattern easy
  to express and reason about using where clauses, well-founded
  recursion and function eliminators. *)

From Equations Require Import Equations.
From Coq Require Import List Program.Syntax Arith Lia.
Import ListNotations.

(** ** Worker/wrapper

  The most standard example is an efficient implementation of list reversal.
  Instead of growing the stack by the size of the list, we accumulate a
  partially reverted list as a new argument of our function.

  We implement this using a [go] auxilliary function defined recursively
  and pattern matching on the list.
 *)
Equations rev_acc {A} (l : list A) : list A :=
  rev_acc l := go [] l

   where go : list A -> list A -> list A :=
         go acc [] := acc;
         go acc (hd :: tl) := go (hd :: acc) tl.

(** A typical issue with such accumulating functions is that one has to
    write lemmas in two versions, once about the internal [go] function
    and then on its wrapper. Using the functional elimination principle
    associated to [rev_acc], we can show both properties simultaneously. *)

Lemma rev_acc_eq : forall {A} (l : list A), rev_acc l = rev l.
Proof.
  (** We apply functional elimination on the [rev_acc l] call.
      The eliminator expects two predicates:
      one specifying the wrapper and another for the worker.
      For the wrapper, we give the expected final goal but for the worker
      we have to invent a kind of loop invariant: here that the result of
      the whole [go acc l] call is equal to [rev l ++ acc]. *)
  apply (rev_acc_elim (fun A l revaccl => revaccl = rev l)
                      (fun A _ acc l go_res => go_res = rev l ++ acc)); intros; simpl.
  (** Functional elimination provides us with the worker property for the
      initial [go [] l] call, i.e. that it is equal to [rev l ++ []], hence
      the proof: *)
  + now rewrite app_nil_r in H.
  (** For the worker proofs themselves, we use standard reasoning. *)
  + reflexivity.
  + now rewrite H, <- app_assoc.
Qed.

(** ** The worker/wrapper and well-founded recursion

  Sometimes the natural expression of an algorithm in the worker/wrapper
  pattern requires well-founded recursion: here we take an example
  algorithm from Haskell whose termination is justified by a measure.
  Note that the [worker] subprogram's termination measure and
  implementation depends on the enclosing [k] argument which is captured
  in the where clause.

 *)

Obligation Tactic := idtac.

Equations? isPrime (n : nat) : bool :=
  isPrime 0 := false;
  isPrime 1 := false;
  isPrime 2 := true;
  isPrime 3 := true;
  isPrime k := worker 2
    where worker (n' : nat) : bool by wf (k - n') lt :=
    worker n' with ge_dec n' k :=
      { | left H := true;
        | right H := if Nat.eqb (Nat.modulo k n') 0 then false else worker (S n') }.
Proof. lia. Defined.

(* Require Import ExtrOcamlBasic. *)
(* Extraction isPrime. *)

(** ** Programm equivalence with worker/wrappers

  Finally we show how the eliminator can be used to prove
  program equivalences involving a worker/wrapper definition.
  Here [indexes l] computes the list [0..|l|-1] of valid indexes in the
  list [l].
*)

Equations indexes : list nat -> list nat :=
  indexes l := go [] (length l)

  where go : list nat -> nat -> list nat :=
  go acc 0     := acc;
  go acc (S n) := go (n :: acc) n.

(** Clearly, all indexes in the resulting list should be smaller than [length l]: *)
Lemma indexes_spec (l : list nat) : Forall (fun x => x < length l) (indexes l).
Proof.
  (** We apply the eliminator, giving a predicate that specifies
      preservation of the property from the accumulator to the end
      result for [go]'s specification. The rest of the proof uses simple reasoning. *)
  apply (indexes_elim (fun l indexesl => Forall (fun x => x < length l) indexesl)
        (fun l acc n indexesl => n <= length l ->
           Forall (fun x => x < length l) acc ->
           Forall (fun x => x < length l) indexesl));
    clear l; intros.
  + apply H; constructor.
  + apply H0.
  + apply H. lia. constructor. lia. apply H1.
Qed.

(** Using well-founded recursion we can also define an [interval x y]
    function producing the interval [x..y-1] *)

Equations? interval x y : list nat by wf (y - x) lt :=
  interval x y with lt_dec x y :=
    { | left  ltxy  => x :: interval (S x) y;
      | right nltxy => [] }.
Proof. lia. Defined.

(** We prove a simple lemmas on [interval]: *)
Lemma interval_large x y : ~ x < y -> interval x y = [].
Proof. funelim (interval x y); clear Heq; intros; now try lia. Qed.

(** One can show that [indexes l] produces the interval [0..|l|-1] using [indexes_elim].
    The recursion invariant for [indexes_go] records that [acc] corresponds to a partial
    interval [n..|l|-1] during the computation, and is finally completed into [0..|l|-1]
    by the end of the computation. We use the previous lemmas as helpers.
 *)
Lemma indexes_interval l : indexes l = interval 0 (length l).
Proof.
  set (P := fun start (l indexesl : list nat) => indexesl = interval start (length l)).
  revert l.
  apply (indexes_elim (P 0)
          (fun l acc n indexesl =>
             n <= length l ->
             P n l acc -> P 0 l indexesl)); subst P; simpl.
  intros l.
  + intros H. apply H; auto. rewrite interval_large; trivial; lia.
  + intros; trivial.
  + intros l ? n H Hn ->. apply H. lia.
    rewrite (interval_equation_1 n).
    destruct lt_dec. reflexivity. elim n0. lia.
Qed.
