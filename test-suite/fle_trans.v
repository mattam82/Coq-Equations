(** printing NoConfusion %\coqdocind{NoConfusion}% *)
(** printing elimination %\coqdoctac{elimination}% *)
(** printing Derive %\coqdockw{Derive}% *)
(* begin hide *)
From Equations Require Import Equations.

Set Implicit Arguments.

Inductive fin : nat -> Set :=
| fz : forall n, fin (S n)
| fs : forall n, fin n -> fin (S n).
Arguments fz [_].
(* end hide *)
(** We define $\le$ by $\cstr{fz} \le i$ and $i \le j "->" \cstr{fs}\ i \le \cstr{fs}\ j$. *)

Inductive fle : forall n, fin n -> fin n -> Set :=
| flez : forall n (j : fin (S n)), fle fz j | fles : forall n (i j : fin (S n)), fle i j -> fle (fs i) (fs j).

(** We will need a NoConfusion principle for [fin], which we derive automatically,
    see section %\ref{sec:derive-noconf}%. *)

Derive Signature NoConfusionHom for fin.

(** We could prove the transitivity of the relation [fle]
    by defining a recursive function with %\Equations%, but here we will
    instead define a [Fixpoint] and use our [dependent elimination] tactic: *)

Fixpoint fle_trans {n : nat} {i j k : fin n} (p : fle i j) (q : fle j k) : fle i k.
(** We use the [dependent elimination] tactic to eliminate [p],
    providing a pattern for each case. We could also let %\Equations%
    generate names for the bound variables. *)

  dependent elimination p as [flez _ | @fles n i j p] ; [ apply flez | ].

  (** We know that [q] has type [fle (fs _) k]. Therefore, it
      cannot be [flez] and we must only provide one pattern for the single
      relevant branch, using: *)
dependent elimination q as [fles q].
  (** The end of the proof is straightforward. *)
(* begin hide *)
  apply fles. apply fle_trans with (1 := p) (2 := q).
Qed.
(* end hide *)
(** We can check that this definition does not make use of any axiom,
    contrary to what we would obtain by using [dependent destruction]
    from Coq's standard library. *)
(* begin hide *)
Print Assumptions fle_trans.

(**
  %\texttt{Closed under the global context}%
*)
(* end hide *)
Require Import Program.
(* begin hide *)
Fixpoint fle_trans' {n : nat} {i j k : fin n}
  (p : fle i j) (q : fle j k) : fle i k.
Proof.
  dependent destruction p.
  - apply flez.
  - dependent destruction q.
    apply fles. apply fle_trans with (1 := p) (2 := q).
Qed.

Print Assumptions fle_trans'.
(*
  Axioms:
  JMeq_eq : forall (A : Type) (x y : A), x ~= y -> x = y
*)
(* end hide *)
