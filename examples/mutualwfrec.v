(* begin hide *)
(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations Require Import Equations.
From Coq Require Import List Program.Syntax Arith Lia.
Require Import List Wellfounded.
(* end hide *)
(** * Mutual well-founded recursion using dependent pattern-matching

  We present a simple encoding of mutual recursion through the use of
  dependent pattern-matching on a GADT-like representation of the functions
  prototypes. We use a simple toy measure here to justify termination,
  but more elaborate well-founded relations can be used as well.
 *)

Set Equations Transparent.

(** Use nice notations for sigma types *)
Notation "{ x : A & y }" := (@sigma A (fun x : A => y)%type) (x at level 99) : type_scope.
Notation "{ x & y }" := (@sigma _ (fun x : _ => y)%type) (x at level 99) : type_scope.
Notation "&( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
    (right associativity, at level 4,
     format "&( x ,  .. ,  y  ,  z )").

(** We first declare the prototypes ouf our mutual definitions. *)
Set Universe Polymorphism.
Inductive ty : forall (A : Type) (P : A -> Type), Set :=
| ty0 : ty nat (fun _ => nat)
| ty1 : ty (list nat) (fun _ => bool).
Derive Signature NoConfusion for ty.

(** Our measure is simple, just the natural number or length of the list argument. *)
Equations measure : {A &{ P &{ _ : A & ty A P }}} -> nat :=
  measure &(_, _, a, ty0) => a;
  measure &(_, _, a, ty1) => length a.

Definition rel := MR lt measure.

Instance: WellFounded rel.
Proof.
  red. apply measure_wf. apply Wf_nat.lt_wf.
Defined.

Definition pack {A} {P} (x : A) (t : ty A P) := (&(A, P, x, t)) : {A & {P & {_ : A & ty A P}}}.

(** We define the function by recursion on the abstract packed argument.
    Using dependent pattern matching, the clauses for [ty0] refine the argument
    and return type to [nat] and similarly for [ty1], we can hence do pattern-matching
    as usual on each separate definition. *)
Equations? double_fn {A} {P} (t : ty A P) (x : A) : P x by wf (pack x t) rel :=
  double_fn ty0 n := n + 0;
  double_fn ty1 nil := true;
  double_fn ty1 (x :: xs) := 0 <? length xs + double_fn ty0 (length xs).
(** It is easily shown terminating in this case. *)
Proof. red. red. cbn. auto with arith. Qed.

(** We can define auxilliary definition to select the functions we want and express unfolding
    lemmas in terms of these abbreviations. *)
Definition fn0 := double_fn ty0.
Definition fn1 := double_fn ty1.

Lemma fn0_unfold n : fn0 n = n + 0.
Proof.
  unfold fn0. simp double_fn.
Qed.

Lemma fn1_unfold l : fn1 l = match l with nil => true | x :: xs => 0 <? length xs + fn0 (length xs) end.
Proof.
  unfold fn1; simp double_fn. destruct l. simp double_fn. simp double_fn.
Qed.
