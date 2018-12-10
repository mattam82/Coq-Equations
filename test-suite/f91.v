(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Program. 
Require Import Equations Bvector List.
Require Import Relations.
Require Import DepElimDec.
Require Import Subterm.

Require Import Arith Wf_nat.
Instance wf_nat : WellFounded lt := lt_wf.
Hint Resolve lt_n_Sn : Below.
Ltac rec ::= rec_wf_eqns.

Definition measure {A B} (f : A -> B) (R : relation B) : relation A :=
  fun x y => R (f x) (f y).

Definition f91_rel : relation nat :=
  measure (fun x => 101 - x) lt.

Instance gt_bound_wf : WellFounded f91_rel.
Proof. red. red. intros.
Admitted.

Set Program Mode.
Equations f91 n : { m : nat | if le_lt_dec n 100 then m = 91 else m = n - 10 } by rec n f91_rel :=
f91 n with le_lt_dec n 100 := {
  | left H := f91 (f91 (n + 11)) ;
  | right H := (n - 10) }.

Require Import Omega.

Next Obligation. intros. do 2 red. try omega. Defined.
Next Obligation. intros. destruct f91. simpl. do 2 red.
  destruct_call le_lt_dec. subst. omega. subst. omega.
Defined.

Next Obligation. destruct_call f91; simpl.
  destruct_call f91. simpl in *. destruct le_lt_dec. subst. simpl in y. auto.
  subst x0. destruct le_lt_dec; auto.
  subst x. simpl. omega.
Defined.

(** MS: Bug, this should be derivable, but needs the user's proofs as hints (omega calls) *)
Next Obligation.
  intros.
  rec_wf_rel IH n f91_rel.
  simp f91. constructor. destruct le_lt_dec. constructor. intros. apply IH.
  do 2 red; omega.
  apply IH. do 2 red. destruct_call f91. simpl proj1_sig.
  destruct le_lt_dec; subst; repeat red; omega.
  constructor.
Defined.

Notation "( x &?) " := (exist _ x _).