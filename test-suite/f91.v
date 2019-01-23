(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Program. 
Require Import Equations Bvector List.
Require Import Relations.
Require Import DepElimDec.
Require Import Subterm.
Require Import Omega.
Require Import Arith Wf_nat.

Instance wf_nat : WellFounded lt := lt_wf.
Hint Resolve lt_n_Sn : Below.

Definition f91_rel : relation nat :=
  MR lt (fun x => 101 - x).

Instance gt_bound_wf : WellFounded f91_rel.
Proof. red. unfold f91_rel. apply measure_wf. apply lt_wf. Defined.
Lemma f91_1 n : n <= 100 -> f91_rel (n + 11) n.
Proof. intros.
  - do 2 red; abstract omega.
Qed.

Lemma f91_2 :   forall (n : nat) (H : n <= 100)
    (f91 : forall x : nat, f91_rel x n -> {m : nat | if le_lt_dec x 100 then m = 91 else m = x - 10}),
  f91_rel (` (f91 (n + 11) (f91_1 n H))) n.
Proof.
  intros.
  - do 2 red; destruct f91; cbn [proj1_sig];
    destruct le_lt_dec; subst; abstract omega.
Defined.

Set Program Mode.

Equations f91 n : { m : nat | if le_lt_dec n 100 then m = 91 else m = n - 10 } by rec n f91_rel :=
f91 n with le_lt_dec n 100 := {
  | left H := f91 (f91 (n + 11)) ;
  | right H := (n - 10) }.
(* Proof. *)
(*   - apply (f91_1 _ H). *)
(*   - apply f91_2. *)
(*   - unfold f91_2. destruct f91; cbn [proj1_sig]; *)
(*     destruct f91; cbn [proj1_sig]; *)
(*     destruct le_lt_dec; subst; simpl in y0; auto; *)
(*     destruct le_lt_dec; subst; auto; omega. *)
(* Defined. *)

Next Obligation. red. now apply f91_1. Qed.
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
  intros. apply IH. auto.
  simp f91.
Defined.
