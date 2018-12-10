(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.
Require Import Arith.
Require Import Omega.
From Equations Require Import Equations.
Require Import Wellfounded Relation_Definitions.
Require Import Relation_Operators Lexicographic_Product Wf_nat.
Unset Implicit Arguments.
Require Import Program.

Definition MR {A B} (f : A -> B) (R : relation B) : relation A :=
  fun x y => R (f x) (f y).

Equations test (n : nat) (pre : n >= 0 ) : { n' : nat | n' <= n }
 by rec n lt :=
test 0 p := exist _ 0 _;
test (S n) p with test n _ => {
                | exist _ 0 _ := exist _ 0 _;
                | exist _ (S n') p' with test n' _ := {
                                                  | exist _ k p'' := exist _ k _ } }.

Next Obligation. auto with arith. Defined.
Next Obligation. auto with arith. Defined.
Solve Obligations with program_simpl; omega.
Solve Obligations.

Module Bug.
  Equations(noind) test' (n : { n : nat | n >= 0 }) : { n' : nat | n' <= `n }
  by rec n (MR (@proj1_sig nat (fun x : nat => x >= 0)) lt) :=
  test' (exist _ n p) with n := {
  | 0 := exist _ 0 _;
  | S n' with test' (exist _ n' _) => {
                  | exist _ 0 _ := exist _ 0 _;
                  | exist _ (S n'') p' with test' (exist _ n'' _) := {
                      | exist _ k p'' := exist _ k _ } } }.
Next Obligation.
  auto with arith.
Defined.

Next Obligation.
  red. simpl. intros. simpl.
  auto with arith.
Defined.

Next Obligation.
  intros. red. simpl.
  auto with arith.
Defined.

Next Obligation.
  red; simpl; eauto with arith; omega.
Defined.

Next Obligation.
  simpl; eauto with arith; omega.
Defined.

End Bug.