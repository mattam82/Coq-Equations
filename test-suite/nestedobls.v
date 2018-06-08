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

Definition MR {A B} (f : A -> B) (R : relation B) : relation A :=
  fun x y => R (f x) (f y).

Equations test (n : nat) (pre : n >= 0 ) : { n' : nat | n' <= n } :=
test n p by rec n lt :=
test 0 p := exist _ 0 _;
test (S n) p <= test n _ => {
                | exist 0 _ := exist _ 0 _;
                | exist (S n') p' with test n' _ := {
                                                  | exist k p'' := exist _ k _ } }.

Next Obligation. auto with arith. Defined.
Next Obligation. auto with arith. Defined.
Next Obligation. auto with arith. Defined.
Next Obligation. auto with arith. Defined.
Solve Obligations with program_simpl; omega.
Solve Obligations.

Module Bug.
  
Equations(noind) test' (n : { n : nat | n >= 0 }) : { n' : nat | n' <= `n } :=
test' n by rec n (MR (@proj1_sig nat (fun x : nat => x >= 0)) lt) :=
test' (exist n p) with n := {
  | 0 := exist _ 0 _;
  | S n' <= test' (exist _ n' _) => {
                  | exist 0 _ := exist _ 0 _;
                  | exist (S n'') p' with test' (exist _ n'' _) := {
                      | exist k p'' := exist _ k _ } } }.
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
  red; simpl; auto with arith.
Defined.

Next Obligation.
  omega.
Defined.

End Bug.