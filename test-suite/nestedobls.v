(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Set Asymmetric Patterns.
Set Implicit Arguments.
Unset Strict Implicit.
Require Import Arith.
Require Import Omega.
From Equations Require Import Equations Telescopes.
Require Import Wellfounded Relation_Definitions.
Require Import Relation_Operators Lexicographic_Product Wf_nat.
Unset Implicit Arguments.
Require Import Program.

Equations? test (n : nat) (pre : n >= 0 ) : { n' : nat | n' <= n }
 by wf n lt :=
test 0 p := exist _ 0 _;
test (S n) p with test n _ => {
                | exist _ 0 _ := exist _ 0 _;
                | exist _ (S n') p' with test n' _ := {
                                                  | exist _ k p'' := exist _ k _ } }.
Proof. all:(auto with arith; omega). Defined.

Module Bug.
  (* FIXME: shrink obligations so that they can apply during induction principle generation *)
  Equations?(noind) test' (n : { n : nat | n >= 0 }) : { n' : nat | n' <= `n }
  by wf (proj1_sig n) lt :=
  test' (exist _ n p) with n := {
  | 0 := exist _ 0 _;
  | S n' with test' (exist _ n' _) => {
                  | exist _ 0 _ := exist _ 0 _;
                  | exist _ (S n'') p' with test' (exist _ n'' _) := {
                      | exist _ k p'' := exist _ k _ } } }.
  Proof. all:(clear test'; unfold MR; simpl; auto with arith). omega. Defined.

End Bug.