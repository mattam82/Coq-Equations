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
Require Import Lia.
Require Import Arith Wf_nat.

Set Program Mode.
Arguments minus : simpl never.

Ltac destruct_lt_dec :=
  match goal with
    [ H : le_lt_dec _ _ = _ |- _ ] => destruct H
  end.

Equations? f91 (n : nat) : { m : nat | if le_lt_dec n 100 then m = 91 else m = n - 10 } by wf (101 - n) lt :=
f91 n with le_lt_dec n 100 := {
  | left H := f91 (f91 (n + 11)) ;
  | right H := (n - 10) }.
Proof.
  all:hnf. 2-3:destruct f91; simpl. 3:destruct f91; simpl. 1:lia.
  all:repeat destruct le_lt_dec; lia.
(* FIXME slow because big proof terms are generated until the unfolding equation is proven *)
Defined.
