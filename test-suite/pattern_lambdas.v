(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations Require Import Equations.

Variable test : forall n : nat, (nat -> bool) -> nat.

Equations f : nat -> nat :=
  f 0 := 0;
  f (S n) := f n.

Equations f' (n : nat) : nat :=
  f' n := test n (λ{ | 0 => true ;
                     | S n => false }).

Definition foo (x : nat) :=
  f' match x with 0 => 0 | S x => 0 end.

Equations decideeq (b b' : bool) : (b = b') + (~ b = b') :=
  decideeq true true   => inl eq_refl;
  decideeq false false => inl eq_refl;
  decideeq false true  => inr (λ{ | ! });
  decideeq true false  => inr (λ{ | ! }).
