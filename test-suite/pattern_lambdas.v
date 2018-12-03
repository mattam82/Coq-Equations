(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
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
  f' n := test n (#{ | 0 => true ;
                     | S n => false }).

Equations decideeq (b b' : bool) : (b = b') + (~ b = b') :=
  decideeq true true := inl eq_refl;
  decideeq false false := inl eq_refl;
  decideeq false true := inr (#{ | x :=! x });
  decideeq true false := inr (#{ | x :=! x }).

