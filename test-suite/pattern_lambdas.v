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


Equations(noind) f' (n : nat) : nat :=
  f' n := test n (#{ | 0 => true ;
                     | S n => false }).




Definition pattern_lambda {A} (x : A) := x.

Notation "'λ' ' x" := (pattern_lambda (fun 'x => x)) (at level 0, x pattern).




Equations decideeq (b b' : bool) : (b = b') + (~ b = b') :=
  decideeq true true := inl eq_refl;
  decideeq false false := inl eq_refl;
  decideeq false true := inr _;
  decideeq true false := inr _.


_≟_ : Decidable {A = Bool} _≡_
true  ≟ true  = yes refl
false ≟ false = yes refl
true  ≟ false = no λ ()
false ≟ true  = no λ ()
