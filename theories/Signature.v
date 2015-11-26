(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Signatures for dependent types. 
   
   A signature for [A] is a sigma-type in which any [A] 
   can be packed. *)

From Equations Require Import Init EqDec.
  
Lemma inj_sigma2 (U : Type) (P : U -> Type) (p : U) (x y : P p) :
  sigmaI P p x = sigmaI P p y -> x = y.
Proof.
Admitted.

Ltac destruct_one_sigma :=
  match goal with
  | [ H : @sigma _ _ |- _ ] => let ph := fresh "H" in destruct H as [H ph]
  end.
Ltac simp_sigmas := repeat destruct_one_sigma.

Class Signature (fam : Type) (signature_index : Type) := {
  signature : signature_index -> Type ;
  signature_pack : fam -> sigma _ signature
}.

Notation " x ~=~ y " := (signature_pack x = signature_pack y) (at level 90).

Notation " '(' x '&' y ')' " := (existT _ x y) : equations. 
