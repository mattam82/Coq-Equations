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

Require Import Equations.EqDec.

Set Primitive Projections.
Record sigma {A : Type} {B : A -> Type} := sigmaI { pr1 : A; pr2 : B pr1 }.
Unset Primitive Projections.

Arguments sigma A B : clear implicits.
Notation " { x : A & y } " := (@sigma _ (fun x : A => y)).
Notation " { x : A & y } " := (@sigma _ (fun x : A => y)) : type_scope.
Notation " ( x ; y ) " := (@sigmaI _ _ x y).
Notation " x .1 " := (pr1 x) (at level 3).
Notation " x .2 " := (pr2 x) (at level 3).

(* Lemma sigma_eq_sigT_eq {A B} (x x' : A) (y : B x) (y' : B x') :  *)
(*   existT B x y = existT B x' y' -> *)
(*   sigmaI B x y = sigmaI B x' y'. *)
(* Proof. *)
(*   intros. *)
(*   change x with (pr1 (x; y)). *)
(*   change y with (pr2 (x; y)). *)
(*   change x' with (pr1 (x'; y')). *)
(*   change y' with (pr2 (x'; y')). *)
(*   set (foo := (x'; y')) in *.  *)
(*   simpl. destruct H. *)
  
Arguments sigmaI {A} B pr1 pr2.
Lemma inj_sigma2 (U : Type) (P : U -> Type) (p : U) (x y : P p) : sigmaI P p x = sigmaI P p y -> x = y.
Proof.
Admitted.

Lemma inj_right_sigma {A : Type} `{EqDec A} (x : A) (P : A -> Type) (y y' : P x) :
  (x; y) = (x; y') -> y = y'.
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
