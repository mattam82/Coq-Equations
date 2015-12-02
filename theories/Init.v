(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Export Coq.Unicode.Utf8_core.
Require Export Coq.Program.Program.

Declare ML Module "equations_plugin".

(** The sigma type used by Equations. *)

Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.
Global Unset Printing Primitive Projection Compatibility.
Polymorphic Record sigma {A : Type} {B : A -> Type} : Type := sigmaI { pr1 : A; pr2 : B pr1 }.
Unset Primitive Projections.

Arguments sigma A B : clear implicits.
Arguments sigmaI {A} B pr1 pr2.

Notation " { x : A & y } " := (@sigma _ (fun x : A => y)).
Notation " { x : A & y } " := (@sigma _ (fun x : A => y)) : type_scope.
Notation " ( x ; y ) " := (@sigmaI _ _ x y).
Notation " x .1 " := (pr1 x) (at level 3).
Notation " x .2 " := (pr2 x) (at level 3).

(** The polymorphic equality type used by Equations. *)

Set Universe Polymorphism.

Inductive Empty@{i} : Type@{i} :=.

Inductive Id@{i} (A : Type@{i}) (a : A) : A -> Type@{i} :=
  id_refl : Id A a a.

Module IdNotations.

  Notation " x = y " := (@Id _ x y).
  Notation " x = y " := (@Id _ x y) : type_scope.

  Notation " x <> y " := (@Id _ x y -> Empty).
  Notation " x <> y " := (@Id _ x y -> Empty) : type_scope.

  Notation " 1 " := (@id_refl _ _).

End IdNotations.

Section IdTheory.
  Universe i.
  Variable A : Type@{i}.

  Import IdNotations.
  
  Lemma id_sym (x y : A) : x = y -> y = x.
  Proof. destruct 1. apply 1. Defined.

  Lemma id_trans (x y z : A) : x = y -> y = z -> x = z.
  Proof. destruct 1. apply id. Defined.

End IdTheory.

(** Forward reference for the NoConfusion tactic. *)
Ltac noconf H := congruence || injection H; intros; subst.
