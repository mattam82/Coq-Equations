(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Export Unicode.Utf8_core.
Require Export Coq.Program.Program.

Declare ML Module "equations_plugin".

(** The sigma type used by Equations. *)

Set Primitive Projections.
Record sigma {A : Type} {B : A -> Type} : Type := sigmaI { pr1 : A; pr2 : B pr1 }.
Unset Primitive Projections.

Arguments sigma A B : clear implicits.
Arguments sigmaI {A} B pr1 pr2.

Notation " { x : A & y } " := (@sigma _ (fun x : A => y)).
Notation " { x : A & y } " := (@sigma _ (fun x : A => y)) : type_scope.
Notation " ( x ; y ) " := (@sigmaI _ _ x y).
Notation " x .1 " := (pr1 x) (at level 3).
Notation " x .2 " := (pr2 x) (at level 3).

