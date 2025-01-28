(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2018 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Stdlib Require Import List Relations.
From Equations Require Import Equations Signature.
From Stdlib Require Import Utf8.
Import ListNotations.

Equations f : forall {A : Type}, list A -> nat :=
  f [] := 0;
  f (_ :: tl) := S (f tl).
