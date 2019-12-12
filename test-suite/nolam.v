(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2018 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Program Bvector List Relations.
From Equations Require Import Equations Signature.
Require Import Utf8.

Equations f : forall {A : Type}, list A -> nat :=
  f [] := 0;
  f (_ :: tl) := S (f tl).
