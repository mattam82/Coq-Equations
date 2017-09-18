(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

Require Import Coq.Program.Program.

(** This exports tactics *)
Declare ML Module "equations_plugin".

From Equations Require Import Init NoConfusion EqDecInstances.
From Equations Require Export Signature DepElim FunctionalInduction Below Subterm.
