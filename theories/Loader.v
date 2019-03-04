(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

Require Import Extraction.

(** This exports tactics *)
Declare ML Module "equations_plugin".

From Equations Require Import Init Signature.
Require Export Equations.Prop.Classes.
Require Import Equations.Prop.DepElim Equations.Prop.Constants.
Require Import FunctionalInduction Below.
From Equations Require Export EqDecInstances HSetInstances.
From Equations.Prop Require Import NoConfusion Subterm (* DepElimDec *).

Export Inaccessible_Notations.