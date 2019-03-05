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

From Equations Require Export Init Signature.
Require Import Equations.Tactics.
Require Export Equations.Prop.Classes.
Require Import Equations.Prop.DepElim Equations.Prop.EqDec Equations.Prop.Constants.
Require Import Below.
Require Export Equations.Prop.EqDecInstances.
Require Import Equations.Prop.NoConfusion Equations.Prop.Subterm.
Require Export Equations.Prop.Tactics.
Require Export Equations.Prop.FunctionalInduction. (* funelim tactic *)

Export Inaccessible_Notations.