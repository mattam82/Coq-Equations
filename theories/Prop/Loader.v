(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

From Corelib Require Import Extraction.

(** This exports tactics *)
Declare ML Module "rocq-equations.plugin".

From Equations Require Export Init Signature.
From Equations Require Import CoreTactics.
Require Export Equations.Prop.SigmaNotations.
Require Export Equations.Prop.Classes.
From Equations.Prop Require Import DepElim Constants.
Require Export Equations.Prop.EqDec.
Require Export Equations.Prop.EqDecInstances.
Require Export Equations.Prop.NoConfusion Equations.Prop.Subterm.
Require Export Equations.Prop.Tactics.
Require Export Equations.Prop.FunctionalInduction. (* funelim tactic *)

Export EquationsNotations.