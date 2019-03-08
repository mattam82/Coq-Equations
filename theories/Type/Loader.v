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

Set Warnings "-notation-overridden".
From Equations Require Export Init Signature.
Require Import Equations.Tactics.
Require Export Equations.Type.Logic Equations.Type.Classes.
Require Import Equations.Type.WellFounded.
Require Import Equations.Type.DepElim Equations.Type.EqDec Equations.Type.Constants.
Require Export Equations.Type.EqDecInstances.
Require Import Equations.Type.NoConfusion.
Require Export Equations.Type.Tactics.
Require Export Equations.Type.FunctionalInduction. (* funelim tactic *)

Global Obligation Tactic := Equations.Tactics.equations_simpl.

(** Tactic to solve well-founded proof obligations by default *)

Ltac solve_rec := simpl in * ; cbv zeta ; intros ;
  try typeclasses eauto with subterm_relation Below rec_decision.

Export Inaccessible_Notations.