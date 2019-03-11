(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

(** This exports tactics *)

Set Warnings "-notation-overridden".
From Equations Require Export Init Signature.
Require Import Equations.Tactics.
Require Export Equations.HoTT.Logic Equations.HoTT.Classes.
Require Import Equations.HoTT.WellFounded.
Require Import Equations.HoTT.DepElim Equations.HoTT.EqDec Equations.HoTT.Constants.
Require Export Equations.HoTT.EqDecInstances.
Require Import Equations.HoTT.NoConfusion.
Require Import Equations.HoTT.Subterm.
Require Export Equations.HoTT.Tactics.
Require Export Equations.HoTT.FunctionalInduction. (* funelim tactic *)

Global Obligation Tactic := Equations.Tactics.equations_simpl.

(** Tactic to solve well-founded proof obligations by default *)

Ltac solve_rec := simpl in * ; cbv zeta ; intros ;
  try typeclasses eauto with subterm_relation Below rec_decision.

Export Inaccessible_Notations.