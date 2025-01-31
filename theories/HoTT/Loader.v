(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

(** This exports tactics *)

Set Warnings "-notation-overridden".
From Equations Require Export Init Signature.
From Equations Require Import CoreTactics.
Require Export Equations.HoTT.Logic Equations.HoTT.Classes.
From Equations Require Import HoTT.WellFounded.
From Equations Require Import HoTT.DepElim Equations.HoTT.EqDec Equations.HoTT.Constants.
Require Export Equations.HoTT.EqDecInstances.
Require Export Equations.HoTT.NoConfusion.
From Equations Require Import HoTT.Subterm.
Require Export Equations.HoTT.Tactics.
Require Export Equations.HoTT.FunctionalInduction. (* funelim tactic *)

Global Obligation Tactic := Equations.CoreTactics.equations_simpl.

(** Tactic to solve well-founded proof obligations by default *)

Ltac solve_rec := simpl in * ; cbv zeta ; intros ;
  try typeclasses eauto with subterm_relation simp rec_decision.

Export EquationsNotations.
