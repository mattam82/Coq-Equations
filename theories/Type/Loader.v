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

Set Warnings "-notation-overridden".
From Equations Require Export Init Signature.
From Equations Require Import CoreTactics.
From Equations.Type Require Export Logic Classes.
From Equations.Type Require Import WellFounded.
From Equations.Type Require Import DepElim EqDec Constants.
From Equations.Type Require Export EqDecInstances.
From Equations.Type Require Import NoConfusion.
From Equations.Type Require Import Subterm.
Require Export Equations.Type.Tactics.
Require Export Equations.Type.FunctionalInduction. (* funelim tactic *)

Global Obligation Tactic := Equations.CoreTactics.equations_simpl.

(** Tactic to solve well-founded proof obligations by default *)

Ltac solve_rec := simpl in * ; cbv zeta ; intros ;
  try typeclasses eauto with subterm_relation simp rec_decision.

Export EquationsNotations.