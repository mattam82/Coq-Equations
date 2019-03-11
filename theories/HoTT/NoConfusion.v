(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Instances of [NoConfusion] for the standard datatypes. To be used by 
   [equations] when it needs applications of injectivity or discrimination
   on some equation. *)

Set Warnings "-notation-overridden".

From Equations Require Import Init Signature.
Require Import Equations.Tactics.
Require Import Equations.HoTT.Logic Equations.HoTT.Classes Equations.HoTT.EqDec Equations.HoTT.Constants.
Require Import Equations.HoTT.DepElim Equations.HoTT.Tactics.

(** Parameterized inductive types just need NoConfusion. *)

Instance Bool_depelim : DependentEliminationPackage Bool.Bool :=
  { elim := @Bool.Bool_ind }.

Derive NoConfusion for Unit Bool.Bool nat option sum Datatypes.prod list sigT.

(* FIXME should be done by the derive command *)
Extraction Inline noConfusion NoConfusionPackage_nat.
