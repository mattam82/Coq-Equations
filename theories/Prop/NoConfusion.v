(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Instances of [NoConfusion] for the standard datatypes. To be used by 
   [equations] when it needs applications of injectivity or discrimination
   on some equation. *)

Set Warnings "-deprecated-since-8.20".   
From Corelib Require Import Program.Tactics ListDef.
Set Warnings "deprecated-since-8.20".
From Equations Require Import Init Signature.
From Equations Require Import CoreTactics.
From Equations.Prop Require Import Classes EqDec Constants.
From Equations.Prop Require Import DepElim Tactics.

(** Simple of parameterized inductive types just need NoConfusion. *)
Derive NoConfusion for unit bool nat option sum Datatypes.prod list sigT sig.

(* FIXME should be done by the derive command *)
Extraction Inline noConfusion NoConfusionPackage_nat.


