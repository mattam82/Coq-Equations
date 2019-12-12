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

Require Import Coq.Program.Tactics Bvector List.
From Equations Require Import Init Signature.
Require Import Equations.CoreTactics.
Require Import Equations.Prop.Classes Equations.Prop.EqDec Equations.Prop.Constants.
Require Import Equations.Prop.DepElim Equations.Prop.Tactics.

(** Simple of parameterized inductive types just need NoConfusion. *)
Derive NoConfusion for unit bool nat option sum Datatypes.prod list sigT sig.

(* FIXME should be done by the derive command *)
Extraction Inline noConfusion NoConfusionPackage_nat.


