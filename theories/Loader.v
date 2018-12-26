(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

Require Import Extraction.

(** This exports tactics *)
Declare ML Module "equations_plugin".

From Equations Require Export Classes Signature DepElim FunctionalInduction Below Constants.
From Equations Require Export EqDecInstances HSetInstances.
From Equations Require Import Init NoConfusion Subterm DepElimDec.
From Coq Require Export Program.Utils Program.Wf FunctionalExtensionality ProofIrrelevance.

Export Inaccessible_Notations.