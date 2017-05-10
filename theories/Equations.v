(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

Require Import Coq.Program.Program.

Require Export Equations.Init Equations.Signature Equations.DepElim.
Require Export Equations.NoConfusion Equations.EqDecInstances
        Equations.FunctionalInduction.
Require Export Equations.Below Equations.Subterm.
