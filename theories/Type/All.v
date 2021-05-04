(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations using an equality in Type
    with all features. *)

Set Warnings "-notation-overridden".

Require Export Equations.Type.Loader.
Require Export Equations.Type.Telescopes.
Require Export Equations.Type.WellFoundedInstances.

Global Obligation Tactic := Equations.CoreTactics.equations_simpl.

(** Tactic to solve well-founded proof obligations by default *)

Ltac solve_rec := simpl in * ; cbv zeta ; intros ;
  try typeclasses eauto with subterm_relation Below rec_decision.

Export EquationsNotations.
Open Scope equations_scope.