(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

Require Export Equations.Prop.Loader.
Require Import Equations.Telescopes.

Require Import Program.Tactics.

(* program_solve_wf launches auto on well-founded and propositional (i.e. in Prop) goals *)

Global Obligation Tactic := program_simplify; Equations.Tactics.equations_simpl;
                              try program_solve_wf.

(** Tactic to solve well-founded proof obligations by default *)

Ltac solve_rec := simpl in * ; cbv zeta ; intros ;
  try typeclasses eauto with subterm_relation Below rec_decision.

Export Inaccessible_Notations.
Open Scope equations_scope.