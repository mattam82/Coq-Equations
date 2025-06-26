(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** The set of libraries required to run Equations with all features. *)

Require Export Equations.Prop.Loader.
Require Import Equations.Prop.Telescopes.

#[export] Existing Instance wf_tele_measure.

Require Import Program.Tactics.

(* program_solve_wf launches auto on well-founded and propositional (i.e. in Prop) goals *)

Global Obligation Tactic := simpl in *; program_simplify; Equations.CoreTactics.equations_simpl;
                              try program_solve_wf.

(** Tactic to solve well-founded proof obligations by default *)

Definition inspect {A} (a : A) : {b | a = b} :=
  exist _ a eq_refl.

Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).

Ltac solve_rec := simpl in * ; cbv zeta ; intros ;
  try typeclasses eauto with subterm_relation simp rec_decision.

Open Scope equations_scope.
