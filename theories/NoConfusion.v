(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Instances of [NoConfusion] for the standard datatypes. To be used by 
   [equations] when it needs applications of injectivity or discrimination
   on some equation. *)

Require Import Coq.Program.Program Bvector List.
Require Export Equations.DepElim.

Ltac noconf H ::=
  blocked ltac:(noconf_ref H; simplify_dep_elim) ; auto 3.

(** Used by the [Derive NoConfusion] command. *)

Ltac solve_noconf := 
  simplify_dep_elim ; on_last_hyp ltac:(fun id => depelim id) ;
  red ; let H := fresh in intro H ; apply H ; reflexivity.

Derive NoConfusion for unit bool nat option sum prod list sigT sig.

(* FIXME should be done by the derive command *)
Extraction Inline noConfusion noConfusion_nat NoConfusionPackage_nat.


