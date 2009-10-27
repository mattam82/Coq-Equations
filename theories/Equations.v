(* -*- coq-prog-name: "~/research/coq/trunk/bin/coqtop.byte"; coq-prog-args: ("-emacs-U"); compile-command: "make -C ../.. TIME='time'" -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** The set of libraries required to run Equations with all features. *)

Require Import Coq.Program.Program.
Require Export Coq.Program.Equality.

Require Export Equations.Init.
Require Import Equations.NoConfusion Equations.FunctionalInduction.
Require Export Equations.Below Equations.Subterm.
