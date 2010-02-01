(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Equations.Signature Equations.DepElim.

(** Alternative implementation of generalization using sigma types only,
   allowing to use K on decidable domains. *)

(** Decompose existential packages. *)

Ltac decompose_exists id :=
  match type of id with
    | { x : _ & _ } => let xn := fresh x in 
      destruct id as [xn id]; decompose_exists xn; 
        decompose_exists id
    | _ => idtac
  end.

(** Dependent generalization using existentials only. *)

Ltac generalize_sig id :=
  let id' := fresh id in
  get_signature_pack id id';
  let idp := eval cbv in id' in
  generalize (@eq_refl _ idp : idp = id') ;
  clearbody id'; move id' at top ;
  revert_until id'; rename id' into id ;
    decompose_exists id.

Ltac generalize_eqs_sig id :=
  (needs_generalization id ; generalize_sig id) || idtac.

Ltac generalize_eqs_vars_sig id :=
  generalize_eqs_sig id.

Ltac generalize_by_eqs id ::= generalize_eqs_sig id.
Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars_sig id.
