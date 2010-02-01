(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Signatures for dependent types. 
   
   A signature for [A] is a sigma-type in which any [A] 
   can be packed. *)

(*i $Id$ i*)

Class Signature (fam : Type) (signature_index : Type) := {
  signature : signature_index -> Type ;
  signature_pack : fam -> { i : signature_index & signature i }
}.

Notation " x ~=~ y " := (signature_pack x = signature_pack y) (at level 90).

