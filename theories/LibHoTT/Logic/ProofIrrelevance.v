(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This defines the functor that build consequences of proof-irrelevance *)

Require Export Coq.Logic.EqdepFacts.
Require Import HoTT.Basics.Overture.

Module Type ProofIrrelevance.

  Axiom proof_irrelevance : forall (P:Type) (p1 p2:P), p1 = p2.

End ProofIrrelevance.

Module ProofIrrelevanceTheory' (M:ProofIrrelevance).

  (** Proof-irrelevance implies uniqueness of reflexivity proofs *)

  Module Eq_rect_eq.
    Lemma eq_rect_eq :
      forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
        x = paths_ind p (fun a _ => Q a) x p h.
    Proof.
      intros; rewrite M.proof_irrelevance with (p1:=h) (p2:=idpath p).
      reflexivity.
    Qed.
  End Eq_rect_eq.

  (** Export the theory of injective dependent elimination *)

  Module EqdepTheory := EqdepTheory(Eq_rect_eq).
  Export EqdepTheory.

  Scheme eq_indd := Induction for paths Sort Type.

  (** We derive the irrelevance of the membership property for subsets *)

  Lemma subset_eq_compat :
    forall (U:Type) (P:U->Type) (x y:U) (p:P x) (q:P y),
      x = y -> exist P x p = exist P y q.
  Proof.
    intros U P x y p q H.
    rewrite M.proof_irrelevance with (p1:=q) (p2:=paths_ind x (fun a _ => P a) p y H).
    elim H using eq_indd.
    reflexivity.
  Qed.

  Lemma subsetT_eq_compat :
    forall (U:Type) (P:U->Type) (x y:U) (p:P x) (q:P y),
      x = y -> existT P x p = existT P y q.
  Proof.
    intros U P x y p q H.
    rewrite M.proof_irrelevance with (p1:=q) (p2:=paths_ind x (fun a _ => P a) p y H).
    elim H using eq_indd.
    reflexivity.
  Qed.

End ProofIrrelevanceTheory'.


(* /\ ProofIrrelevanceFacts /\ *)


(* \/ ProofIrrelevance \/ *)


(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** This file axiomatizes proof-irrelevance and derives some consequences *)

(*Require Import ProofIrrelevanceFacts.*)

Axiom proof_irrelevance : forall (P:Type) (p1 p2:P), p1 = p2.

Module PI. Definition proof_irrelevance := proof_irrelevance. End PI.

Module ProofIrrelevanceTheory := ProofIrrelevanceTheory'(PI).
Export ProofIrrelevanceTheory.
