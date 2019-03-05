From Equations Require Import Init.
From Coq Require Import Extraction Relation_Definitions.

(** Notation for the single element of [x = x]. *)

Arguments eq_refl {A} {x}.

(** Depdent eliminators for proofs, not derived automatically by Coq. *)

Lemma False_rect_dep (P : False -> Type) : forall e : False, P e.
Proof. intros e. destruct e. Defined.

Lemma True_rect_dep (P : True -> Type) (m : P I) : forall e : True, P e.
Proof. intros e. destruct e. exact m. Defined.
