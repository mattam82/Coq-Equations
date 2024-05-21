From Equations Require Import Init.
From Equations.Prop Require Export SigmaNotations.

From Coq Require Import Extraction Relation_Definitions.

(** The regular dependent eliminator of equality *)
Scheme eq_elim := Induction for eq Sort Type.

(** A symmetric variant taking a proof of [y = x] instead of [x = y].
    (Used in functional elimination principles in case of dependent "with" nodes)
 *)

Lemma eq_elim_r {A} (x : A) (P : forall a, a = x -> Type) (p : P x eq_refl)
      (y : A) (e : y = x) : P y e.
Proof. destruct e. apply p. Defined.

Extraction Inline eq_rect eq_rect_r eq_rec eq_ind eq_elim_r eq_elim.

(** Transport is a rephrasing of the non-dependent elimination principle of equality.  *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (e : x = y) : P x -> P y :=
  fun x => match e with eq_refl => x end.

(** [transport_r] is a symmetric variant. *)

Definition transport_r {A : Type} (P : A -> Type) {x y : A} (e : y = x) : P x -> P y :=
  transport P (eq_sym e).

Extraction Inline transport transport_r.

(** [inspect x] allows to pattern-match x while retaining a propositional equality with [x] *)

Definition inspect {A : Type} (x : A) : { y : A | x = y } := exist _ x eq_refl.

(** Extract sigma to a (non-dependent) pair in OCaml *)

Extract Inductive sigma => "( * )" ["(,)"].

(** Notation for the single element of [x = x]. *)

Arguments eq_refl {A} {x}.

(** Depdent eliminators for proofs, not derived automatically by Coq. *)

Lemma False_rect_dep (P : False -> Type) : forall e : False, P e.
Proof. intros e. destruct e. Defined.

Extraction Inline False_rect False_rect_dep.

Lemma True_rect_dep (P : True -> Type) (m : P I) : forall e : True, P e.
Proof. intros e. destruct e. exact m. Defined.

Extraction Inline True_rect True_rect_dep.
