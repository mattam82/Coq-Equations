From Equations Require Import DepElim.
Require Import Eqdep EqdepFacts.

Lemma simplification_K : forall {A} (x : A) {B : x = x -> Type}, B eq_refl -> (forall p : x = x, B p).
Proof. intros. rewrite (UIP_refl A). assumption. Defined.
Arguments simplification_K : simpl never.

Register simplification_K as equations.depelim.simpl_K.

Lemma UIP_refl_refl : forall A (x : A),
  UIP_refl A x eq_refl = eq_refl.
Proof. intros. apply UIP_refl. Qed.

Lemma simplification_K_refl : forall {A} (x : A) {B : x = x -> Type}
                                    (p : B eq_refl),
  simplification_K x p eq_refl = p.
Proof.
  intros.
  unfold simplification_K.
  rewrite UIP_refl_refl. unfold eq_rect_r. simpl.
  reflexivity.
Defined.

Global Opaque simplification_K.
Extraction Inline simplification_K.
Ltac rewrite_sigma2_refl_K :=
  match goal with
  | |- context [@simplification_K ?A ?x ?B ?p eq_refl] =>
    rewrite (@simplification_K_refl A x B p); simpl eq_rect
  end.

Ltac rewrite_sigma2_refl ::= rewrite_sigma2_refl_noK || rewrite_sigma2_refl_K.

Ltac rewrite_sigma2_rule_K c :=
  match c with
  | @simplification_K ?A ?x ?B ?p eq_refl=>
    rewrite (@simplification_K_refl A x B p); simpl eq_rect
  end.

Ltac rewrite_sigma2_rule c ::=
  rewrite_sigma2_rule_noK c || rewrite_sigma2_rule_K c.


(* Polymorphic Lemma Id_simplification_K_ax : *)
(*   forall {A} (x : A) {B : Id x x -> Type}, B id_refl -> (forall p : Id x x, B p). *)
(* Proof. intros. rewrite (UIP_refl A). assumption. Defined. *)
(* Arguments simplification_K : simpl never. *)

(* Lemma Id_simplification_K_refl : forall {A} (x : A) {B : x = x -> Type} *)
(*                                     (p : B eq_refl), *)
(*   simplification_K x p eq_refl = p. *)
(* Proof. *)
(*   intros. *)
(*   unfold simplification_K. *)
(*   rewrite UIP_refl_refl. unfold eq_rect_r. simpl. *)
(*   reflexivity. *)
(* Defined. *)
