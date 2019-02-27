From Equations Require Import Init.
From Coq Require Import Extraction Relation_Definitions.
(** A class for well foundedness proofs.
   Instances can be derived automatically using [Derive Subterm for ind]. *)

Class WellFounded {A : Type} (R : relation A) :=
  wellfounded : well_founded R.

(** The NoConfusionPackage class provides a method for solving injectivity and discrimination
    of constructors, represented by an equality on an inductive type [I]. The type of [noConfusion]
    should be of the form [ Π Δ, (x y : I Δ) (x = y) -> NoConfusion x y ], where
   [NoConfusion x y] for constructor-headed [x] and [y] will give equality of their arguments
   or the absurd proposition in case of conflict.
   This gives a general method for simplifying by discrimination or injectivity of constructors.

   Some actual instances are defined later in the file using the more primitive [discriminate] and
   [injection] tactics on which we can always fall back.
   *)

Class NoConfusionPackage (A : Type) := {
  NoConfusion : A -> A -> Prop;
  noConfusion : forall {a b}, a = b -> NoConfusion a b;
  noConfusion_inv : forall {a b}, NoConfusion a b -> a = b;
  noConfusion_is_equiv : forall {a b} (e : a = b), noConfusion_inv (noConfusion e) = e;
}.

(** This lemma explains how to apply it during simplification. *)
Lemma apply_noConfusion {A} {noconf : NoConfusionPackage A}
      (p q : A) {B : p = q -> Type} :
  (forall H : NoConfusion p q, B (noConfusion_inv H)) -> (forall H : p = q, B H).
Proof.
  intros. generalize (noConfusion_is_equiv H).
  intros e. destruct e. apply X.
Defined.
Extraction Inline apply_noConfusion.

(** We also provide a variant for equality in [Type]. *)

Polymorphic Class NoConfusionIdPackage (A : Type) := {
  NoConfusionId : A -> A -> Type;
  noConfusionId : forall {a b}, Id a b -> NoConfusionId a b;
  noConfusionId_inv : forall {a b}, NoConfusionId a b -> Id a b;
  noConfusionId_is_equiv : forall {a b} (e : Id a b), Id (noConfusionId_inv (noConfusionId e)) e;
}.

Polymorphic
Lemma apply_noConfusionId {A} {noconf : NoConfusionIdPackage A}
      (p q : A) {B : Id p q -> Type} :
  (forall e : NoConfusionId p q, B (noConfusionId_inv e)) -> (forall e : Id p q, B e).
Proof.
  intros. generalize (noConfusionId_is_equiv e). destruct e.
  intros <-. apply X.
Defined.
Extraction Inline apply_noConfusionId.

(** Apply [noConfusion] on a given hypothsis. *)

Ltac noconf_ref H :=
  match type of H with
    @eq ?A ?X ?Y =>
      let H' := fresh in assert (H':=noConfusion (A:=A) (a:=X) (b:=Y) H) ;
      clear H; hnf in H';
      match type of H' with
      | True => clear H'
      | False => elim H'
      | @eq _ _ _ => revert dependent H'
      | _ => fail
      end
  end.

(** For treating impossible cases. Equations corresponding to impossible
   calls form instances of [ImpossibleCall (f args)]. *)

Class ImpossibleCall {A : Type} (a : A) : Type :=
  is_impossible_call : False.

(** We have a trivial elimination operator for impossible calls. *)

Definition elim_impossible_call {A} (a : A) {imp : ImpossibleCall a} (P : A -> Type) : P a :=
  match is_impossible_call with end.

(** The tactic tries to find a call of [f] and eliminate it. *)

Ltac impossible_call f := on_call f ltac:(fun t => apply (elim_impossible_call t)).
