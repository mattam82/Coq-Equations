From Equations Require Import Init.
From Coq Require Import Extraction Relation_Definitions.
(** A class for well foundedness proofs.
   Instances can be derived automatically using [Derive Subterm for ind]. *)

Class WellFounded {A : Type} (R : relation A) :=
  wellfounded : well_founded R.

(** This class contains no-cyclicity proofs.
    They can be derived from well-foundedness proofs for example.
 *)

(** The proofs of [NoCycle] can be arbitrarily large, it doesn't
    actually matter in the sense that they are used to prove
    absurdity. *)

Class NoCyclePackage (A : Type) :=
  { NoCycle : A -> A -> Prop;
    noCycle : forall {a b}, NoCycle a b -> (a = b -> False) }.

(** These lemmas explains how to apply it during simplification. *)

(** We always generate a goal of the form [NoCycle x C[x]], using either
    the left or right versions of the following lemma. *)

Lemma apply_noCycle_left {A} {noconf : NoCyclePackage A}
      (p q : A) {B : p = q -> Type} :
  NoCycle p q -> (forall H : p = q, B H).
Proof.
  intros. destruct (noCycle H H0).
Defined.

Lemma apply_noCycle_right {A} {noconf : NoCyclePackage A}
      (p q : A) {B : p = q -> Type} :
  NoCycle q p -> (forall H : p = q, B H).
Proof.
  intros. destruct (noCycle H (eq_sym H0)).
Defined.
Extraction Inline apply_noCycle_left apply_noCycle_right.

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
  noConfusion : forall {a b}, NoConfusion a b -> a = b;
  noConfusion_inv : forall {a b}, a = b -> NoConfusion a b;
  noConfusion_sect : forall {a b} (e : NoConfusion a b), noConfusion_inv (noConfusion e) = e;
  noConfusion_retr : forall {a b} (e : a = b), noConfusion (noConfusion_inv e) = e;
}.

(** This lemma explains how to apply it during simplification. *)
Lemma apply_noConfusion {A} {noconf : NoConfusionPackage A}
      (p q : A) {B : p = q -> Type} :
  (forall H : NoConfusion p q, B (noConfusion H)) -> (forall H : p = q, B H).
Proof.
  intros. generalize (noConfusion_retr H).
  intros e. destruct e. apply X.
Defined.
Extraction Inline apply_noConfusion.

(** Classes for types with UIP or decidable equality.  *)

Class UIP (A : Type) := uip : forall {x y : A} (e e' : x = y), e = e'.

Class EqDec (A : Type) :=
  eq_dec : forall x y : A, { x = y } + { x <> y }.

Class EqDecPoint (A : Type) (x : A) :=
  eq_dec_point : forall y : A, { x = y } + { x <> y }.

Instance EqDec_EqDecPoint A `(EqDec A) (x : A) : EqDecPoint A x := eq_dec x.

(** For treating impossible cases. Equations corresponding to impossible
   calls form instances of [ImpossibleCall (f args)]. *)

Class ImpossibleCall {A : Type} (a : A) : Type :=
  is_impossible_call : False.

(** We have a trivial elimination operator for impossible calls. *)

Definition elim_impossible_call {A} (a : A) {imp : ImpossibleCall a} (P : A -> Type) : P a :=
  match is_impossible_call with end.

(** The tactic tries to find a call of [f] and eliminate it. *)

Ltac impossible_call f := on_call f ltac:(fun t => apply (elim_impossible_call t)).
