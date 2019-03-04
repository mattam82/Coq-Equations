From Coq Require Import Extraction CRelationClasses.
From Equations Require Import Init.
Set Warnings "-notation-overridden".
Require Import Equations.Type.Logic Equations.Type.Relation
        Equations.Type.Relation_Properties Equations.Type.WellFounded.

Set Universe Polymorphism.

Import Id_Notations.

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
  { NoCycle : A -> A -> Type;
    noCycle : forall {a b}, NoCycle a b -> (a = b -> Empty) }.

(** These lemmas explains how to apply it during simplification. *)

(** We always generate a goal of the form [NoCycle x C[x]], using either
    the left or right versions of the following lemma. *)

Lemma apply_noCycle_left {A} {noconf : NoCyclePackage A}
      (p q : A) {B : p = q -> Type} :
  NoCycle p q -> (forall H : p = q, B H).
Proof.
  intros noc eq. destruct (noCycle noc eq).
Defined.

Lemma apply_noCycle_right {A} {noconf : NoCyclePackage A}
      (p q : A) {B : p = q -> Type} :
  NoCycle q p -> (forall H : p = q, B H).
Proof.
  intros noc eq. destruct (noCycle noc (id_sym eq)).
Defined.
Extraction Inline apply_noCycle_left apply_noCycle_right.

(** NoCycle can be decided using the well-founded subterm relation. *)

Definition NoCycle_WellFounded {A} (R : relation A) (wfR : WellFounded R) : NoCyclePackage A :=
  {| NoCycle := R;
     noCycle := WellFounded.well_founded_irreflexive |}.
Existing Instance NoCycle_WellFounded.

Hint Extern 30 (@NoCycle ?A (NoCycle_WellFounded ?R ?wfr) _ _) =>
  hnf; typeclasses eauto with subterm_relation : typeclass_instances.

(** The NoConfusionPackage class provides a method for solving injectivity and discrimination
    of constructors, represented by an equality on an inductive type [I]. The type of [noConfusion]
    should be of the form [ Π Δ, (x y : I Δ) (x = y) -> NoConfusion x y ], where
   [NoConfusion x y] for constructor-headed [x] and [y] will give equality of their arguments
   or the absurd proposition in case of conflict.
   This gives a general method for simplifying by discrimination or injectivity of constructors.

   Some actual instances are defined later in the file using the more primitive [discriminate] and
   [injection] tactics on which we can always fall back.
   *)

Cumulative Class NoConfusionPackage (A : Type) := {
  NoConfusion : A -> A -> Type;
  noConfusion : forall {a b}, NoConfusion a b -> Id a b;
  noConfusion_inv : forall {a b}, Id a b -> NoConfusion a b;
  noConfusion_sect : forall {a b} (e : NoConfusion a b), Id (noConfusion_inv (noConfusion e)) e;
  noConfusion_retr : forall {a b} (e : Id a b), Id (noConfusion (noConfusion_inv e)) e;
}.

(** This lemma explains how to apply it during simplification. *)

Polymorphic
Lemma apply_noConfusion {A} {noconf : NoConfusionPackage A}
      (p q : A) {B : Id p q -> Type} :
  (forall e : NoConfusion p q, B (noConfusion e)) -> (forall e : Id p q, B e).
Proof.
  intros. generalize (noConfusion_retr e). destruct e.
  intros <-. apply X.
Defined.
Extraction Inline apply_noConfusion.

(** Classes for types with UIP or decidable equality.  *)

Cumulative
Class UIP (A : Type) := uip : forall {x y : A} (e e' : x = y), e = e'.

Instance UIP_hSet (A : Type) (H : HSet A) : UIP A := H.

Definition dec_eq {A} (x y : A) : Type := (x = y) + (x <> y).

Class EqDec@{i} (A : Type@{i}) := eq_dec : forall x y : A, (x = y) + (x = y -> Empty@{i}).

Cumulative
Class EqDecPoint (A : Type) (x : A) := eq_dec_point : forall y : A, (x = y) + (x <> y).

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
