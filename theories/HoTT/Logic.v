From Equations Require Import Init.
Require Export HoTT.Basics.Overture.
Set Warnings "-notation-overridden".
Set Universe Polymorphism.

(** Fixes to the HoTT library *)

Register idpath as core.identity.refl.
Register paths_rect as core.identity.ind.
Register paths as core.identity.type.
Register inverse as core.identity.sym.

(** This allows [rewrite] to both in left-to-right and right-to left directions. *)
Definition paths_rect_r (A : Type) (x : A) (P : A -> Type) (p : P x) (y : A) (e : paths y x) : P y :=
  paths_rect A x (fun y e => P y) p y (inverse e).
Register concat as core.identity.trans.

Register ap as core.identity.congr.

Require Import HoTT.Types.Bool.
(* For compatibility with Coq's [induction] *)
Definition Bool_rect := Bool_ind.

(** /End of fixes to the HoTT library *)

(** The polymorphic equality type used by Equations when working with equality in Type. *)

Definition BiImpl (A B : Type) : Type := (A -> B) * (B -> A).

Notation "A <-> B" := (BiImpl A B) (at level 95) : type_scope.

Definition transport_r {A} (P : A -> Type) {x y : A} (e : y = x) : P x -> P y :=
  fun x => match (inverse e) with 1%path => x end.

Lemma paths_rect_dep_r {A} (x : A) (P : forall a, a = x -> Type) (p : P x 1%path)
      (y : A) (e : y = x) : P y e.
Proof. destruct e. apply p. Defined.
