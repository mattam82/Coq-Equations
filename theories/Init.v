(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Coq.Unicode.Utf8_core.

Require Export HoTT.Basics.Overture.
Require Export Coq.extraction.Extraction.
Require Export Coq.Program.Tactics.

Declare ML Module "equations_plugin".

(** A notation scope for equations declarations.

  The general mechanism of notations forces us to define
  notations in this scope in separate modules that we can
  avoid to export to remain compatible with user developments.
*)

Delimit Scope equations_scope with equations.
Local Open Scope equations_scope.

(** For now we don't support obligation shrinking. Need to sync ML code with this. *)
Set Warnings "-deprecated-option".
Global Unset Shrink Obligations.

(** Path induction referenced in equations_common.ml *)
Local Definition eq_rect_r {A : Type} (x : A) (P : A -> Type) (b : P x) (y : A) (H : y = x) : P y :=
  paths_rew_r A y x P b H.

(** Identity function referenced in equations_common.ml *)
Local Definition id {A : Type} (x : A) := x.

(** A marker for fixpoint prototypes in the context *)
Definition fixproto := tt.

(** A constant to avoid displaying large let-defined terms
    in the context. *)
Definition hidebody {A : Type} {a : A} := a.

Ltac hidebody H :=
  match goal with
    [ H := ?b |- _ ] => change (@hidebody _ b) in (value of H)
  end.

Ltac destruct_rec_calls ::=
  match goal with
    | [ H : let _ := fixproto in _ |- _ ] => red in H; destruct_calls H ; clear H
  end.

(* Redefine to avoid the [simpl] tactic before clearing fixpoint prototypes *)
Ltac program_simplify ::=
  intros; destruct_all_rec_calls; simpl in *; repeat (destruct_conjs; simpl proj1_sig in * );
  subst*; autoinjections ; try discriminates ;
    try (solve [ red ; intros ; destruct_conjs ; autoinjections ; discriminates ]).

(** The sigma type used by Equations. *)

Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.
Global Unset Printing Primitive Projection Compatibility.
Polymorphic Record sigma {A : Type} {B : A -> Type} : Type := sigmaI { pr1 : A; pr2 : B pr1 }.
Unset Primitive Projections.

Arguments sigma A B : clear implicits.
Arguments sigmaI {A} B pr1 pr2.

Set Warnings "-notation-overridden".

Module Sigma_Notations.

  Notation "&{ x : A & y }" := (@sigma A (fun x : A => y)%type) (x at level 99) : equations_scope.
  Notation "&{ x : A & y }" := (@sigma A (fun x : A => y)%type) (x at level 99) : type_scope.
  Notation "&( x , .. , y & z )" :=
    (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
      (right associativity, at level 4,
       format "&( x ,  .. ,  y  &  z )") : equations_scope.
  Notation " x .1 " := (pr1 x) (at level 3, format "x .1") : equations_scope.
  Notation " x .2 " := (pr2 x) (at level 3, format "x .2") : equations_scope.

End Sigma_Notations.

Import Sigma_Notations.

(** The polymorphic equality type used by Equations. *)

Set Universe Polymorphism.

Inductive Empty@{i} : Type@{i} :=.

Inductive Id@{i} {A : Type@{i}} (a : A) : A -> Type@{i} :=
  id_refl : Id a a.
Arguments id_refl {A a}, [A] a.

Module Id_Notations.

  Notation " x = y " := (@Id _ x y) : equations_scope.
  Notation " x = y " := (@Id _ x y) : type_scope.
  Notation " x <> y " := (@Id _ x y -> Empty) : equations_scope.
  Notation " x <> y " := (@Id _ x y -> Empty) : type_scope.
  Notation " 1 " := (@id_refl _ _) : equations_scope.

End Id_Notations.

Import Id_Notations.

Section IdTheory.
  Universe i.
  Context {A : Type@{i}}.

  Import Id_Notations.

  Lemma id_sym {x y : A} : x = y -> y = x.
  Proof. destruct 1. apply 1. Defined.

  Lemma id_trans {x y z : A} : x = y -> y = z -> x = z.
  Proof. destruct 1. apply (fun a => a). Defined.

End IdTheory.

(** Forward reference for the NoConfusion tactic. *)
Ltac noconf H := (* FIXME congruence || *) injection H; intros; subst.

(** Such a useful tactic it should be part of the stdlib. *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.
