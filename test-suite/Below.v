(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2021 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Instances of [Below] for the standard datatypes. To be used by 
   [equations] when it needs to do recursion on a type. *)

Set Warnings "-deprecated-library-file-since-8.20".
Set Warnings "-warn-library-file-stdlib-vector".
From Stdlib Require Import Bvector Vectors.Vector.
From Equations Require Import Init CoreTactics.
From Equations.Prop Require Import DepElim Tactics Constants FunctionalInduction.

(** The [BelowPackage] class provides the definition of a [Below] predicate for some datatype,
   allowing to talk about course-of-value recursion on it. *)

Class BelowPackage (A : Type) := {
  Below : A -> Type ;
  below : forall (a : A), Below a }.

(** The [Recursor] class defines a recursor on a type *)

Class Recursor (A : Type) :=
  { rec_type : forall x : A, Type ; rec : forall x : A, rec_type x }.

(** Support simplification of unification constraints appearing in the goal
   and the hypothesis. *)

#[local] Hint Extern 0 (_ = _) => reflexivity : rec_decision.

Ltac simpl_let :=
  match goal with
    [ H : let _ := ?t in _ |- _ ] =>
    match t with
    | fixproto => fail 1
    | _ => cbv zeta in H
    end
  end.

#[local] Hint Extern 40 => progress (cbv beta in * || simpl_let) : rec_decision.

(** Use it as well as the [equations] simplifications. *)

Ltac unfold_equations ::= repeat progress autounfold with equations Below.
Ltac unfold_equations_in H ::= repeat progress autounfold with equations Below in H.

Ltac destruct_conj := 
  match goal with
    [ H : (_ * _)%type |- _ ] => destruct H
  end.

(** Simplify [Below] hyps for proof search. *)

#[local] Hint Extern 2 => progress (autorewrite with Below in * ; 
  destruct_conj ; simplify_IH_hyps) : rec_decision.

(** When solving goals with recursive prototypes in them, we allow an application
   only if it keeps the proof guarded (FIXME, guarded doesn't work). *)

Ltac apply_fix_proto := 
  match goal with
  | [ f : let _ := fixproto in _ |- _ ] => apply f
  end.

#[local] Hint Extern 100 => apply_fix_proto : rec_decision.

(** We now derive standard Below instances. *)

Derive Below for nat.

Definition rec_nat (P : nat -> Type) n (step : forall n, Below_nat P n -> P n) : P n :=
  step n (below_nat P step n).

#[export]
Instance nat_Recursor : Recursor nat :=
  { rec_type := fun n => forall P step, P n ;
    rec := fun n P step => rec_nat P n step }.

Notation vector := Vector.t.
Import Vector.
Arguments nil {A}.
Arguments cons {A} _ {n}.

Open Scope equations_scope.

Import EquationsNotations.

Equations Below_vector A (P : forall n, vector A n -> Type) n (v : vector A n) : Type
  by struct v :=
Below_vector A P ?(0) [] := unit ;
Below_vector A P _ (a :: v) :=
  ((P _ v) * Below_vector A P _ v)%type.

#[local] Hint Rewrite Below_vector_equation_2 : rec_decision.

Ltac rec_fast v recname := intro_block v ; move v at top ;
  generalize_by_eqs_vars v ; (intros until v || revert_until v) ;
    let recv := eval simpl in (rec v) in
    (eapply recv || (dependent pattern v ; refine (recv _ _))) ;
    clear -recname ;
    intros until 1 ; on_last_hyp ltac:(fun x => rename x into recname) ;
      simpl in * ; simplify_dep_elim ; intros ; unblock_goal ; intros ;
        (try move recname at bottom) ;
        add_pattern (hide_pattern recname).

(* Ltac rec_debug v recname := intro_block v ; move v at top ; *)
(*   generalize_by_eqs_vars v ; (intros until v || revert_until v) ; *)
(*     let recv := eval simpl in (rec v) in show_goal ;  *)
(*     (eapply recv || (dependent pattern v ; refine (recv _ _))) ; show_hyps ; idtac "before clear"; *)
(*     clear_except recname ;  *)
(*     intros until 1 ; on_last_hyp ltac:(fun x => rename x into recname) ; *)
(*     idtac "after clear"; *)
(*     show_hyps ; show_goal ; simpl in * ; simplify_dep_elim ; intros ; unblock_goal ; intros ; *)
(*       add_pattern (hide_pattern recname). *)

Ltac rec recname v := rec_fast v recname.
