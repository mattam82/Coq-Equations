(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Coq.Unicode.Utf8_core.

Declare ML Module "cc_plugin".
Declare ML Module "extraction_plugin".
Declare ML Module "equations_plugin".

(** A notation scope for equations declarations.

  The general mechanism of notations forces us to define
  notations in this scope in separate modules that we can
  avoid to export to remain compatible with user developments.
*)

Declare Scope equations_scope.
Delimit Scope equations_scope with equations.
Local Open Scope equations_scope.

Global Unset Auto Template Polymorphism.

(** We use this inductive internally *)

Variant equations_tag@{} : Set := the_equations_tag.

(** Notation for empty patterns. *)

Definition bang := the_equations_tag.
Opaque bang.
Notation "!" := bang.

Register bang as equations.internal.bang.

(** Notation for inaccessible patterns. *)

Definition inaccessible_pattern {A : Type} (t : A) := t.

Module Inaccessible_Notations.

  Notation "?( t )" := (inaccessible_pattern t) (format "?( t )") : equations_scope.

End Inaccessible_Notations.

Register inaccessible_pattern as equations.internal.inaccessible_pattern.

Import Inaccessible_Notations.

(** A marker for fixpoint prototypes in the context *)

Definition fixproto := the_equations_tag.

Register fixproto as equations.fixproto.

(** A constant to avoid displaying large let-defined terms
    in the context. *)
Definition hidebody {A : Type} {a : A} := a.

Register hidebody as equations.internal.hidebody.

Ltac hidebody H :=
  match goal with
    [ H := ?b |- _ ] => change (@hidebody _ b) in (value of H)
  end.

(** The sigma type used by Equations. *)

Set Primitive Projections.
Global Unset Printing Primitive Projection Parameters.
Polymorphic Cumulative Record sigma@{i} {A : Type@{i}} {B : A -> Type@{i}} : Type@{i} :=
  sigmaI { pr1 : A; pr2 : B pr1 }.
Unset Primitive Projections.
Arguments sigma {A} B.
Arguments sigmaI {A} B pr1 pr2.

Set Warnings "-notation-overridden".

Module Sigma_Notations.

Notation "'Σ' x .. y , P" := (sigma (fun x => .. (sigma (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' Σ  x  ..  y ']' ,  '/' P ']'") : type_scope.

Notation "( x , .. , y , z )" :=
  (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
      (right associativity, at level 0,
       format "( x ,  .. ,  y ,  z )") : equations_scope.

Notation " x .1 " := (pr1 x) (at level 3, format "x .1") : equations_scope.
Notation " x .2 " := (pr2 x) (at level 3, format "x .2") : equations_scope.

End Sigma_Notations.

Import Sigma_Notations.


(** Forward reference for the no-confusion tactic. *)
Ltac noconf H := fail "Equations.Init.noconf has not been bound yet".

(** Forward reference for the simplifier of equalities *)
Ltac simplify_equalities := fail "Equations.Init.simplify_equalities has not been bound yet".

(** Forward reference for simplification of equations internal constants *)
Ltac simpl_equations := fail "Equations.Init.simpl_equations has not been bound yet".

(** Forward reference for Equations' [depelim] tactic, which will be defined in [DepElim]. *)
Ltac depelim x := fail "Equations.Init.depelim has not been bound yet".

(** Forward reference for Equations' [depind] tactic, which will be defined in [DepElim]. *)
Ltac depind x := fail "Equations.Init.depind has not been bound yet".

(** Forward reference for Equations' [funelim] tactic, which will be defined in [FunctionalInduction]. *)
Ltac funelim_constr x := fail "Equations.Init.funelim_constr has not been bound yet".

(* We allow patterns, using the following trick. *)
Tactic Notation "funelim" uconstr(p) :=
  let call := fresh "call" in
  set (call:=p);
  lazymatch goal with
    [ call := ?fp |- _ ] =>
    subst call; funelim_constr fp
  end.

(** Forward reference for [apply_funelim]. A simpler minded variant that
    does no generalization by equalities. Use it if you want to do the
    induction loading by yourself. *)
Ltac apply_funelim x := fail "Equations.Init.funelim has not been bound yet".

(** A tactic that tries to remove trivial equality guards in induction hypotheses coming
   from [dependent induction]/[generalize_eqs] invocations. *)

Ltac simplify_IH_hyps := repeat
  match goal with
    | [ hyp : _ |- _ ] => simpl in hyp; eqns_specialize_eqs hyp; simpl in hyp
  end.

(** Forward reference for Equations' [solve_eqdec] tactic, which will be defined later in [EqDec].
    It is used to derive decidable equality on an inductive family. *)
Ltac solve_eqdec := fail "Equations.Init.solve_eqdec has not been bound yet".

(** Forward reference for Equations' [solve_subterm] tactic, which will be defined in [Subterm].
    It is used to derive the well-foundedness of the subterm relation. *)
Ltac solve_subterm := fail "Equations.Init.solve_subterm has not been bound yet".

(** Forward reference for Equations' [solve_noconf] tactic, which will be defined later.
    It is used to derive the heterogeneous no-confusion property of an inductive family. *)
Ltac solve_noconf := fail "Equations.Init.solve_noconf has not been bound yet".

(** Forward reference for Equations' [solve_noconf_hom] tactic, which will be defined later.
    It is used to derive the homogeneous no-confusion property of an inductive family. *)
Ltac solve_noconf_hom := fail "Equations.Init.solve_noconf_hom has not been bound yet".

(** Such a useful tactic it should be part of the stdlib. *)
Ltac forward_gen H tac :=
  match type of H with
  | ?X -> _ => let H' := fresh in assert (H':X) ; [tac|specialize (H H'); clear H']
  end.

Tactic Notation "forward" constr(H) := forward_gen H ltac:(idtac).
Tactic Notation "forward" constr(H) "by" tactic(tac) := forward_gen H tac.

(** A hintdb for transparency information of definitions related to [Below] and
   for solving goals related to [Below] instances. *)

Create HintDb Below discriminated.

(** Forward reference to an internal tactic to unfold well-founded fixpoints *)
Ltac unfold_recursor := fail "Equations.Init.unfold_recursor has not been bound yet".

(** Forward reference to an internal tactic to unfold well-founded fixpoints using funext *)
Ltac unfold_recursor_ext := fail "Equations.Init.unfold_recursor_ext has not been bound yet".

(** Forward reference to an internal tactic to combine eliminators for mutual and nested definitions *)
Ltac specialize_mutfix := fail "Equations.Init.specialize_mutfix has not been bound yet".