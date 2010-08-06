(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Instances of [Below] for the standard datatypes. To be used by 
   [equations] when it needs to do recursion on a type. *)

Require Import Bvector.

Require Import Coq.Program.Program.
Require Export Equations.DepElim.

(** The [BelowPackage] class provides the definition of a [Below] predicate for some datatype,
   allowing to talk about course-of-value recursion on it. *)

Class BelowPackage (A : Type) := {
  Below : A -> Type ;
  below : ∀ (a : A), Below a }.

(** The [Recursor] class defines a recursor on a type *)

Class Recursor (A : Type) :=
  { rec_type : ∀ x : A, Type ; rec : ∀ x : A, rec_type x }.

(** A hintdb for transparency information of definitions related to [Below] and
   for solving goals related to [Below] instances. *)

Create HintDb Below discriminated.

(** Support simplification of unification constraints appearing in the goal
   and the hypothesis. *)

Hint Extern 0 (_ = _) => reflexivity : Below.
Hint Extern 0 (_ ~= _) => reflexivity : Below.

(** Use it as well as the [equations] simplifications. *)

Ltac unfold_equations ::= repeat progress autounfold with equations Below.
Ltac unfold_equations_in H ::= repeat progress autounfold with equations Below in H.

Ltac destruct_conj := 
  match goal with
    [ H : (_ * _)%type |- _ ] => destruct H
  end.

(** Simplify [Below] hyps for proof search. *)

Hint Extern 2 => progress (autorewrite with Below in * ; 
  destruct_conj ; simplify_IH_hyps) : Below.

(** When solving goals with recursive prototypes in them, we allow an application
   only if it keeps the proof guarded (FIXME, guarded doesn't work). *)

Ltac apply_fix_proto := 
  match goal with
    [ f : fix_proto _ |- _ ] => unfold fix_proto in f ; apply f (*  ; guarded  *)
  end.

Hint Opaque fix_proto : Below.

Hint Extern 100 => apply_fix_proto : Below.

(** We now derive standard Below instances. *)

Derive Below for nat.

Definition rec_nat (P : nat -> Type) n (step : ∀ n, Below_nat P n -> P n) : P n :=
  step n (below_nat P step n).

Instance nat_Recursor : Recursor nat :=
  { rec_type := λ n, ∀ P step, P n ;
    rec := λ n P step, rec_nat P n step }.

Equations(nocomp noind) Below_vector A (P : ∀ n, vector A n -> Type) n (v : vector A n) : Type :=
Below_vector A P ?(0) Vnil := unit ;
Below_vector A P ?(S n) (Vcons a n v) := 
  ((P n v) * Below_vector A P n v)%type.

Hint Rewrite Below_vector_equation_2 : Below.

(* Equations(nocomp noeqns noind) below_vector A (P : ∀ n, vector A n -> Type) *)
(*   (step : ∀ n (v : vector A n), Below_vector A P n v -> P n v) *)
(*   n (v : vector A n) : Below_vector A P n v := *)
(* below_vector A P _ ?(0) Vnil := tt ; *)
(* below_vector A P step ?(S n) (Vcons a n v) :=  *)
(*   let rest := below_vector A P step n v in *)
(*     (step n v rest, rest). *)

(* Global Opaque Below_vector. *)

(* Definition rec_vector A (P : ∀ n, vector A n -> Type) n v *)
(*   (step : ∀ n (v : vector A n), Below_vector A P n v -> P n v) : P n v := *)
(*   step n v (below_vector A P step n v). *)

(* Instance vect_Recursor A n : Recursor (vector A n) := *)
(*   { rec_type := λ v, ∀ (P : ∀ n, vector A n -> Type) step, P n v; *)
(*     rec := λ v P step, rec_vector A P n v step }. *)

(* Hint Unfold rec_nat rec_vector : Recursors. *)

Hint Extern 4 => progress (unfold hide_pattern in *) : Below.

Ltac add_pattern t :=
  match goal with
    |- ?T => change (add_pattern T t)
  end.

Ltac rec_fast v recname := intro_block v ; move v at top ;
  generalize_eqs_vars v ; (intros until v || revert_until v) ;
    let recv := eval simpl in (rec v) in
    (eapply recv || (dependent pattern v ; refine (recv _ _))) ;
    clear_except recname ;
    intros until 1 ; on_last_hyp ltac:(fun x => rename x into recname) ;
      simpl in * ; simplify_dep_elim ; intros ; unblock_goal ; intros ;
        (try move recname at bottom) ;
        add_pattern (hide_pattern recname).

Ltac rec_debug v recname := intro_block v ; move v at top ;
  generalize_eqs_vars v ; (intros until v || revert_until v) ;
    let recv := eval simpl in (rec v) in show_goal ; 
    (eapply recv || (dependent pattern v ; refine (recv _ _))) ; show_hyps ; idtac "before clear";
    clear_except recname ; 
    intros until 1 ; on_last_hyp ltac:(fun x => rename x into recname) ;
    idtac "after clear";
    show_hyps ; show_goal ; simpl in * ; simplify_dep_elim ; intros ; unblock_goal ; intros ;
      add_pattern (hide_pattern recname).

Ltac rec v recname := rec_fast v recname.

Ltac solve_rec := simpl in * ; cbv zeta ; intros ; try typeclasses eauto with Below.
