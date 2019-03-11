(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
Set Warnings "-notation-overridden".
From Equations Require Import Init.
Require Import Equations.HoTT.Logic Equations.HoTT.Classes Equations.HoTT.DepElim
        Equations.HoTT.Constants
        Equations.HoTT.Tactics Equations.HoTT.EqDec Equations.HoTT.NoConfusion.
Local Open Scope equations_scope.
Import Sigma_Notations.

Set Universe Polymorphism.


(** Tactic to solve EqDec goals, destructing recursive calls for the recursive
  structure of the type and calling instances of eq_dec on other types. *)

Ltac eqdec_loop t u :=
  (left; reflexivity) ||
  (solve [right; simplify *]) ||
  (let x := match t with
             | context C [ _ ?x ] => constr:(x)
             end
    in
    let y := match u with
             | context C [ _ ?y ] => constr:(y)
             end
    in
    let contrad := let Hn := fresh in
                   intro Hn; right; intros He; apply Hn; revert He; simplify *; reflexivity in
    let good :=
        let Heq := fresh in
        intros Heq; destruct Heq;
      let t' := match t with
                | context C [ ?x _ ] => constr:(x)
                end
      in
      let u' := match u with
                | context C [ ?y _ ] => constr:(y)
                end
      in
      (* idtac "there" t' u'; *)  try (eqdec_loop t' u')
    in
    (* idtac "here" x y; *)
    match goal with
    | [ H : forall z, sum (_ = z) _ |- _ ] =>
      case (H y); [good|contrad]
    | _ => case (eq_dec x y); [good|contrad]
    end) || idtac.

Ltac eqdec_proof := try red; intros;
  match goal with
   | |- sum (?x = ?y) _ =>
    revert y; do_ind x; intros until y; depelim y;
    match goal with
      |- sum (?x' = ?y') _ => eqdec_loop x' y'
    end
  end.

(** Standard instances. *)

Instance unit_eqdec : EqDec Unit.
Proof. eqdec_proof. Defined.

Instance bool_eqdec : EqDec Bool.Bool.
Proof. eqdec_proof. Defined.

Instance nat_eqdec : EqDec nat.
Proof. eqdec_proof. Defined.

Instance prod_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (prod A B).
Proof. eqdec_proof. Defined.

Instance sum_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (A + B).
Proof. eqdec_proof. Defined.

Instance list_eqdec {A} `(EqDec A) : EqDec (list A).
Proof. eqdec_proof. Defined.

(** Any signature made up entirely of decidable types is decidable. *)

Polymorphic Definition eqdec_sigma_Id@{i} {A : Type@{i}} {B : A -> Type@{i}}
            `(EqDec A) `(forall a, EqDec (B a)) :
  EqDec@{i} (sigma B).
Proof.
  Set Printing Universes.
  intros. intros [xa xb] [ya yb].
  case (eq_dec xa ya).
  - intros Hxya. destruct Hxya. case (eq_dec xb yb).
    + intros He; destruct He. left. reflexivity.
    + intros. right. apply simplification_sigma2_uip@{i i}. apply e.
  - intros. right. refine (simplification_sigma1_dep@{i i} _ _ _ _ _).
    intros He _; revert He. apply e.
Defined.
(* TODO fix universes *)
(* Polymorphic Definition eqdec_sig_Id@{i} {A : Type@{i}} {B : A -> Type@{i}} *)
(*             `(EqDec A) `(forall a, EqDec (B a)) : *)
(*   EqDec@{i} (sig B). *)
(* Proof. *)
(*   Set Printing Universes. *)
(*   intros. intros [xa xb] [ya yb]. *)
(*   case (eq_dec xa ya). *)
(*   - intros Hxya. destruct Hxya. case (eq_dec xb yb). *)
(*     + intros He; destruct He. left. reflexivity. *)
(*     + intros. right. simplify ?. apply simplification_sigma2_uip@{i i}. apply e. *)
(*   - intros. right. refine (simplification_sigma1_dep@{i i} _ _ _ _ _). *)
(*     intros He _; revert He. apply e. *)
(* Defined. *)

Existing Instance eqdec_sigma_Id.
