(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
Set Warnings "-notation-overridden".
From Equations Require Import Init.
Require Import Equations.Type.Logic Equations.Type.Classes Equations.Type.DepElim
        Equations.Type.Tactics Equations.Type.EqDec.
Local Open Scope equations_scope.
Import Id_Notations Sigma_Notations.

Set Universe Polymorphism.

#[export]
Instance eqdec_hset (A : Type) `(EqDec A) : HSet A.
Proof.
  red. red. apply eq_proofs_unicity.
Defined.

(** Standard instances. *)

#[export]
Instance unit_eqdec : EqDec unit.
Proof. eqdec_proof. Defined.

#[export]
Instance bool_eqdec : EqDec bool.
Proof. eqdec_proof. Defined.

#[export]
Instance nat_eqdec : EqDec nat.
Proof. eqdec_proof. Defined.

#[export]
Instance prod_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (prod A B).
Proof. eqdec_proof. Defined.

#[export]
Instance sum_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (A + B).
Proof. eqdec_proof. Defined.

#[export]
Instance list_eqdec {A} `(EqDec A) : EqDec (list A).
Proof. eqdec_proof. Defined.

(** Any signature made up entirely of decidable types is decidable. *)

Polymorphic Definition eqdec_sig_Id@{i} {A : Type@{i}} {B : A -> Type@{i}}
            `(EqDec A) `(forall a, EqDec (B a)) :
  EqDec@{i} (sigma B).
Proof.
  Set Printing Universes.
  intros. intros [xa xb] [ya yb].
  case (eq_dec xa ya). intros Hxya. destruct Hxya. case (eq_dec xb yb).
  + intros He; destruct He. left. reflexivity.
  + intros. right. apply simplification_sigma2_uip@{i i}. apply e.
  + intros. right. refine (simplification_sigma1_dep@{i i} _ _ _ _ _).
    intros He _; revert He. apply e.
Defined.

#[export]
Existing Instance eqdec_sig_Id.
