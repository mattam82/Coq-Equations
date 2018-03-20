(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations Require Import Init DepElim HSets.
Require Import Coq.Logic.JMeq.
Require Import HoTT.Basics.Overture.
Require Import HoTT.Basics.Decidable.

Set Universe Polymorphism.

Instance eqdec_hset (A : Type) `(EqDec A) : HSet A.
Proof.
  red. red. apply eq_proofs_unicity.
Defined.

(** Standard instances. *)

(* FIXME Fix standard instandec. *)
Instance unit_eqdec : EqDec Unit.
Proof. Admitted.

Require Import HoTT.Types.Bool.
Instance bool_eqdec : EqDec Bool.
Proof. Admitted.

Instance nat_eqdec : EqDec nat.
Proof. Admitted.

Instance prod_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (prod A B).
Proof. Admitted.

Instance sum_eqdec {A B} `(x : EqDec A) `(y : EqDec B) : EqDec (A + B).
Proof. Admitted.

Instance list_eqdec {A} `(EqDec A) : EqDec (list A).
Proof. Admitted.

(** Any signature made up entirely of decidable types is decidable. *)

Polymorphic Definition eqdec_sig_Id@{i j k} {A : Type@{i}} {B : A -> Type@{j}}
            `(HSets.EqDec A) `(forall a, HSets.EqDec (B a)) :
  HSets.EqDec@{k} (sigma A B).
Proof.
  intros. intros [xa xb] [ya yb].
  case (HSets.eq_dec xa ya). intros Hxya. destruct Hxya. case (HSets.eq_dec xb yb).
  + intros He; destruct He. left. reflexivity.
  + intros. right. apply Id_simplification_sigma2. apply e.
  + intros. right. apply Id_simplification_sigma1.
    intros He _; revert He. apply e.
Defined.

Polymorphic Existing Instance eqdec_sig_Id.
