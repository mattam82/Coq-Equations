(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2015 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Instances of [NoConfusion] for the standard datatypes. To be used by 
   [equations] when it needs applications of injectivity or discrimination
   on some equation. *)

Require Import Coq.Program.Program Bvector List.
Require Import Equations.Signature Equations.EqDec.
Require Export Equations.DepElim.

Ltac noconf H ::=
  blocked ltac:(noconf_ref H; simplify_dep_elim) ; auto 3.

(** Used by the [Derive NoConfusion] command. *)

Ltac solve_noconf_prf := intros;
  on_last_hyp ltac:(fun id => destruct id) ; (* Subtitute a = b *)
  on_last_hyp ltac:(fun id => destruct id) ; (* Destruct the inductive object a *)
  constructor.

Ltac solve_noconf_inv := intros;
  match goal with
    |- ?R ?a ?b => destruct a; depelim b; simpl in *;
                 on_last_hyp ltac:(fun id =>
                                     revert id; simplify_dep_elim);
                 try constructor
  end.

Ltac solve_noconf_inv_equiv :=
  intros;
  on_last_hyp ltac:(fun id => destruct id) ; (* Subtitute a = b *)
  on_last_hyp ltac:(fun id => destruct id) ; (* Destruct the inductive object a *)
  simpl; autounfold with equations; rewrite_refl_id;
  try constructor.

Ltac solve_noconf := intros;
    match goal with
      [ H : @eq _ _ _ |- @eq _ _ _ ] => solve_noconf_inv_equiv
    | [ H : @eq _ _ _ |- _ ] => solve_noconf_prf
    | [ |- @eq _ _ _ ] => solve_noconf_inv
    end.

Derive NoConfusion for unit bool nat option sum prod list sigT sig.

(* FIXME should be done by the derive command *)
Extraction Inline noConfusion NoConfusionPackage_nat.


