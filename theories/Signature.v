(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

(** Signatures for dependent types. 
   
   A signature for [A] is a sigma-type in which any [A] 
   can be packed. *)

From Equations Require Import Init.

Polymorphic Cumulative Class Signature (fam : Type) (signature_index : Type) : Type := {
  signature : signature_index -> Type ;
  signature_pack : fam -> sigma signature
}.

Register Equations.Signature.Signature as equations.signature.class.
Register Equations.Signature.signature as equations.signature.signature.
Register Equations.Signature.signature_pack as equations.signature.pack.

Extraction Inline signature signature_pack.

(* For right associated sigmas *)

Ltac destruct_right_sigma H :=
  match type of H with
  | @sigma _ (fun x => unit) =>
    let ph := fresh in
    destruct H as [x ph];
      cbn [pr1 pr2] in * |- *; try clear ph
  | @sigma _ (fun x => _) =>
    destruct H as [x H]; destruct_right_sigma H
  | @sigma _ _ => destruct H as [x H];
      destruct_right_sigma H
  | _ => idtac
  end.

Ltac destruct_one_sigma :=
  match goal with
  | [ H : @sigma _ _ |- _ ] => destruct_right_sigma H
  end.

Ltac simp_sigmas := repeat destruct_one_sigma.
