(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Equations.Signature Equations.DepElim Equations.EqDec.

(** Alternative implementation of generalization using sigma types only,
   allowing to use K on decidable domains. *)

Hint Rewrite @inj_right_pair_refl : refl_id.

(** Decompose existential packages. *)

Ltac decompose_exists id := hnf in id ;
  match type of id with
    | { x : _ & _ } => let xn := fresh x in 
      destruct id as [xn id]; decompose_exists xn; 
        cbv beta delta [ projT1 projT2 ] iota in id;
          decompose_exists id
    | _ => cbv beta delta [ projT1 projT2 ] iota in id
  end.

(** Dependent generalization using existentials only. *)

Ltac generalize_sig id cont :=
  let id' := fresh id in
  get_signature_pack id id';
  hnf in (value of id'); hnf in (type of id');
  generalize (@eq_refl _ id' : id' = id') ;
  unfold id' at 1;
  clearbody id'; move id' after id ;
  revert_until id'; rename id' into id;
    cont id.

Ltac generalize_sig_dest id :=
  generalize_sig id ltac:(fun id => decompose_exists id).

Ltac generalize_eqs_sig id :=
  (needs_generalization id ; generalize_sig_dest id) || idtac.

Ltac generalize_eqs_vars_sig id :=
  generalize_eqs_sig id.

Ltac generalize_by_eqs id ::= generalize_eqs_sig id.
Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars_sig id.

(** Any signature made up entirely of decidable types is decidable. *)

Instance eqdec_sig {A} {B : A -> Type} `(EqDec A) `(forall a, EqDec (B a)) : EqDec { x : A & B x }.
Proof.
  intros. intros x y. decompose_exists x. decompose_exists y.
  case (eq_dec x0 x1). simpdep. case (eq_dec x y). simpdep. left. reflexivity.
  intros. right. red. simpdep. apply n. auto.
  intros. right. red. simpdep. apply n. auto.
Defined.
