(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Decidable equality.

   We redevelop the derivation of [K] from decidable equality on [A] making
   everything transparent and moving to [Type] so that programs using this 
   will actually be computable inside Coq. *)
   
(*i $Id$ i*)

Set Implicit Arguments.

Definition dec_eq {A} (x y : A) := 
  { x = y } + { x <> y }.

Class EqDec (A : Type) :=
  eq_dec : forall x y : A, { x = y } + { x <> y }.

Instance nat_eqdec : EqDec nat. 
Proof. intros x y. decide equality. Defined.

Instance bool_eqdec : EqDec bool. 
Proof. intros x y. decide equality. Defined.

Instance unit_eqdec : EqDec unit. 
Proof. intros x y. decide equality. Defined.

Instance list_eqdec {A} `(EqDec A) : EqDec (list A). 
Proof. intros x y. decide equality. Defined.

Section EqdepDec.

  Context {A : Type} `{EqDec A}.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = refl_equal y.
  Proof.
    intros.
    case u; trivial.
  Defined.

  Variable x : A.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
      | left eqxy => eqxy
      | right neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    reflexivity.

    case n; trivial.
  Defined.

  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (refl_equal x)) v.

  Remark nu_left_inv : forall (y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    intros.
    case u; unfold nu_inv in |- *.
    apply trans_sym_eq.
  Defined.

  Theorem eq_proofs_unicity : forall (y:A) (p1 p2:x = y), p1 = p2.
  Proof.
    intros.
    elim nu_left_inv with (u := p1).
    elim nu_left_inv with (u := p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Defined.

  Theorem K_dec :
    forall P:x = x -> Type, P (refl_equal x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity with x (refl_equal x) p.
    trivial.
  Defined.

  (** The corollary *)

  Let proj (P:A -> Type) (exP:sigT P) (def:P x) : P x :=
    match exP with
      | existT x' prf =>
        match eq_dec x' x with
          | left eqprf => eq_rect x' P prf x eqprf
          | _ => def
        end
    end.

  Theorem inj_right_pair :
    forall (P:A -> Type) (y y':P x),
      existT P x y = existT P x y' -> y = y'.
  Proof.
    intros.
    cut (proj (existT P x y) y = proj (existT P x y') y).
    simpl in |- *.
    case (eq_dec x x).
    intro e.
    elim e using K_dec; trivial.

    intros.
    case n; trivial.

    case H0.
    reflexivity.
  Defined.

  Lemma eq_dec_refl : eq_dec x x = left _ (eq_refl x).
  Proof. clear. case eq_dec. intros. f_equal. apply eq_proofs_unicity. 
    intro. congruence.
  Defined.

  Lemma inj_right_pair_refl (P : A -> Type) (y : P x) :
    inj_right_pair (y:=y) (y':=y) (eq_refl _) = (eq_refl _).
  Proof. unfold inj_right_pair. intros. 
    unfold eq_rect. unfold proj. rewrite eq_dec_refl. 
    unfold K_dec. simpl.
    unfold eq_proofs_unicity. subst proj. 
    simpl. unfold nu_inv, comp, nu. simpl. 
    unfold eq_ind, nu_left_inv, trans_sym_eq, eq_rect, nu_constant.
    rewrite eq_dec_refl. reflexivity.
  Defined.

End EqdepDec.
