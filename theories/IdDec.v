(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Equations.Init.

(** Decidable equality.

   We redevelop the derivation of [K] from decidable equality on [A] making
   everything transparent and moving to [Type] so that programs using this 
   will actually be computable inside Coq. *)

Set Implicit Arguments.

Set Universe Polymorphism.

Import Id_Notations.
Open Scope equations.

Inductive sum@{i j} (A : Type@{i}) (B : Type@{i}) :=
| inl : A -> sum A B
| inr : B -> sum A B.
Arguments inl {A} {B} _.
Arguments inr {A} {B} _.

Notation " x + y " := (@sum x y) : type_scope.

Notation decidable A := (forall (x y : A), ((x = y) + (x <> y))%type).

Class EqDec (A : Type) := eq_dec : decidable A.

(* Class NoConfusionPackage (A : Type) := { *)
(*   NoConfusion : A -> A -> Type; *)
(*   noConfusion : forall a b, a = b -> NoConfusion a b *)
(* }. *)

(* Instance nat_eqdec : EqDec nat.  *)
(* Proof. *)
(*   red; induction x; destruct y. *)
(*   left; apply 1. *)
(*   right; intros Heq.  *)
(*   left *)
(*   red.  *)

  
(* Instance bool_eqdec : EqDec bool.  *)
(* Proof. intros x y. decide equality. Defined. *)

(* Instance unit_eqdec : EqDec unit.  *)
(* Proof. intros x y. decide equality. Defined. *)

(* Instance list_eqdec {A} `(EqDec A) : EqDec (list A).  *)
(* Proof. intros x y. decide equality. Defined. *)

(* Instance prod_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (prod A B). *)
(* Proof. intros x y. decide equality. Defined. *)

Section EqdepDec.

  Context {A : Type} `{EqDec A}.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    Id_rect _ _ (fun a _ => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = 1.
  Proof.
    intros.
    case u; apply 1.
  Defined.

  Variable x : A.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
      | inl eqxy => eqxy
      | inr neqxy => Empty_rect (fun x => _) (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros. apply 1.

    case e.
  Defined.

  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu 1) v.

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
    forall P:x = x -> Type, P 1 -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity with x (@id_refl _ x) p.
    trivial.
  Defined.

  Lemma eq_dec_refl : eq_dec x x = inl 1.
  Proof.
    case eq_dec. intros.
    rewrite (eq_proofs_unicity i 1). apply 1.
    intro e. case e. apply 1.
  Defined.

  (** The corollary *)

  Let proj (P:A -> Type) (exP:sigT P) (def:P x) : P x :=
    match exP with
      | existT x' prf =>
        match eq_dec x' x with
          | inl eqprf => Id_rect _ x' (fun x _ => P x) prf x eqprf
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
    unfold proj.
    case (eq_dec x x).
    intro e.
    elim e using K_dec; trivial.

    intros.
    case e; apply 1.

    case X.
    reflexivity.
  Defined.

  Lemma inj_right_pair_refl (P : A -> Type) (y : P x) :
    inj_right_pair (y:=y) (y':=y) 1 = 1.
  Proof. unfold inj_right_pair. intros. 
    unfold Id_rect. unfold proj. rewrite eq_dec_refl. 
    unfold K_dec. simpl.
    unfold eq_proofs_unicity. subst proj. 
    simpl. unfold nu_inv, comp, nu. simpl. 
    unfold paths_ind, nu_left_inv, trans_sym_eq, nu_constant.
    rewrite eq_dec_refl. reflexivity.
  Defined.

  (* On [sigma] *)
  
  Let projs (P:A -> Type) (exP:sigma A P) (def:P x) : P x :=
    match exP with
      | sigmaI x' prf =>
        match eq_dec x' x with
          | inl eqprf => Id_rect _ x' (fun x _ => P x) prf x eqprf
          | _ => def
        end
    end.

  Theorem inj_right_sigma :
    forall (P:A -> Type) (y y':P x),
      sigmaI P x y = sigmaI P x y' -> y = y'.
  Proof.
    intros.
    cut (projs (sigmaI P x y) y = projs (sigmaI P x y') y).
    unfold projs. 
    unfold proj.
    case (eq_dec x x).
    intro e.
    elim e using K_dec. trivial.

    intros.
    case e; apply 1.

    case X.
    reflexivity.
  Defined.

  Lemma inj_right_sigma_refl (P : A -> Type) (y : P x) :
    inj_right_sigma (y:=y) (y':=y) 1 = 1.
  Proof. unfold inj_right_sigma. intros. 
    unfold Id_rect. unfold projs. rewrite eq_dec_refl. 
    unfold K_dec. simpl.
    unfold eq_proofs_unicity. subst projs.
    simpl. unfold nu_inv, comp, nu. simpl.
    unfold paths_ind, nu_left_inv, trans_sym_eq, Id_rect, nu_constant.
    rewrite eq_dec_refl. reflexivity.
  Defined.

End EqdepDec.
