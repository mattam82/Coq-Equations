(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2019 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import HoTT.Basics.Overture.
Require Import Coq.Logic.EqdepFacts.
Require Import Equations.Init Equations.Classes.

(** Decidable equality.

   We redevelop the derivation of [UIP] from decidable equality on [A] making
   everything transparent and moving to [Type] so that programs using this 
   will actually be computable inside Coq. *)

Set Implicit Arguments.
Set Universe Polymorphism.

Definition dec_eq {A} (x y : A) := 
  ( x = y ) + ( x <> y ).

(** We rederive the UIP shifting proof transparently. *)
Theorem UIP_shift_on (X : Type) (x : X) :
  UIP_refl_on_ X x -> forall y : x = x, UIP_refl_on_ (x = x) y.
Proof.
  intros UIP_refl y.
  rewrite (UIP_refl y).
  intros z.
  assert (UIP:forall y' y'' : x = x, y' = y'').
  { intros. apply eq_trans_r with (eq_refl x); apply UIP_refl. }
  transitivity (eq_trans (eq_trans (UIP (eq_refl x) (eq_refl x)) z)
                         (eq_sym (UIP (eq_refl x) (eq_refl x)))).
  - destruct z. destruct (UIP _ _). reflexivity.
  - change
      (match eq_refl x as y' in _ = x' return y' = y' -> Prop with
       | eq_refl => fun z => z = (eq_refl (eq_refl x))
       end (eq_trans (eq_trans (UIP (eq_refl x) (eq_refl x)) z)
                     (eq_sym (UIP (eq_refl x) (eq_refl x))))).
    destruct z. destruct (UIP _ _). reflexivity.
Defined.

Theorem UIP_shift : forall U, UIP_refl_ U -> forall x:U, UIP_refl_ (x = x).
Proof. exact (fun U UIP_refl x => @UIP_shift_on U x (UIP_refl x)). Defined.

(** This is the reduction rule of UIP. *)
Lemma uip_refl_refl {A} {E : UIP A} (x : A) : uip (x:=x) eq_refl eq_refl = eq_refl.
Proof.
  assert (Us:=UIP_shift).
  specialize (Us A). compute in Us. apply Us.
  intros. apply uip.
Defined.

Theorem UIP_K {A} {U : UIP A} (x : A) : 
  forall P : x = x -> Type,
    P (refl_equal x) -> forall p : x = x, P p.
Proof.
  intros P peq e. now elim (uip refl_equal e).
Defined.

(** Derivation of principles on sigma types whose domain is decidable. *)

Section EqdepDec.

  Context {A : Type} `{EqDec A}.
  
  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    paths_ind _ (fun a _ => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = idpath y.
  Proof.
    intros.
    case u; trivial.
  Defined.

  Variable x : A.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
      | inl eqxy => eqxy
      | inr neqxy => Overture.Empty_ind (fun _ => x = y) (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    reflexivity.

    case n; trivial.
  Defined.

  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (idpath x)) v.

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
    forall P:x = x -> Type, P (idpath x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity with x (idpath x) p.
    trivial.
  Defined.

  Lemma eq_dec_refl : eq_dec x x = inl _ (idpath x).
  Proof. case eq_dec. intros. f_ap. apply eq_proofs_unicity.
    contradiction.
  Defined.

  (** The corollary *)

  Let proj (P:A -> Type) (exP:sigT P) (def:P x) : P x :=
    match exP with
      | existT x' prf =>
        match eq_dec x' x with
          | inl eqprf => paths_ind x' (fun a _ => P a) prf x eqprf
          | _ => def
        end
    end.

  Theorem inj_right_pair :
    forall (P:A -> Type) (y y':P x),
      existT P x y = existT P x y' -> y = y'.
  Proof.
    intros P y y' H0.
    cut (proj (existT P x y) y = proj (existT P x y') y).
    unfold proj.
    simpl in |- *.
    case (eq_dec x x).
    intro e.
    elim e using K_dec; trivial.

    intros.
    case n; trivial.

    case H0.
    reflexivity.
  Defined.

  Lemma inj_right_pair_refl (P : A -> Type) (y : P x) :
    inj_right_pair (y:=y) (y':=y) (idpath _) = (idpath _).
  Proof. unfold inj_right_pair. intros. 
    unfold paths_ind. unfold proj. rewrite eq_dec_refl.
    unfold K_dec. simpl.
    unfold eq_proofs_unicity. subst proj. 
    simpl. unfold nu_inv, comp, nu. simpl. 
    unfold paths_ind, nu_left_inv, trans_sym_eq, nu_constant.
    rewrite eq_dec_refl. reflexivity.
  Defined.

End EqdepDec.

(** Derivation of principles on sigma types whose domain is decidable. *)

Section PointEqdepDec.
  Set Universe Polymorphism.
  
  Context {A : Type} {x : A} `{EqDecPoint A x}.
  
  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    paths_ind _ (fun a _ => a = y') eq2 _ eq1.

  Remark point_trans_sym_eq : forall (x y:A) (u:x = y), comp u u = idpath y.
  Proof.
    intros.
    case u; trivial.
  Defined.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec_point y with
      | inl eqxy => eqxy
      | inr neqxy => Overture.Empty_ind (fun _ => x = y) (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec_point y); intros.
    reflexivity.

    case n; trivial.
  Defined.

  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (idpath x)) v.

  Remark nu_left_inv_point : forall (y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    intros.
    case u; unfold nu_inv in |- *.
    apply trans_sym_eq.
  Defined.

  Theorem eq_proofs_unicity_point : forall (y:A) (p1 p2:x = y), p1 = p2.
  Proof.
    intros.
    elim nu_left_inv_point with (u := p1).
    elim nu_left_inv_point with (u := p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Defined.

  Theorem K_dec_point :
    forall P:x = x -> Type, P (idpath x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity_point with x (idpath x) p.
    trivial.
  Defined.

  Lemma eq_dec_refl_point : eq_dec_point x = inl _ (idpath x).
  Proof. case eq_dec_point. intros. f_ap. apply eq_proofs_unicity_point.
    contradiction.
  Defined.

  (** The corollary *)

  Let proj (P:A -> Type) (exP:sigma _ P) (def:P x) : P x :=
    match exP with
      | sigmaI x' prf =>
        match eq_dec_point x' with
          | inl eqprf => paths_ind x' (fun a _ => P a) prf x (inverse eqprf)
          | _ => def
        end
    end.

  Theorem inj_right_sigma_point :
    forall (P:A -> Type) (y y':P x),
      sigmaI P x y = sigmaI P x y' -> y = y'.
  Proof.
    intros P y y' H0.
    cut (proj (sigmaI P x y) y = proj (sigmaI P x y') y).
    unfold proj. simpl in |- *.
    case (eq_dec_point x).
    intro e.
    elim e using K_dec_point; trivial.

    intros.
    case n; trivial.

    case H0.
    reflexivity.
  Defined.

  Lemma inj_right_sigma_refl_point (P : A -> Type) (y : P x) :
    inj_right_sigma_point (y:=y) (y':=y) (idpath _) = (idpath _).
  Proof. unfold inj_right_sigma_point. intros. 
    unfold paths_ind. unfold proj. rewrite eq_dec_refl_point.
    unfold K_dec_point. simpl.
    unfold eq_proofs_unicity_point. subst proj. 
    simpl. unfold nu_inv, comp, nu. simpl. 
    unfold paths_ind, nu_left_inv, trans_sym_eq, nu_constant.
    rewrite eq_dec_refl_point. reflexivity.
  Defined.

End PointEqdepDec.

Section PEqdepDec.
  Set Universe Polymorphism.
    
  Context {A : Type} `{EqDec A}.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    paths_ind _ (fun a _ => a = y') eq2 _ eq1.

  Remark ptrans_sym_eq : forall (x y:A) (u:x = y), comp u u = idpath y.
  Proof.
    intros.
    case u; trivial.
  Defined.

  Variable x : A.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
      | inl eqxy => eqxy
      | inr neqxy => Overture.Empty_ind (fun _ => x = y) (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    reflexivity.

    case n; trivial.
  Defined.

  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (idpath x)) v.

  Remark pnu_left_inv : forall (y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    intros.
    case u; unfold nu_inv in |- *.
    apply ptrans_sym_eq.
  Defined.

  Theorem peq_proofs_unicity : forall (y:A) (p1 p2:x = y), p1 = p2.
  Proof.
    intros.
    elim pnu_left_inv with (u := p1).
    elim pnu_left_inv with (u := p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Defined.

  Theorem pK_dec :
    forall P:x = x -> Type, P (idpath x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim peq_proofs_unicity with x (idpath x) p.
    trivial.
  Defined.

  Lemma peq_dec_refl : eq_dec x x = inl _ (idpath x).
  Proof. case eq_dec. intros. f_ap. apply peq_proofs_unicity.
    contradiction.
  Defined.

  (* On [sigma] *)
  
  Let projs (P:A -> Type) (exP:sigma A P) (def:P x) : P x :=
    match exP with
      | sigmaI x' prf =>
        match eq_dec x' x with
          | inl eqprf => paths_ind x' (fun a _ => P a) prf x eqprf
          | _ => def
        end
    end.

  Theorem inj_right_sigma :
    forall (P:A -> Type) (y y':P x),
      sigmaI P x y = sigmaI P x y' -> y = y'.
  Proof.
    intros P y y' H0.
    cut (projs (sigmaI P x y) y = projs (sigmaI P x y') y).
    unfold projs.
    case (eq_dec x x).
    intro e.
    elim e using pK_dec. trivial.

    intros.
    case n; trivial.

    case H0.
    reflexivity.
  Defined.

  Lemma inj_right_sigma_refl (P : A -> Type) (y : P x) :
    inj_right_sigma (y:=y) (y':=y) (idpath _) = (idpath _).
  Proof. unfold inj_right_sigma. intros. 
    unfold paths_ind. unfold projs. rewrite peq_dec_refl.
    unfold pK_dec. simpl.
    unfold peq_proofs_unicity. subst projs.
    simpl. unfold nu_inv, comp, nu. simpl.
    unfold paths_ind, nu_left_inv, ptrans_sym_eq, nu_constant.
    rewrite peq_dec_refl. reflexivity.
  Defined.

End PEqdepDec.

Arguments inj_right_sigma {A} {H} {x} P y y' e.

Instance eq_eqdec {A} `{EqDec A} : forall x y : A, EqDec (x = y).
Proof.
  intros. red. intros.
  exact (inl (eq_proofs_unicity x0 y0)).
Defined.

Instance eqdec_uip {A} (E : EqDec A) : UIP A :=
  fun x y e e' => eq_proofs_unicity e e'.

Instance eq_uip {A} (E : UIP A) : forall x : A, UIP (x = x).
Proof.
  intros y e e'. intros e'' ->.
  assert (Us := @UIP_shift A). compute in Us. forward Us.
  intros; apply E.
  intros. apply Us.
Qed.
