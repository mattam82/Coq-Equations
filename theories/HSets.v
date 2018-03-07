(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Equations.Init.
Require Import Coq.Program.Equality.

(** Decidable equality.

   We redevelop the derivation of [K] from decidable equality on [A] making
   everything transparent and moving to [Type] so that programs using this 
   will actually be computable inside Coq. *)

Set Implicit Arguments.

Set Universe Polymorphism.

Class HProp A := is_hprop : forall x y : A, Id x y.

Class HSet A := is_hset : forall {x y : A}, HProp (Id x y).

Inductive sum (A : Type) (B : Type) := inl : A -> sum A B | inr : B -> sum A B.

Set Warnings "-notation-overridden".
Import Id_Notations.
Import Sigma_Notations.
Local Open Scope equations_scope.

Definition ap {A : Type} {B : Type} (f : A -> B) {x y : A} (p : x = y) : f x = f y :=
  match p with id_refl => id_refl end.

Definition Id_rew (A : Type) (a : A) (P : A -> Type) (p : P a) (y : A) (e : a = y) : P y :=
  match e with id_refl => p end.
                             
Definition dec_eq@{i} {A : Type@{i}} (x y : A) := sum (x = y) (x = y -> Empty@{i}).

Class EqDec@{i} (A : Type@{i}) := eq_dec : forall x y : A, sum (x = y) (x = y -> Empty@{i}).

(** Tactic to solve EqDec goals, destructing recursive calls for the recursive 
  structure of the type and calling instances of eq_dec on other types. *)

Ltac eqdec_loop t u :=
  (left; reflexivity) || 
  (solve [right; intro He; inversion He]) ||
  (let x := match t with
             | context C [ _ ?x ] => constr:(x)
             end
    in
    let y := match u with
             | context C [ _ ?y ] => constr:(y)
             end
    in
    let contrad := let Hn := fresh in
                   intro Hn; right; intro He; apply Hn; inversion He; reflexivity in
    let good := intros ->;
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
      [ H : forall z, dec_eq x z |- _ ] =>
      case (H y); [good|contrad]
    | [ H : forall z, sum (Id _ z) _ |- _ ] =>
      case (H y); [good|contrad]
    | _ => case (eq_dec x y); [good|contrad]
    end) || idtac.

Ltac eqdec_proof := try red; intros;
  match goal with
    |- dec_eq ?x ?y =>
    revert y; induction x; intros until y; depelim y;
    match goal with
      |- dec_eq ?x ?y => eqdec_loop x y
    end
   | |- sum (Id ?x ?y) _ =>
    revert y; induction x; intros until y; depelim y;
    match goal with
      |- sum (Id ?x ?y) _ => eqdec_loop x y
    end
  end.

(** Derivation of principles on sigma types whose domain is decidable. *)

Section EqdepDec.

  Context {A : Type} `{EqDec A}.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    Id_rect _ _ (fun a _ => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = id_refl y.
  Proof.
    intros.
    case u; compute. apply id_refl.
  Defined.

  Variable x : A.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
      | inl eqxy => eqxy
      | inr neqxy => Empty_rect (fun _ => _) (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    reflexivity.

    case e; trivial.
  Defined.

  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (id_refl x)) v.

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
    forall P:x = x -> Type, P (id_refl x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity with x (id_refl x) p.
    trivial.
  Defined.

  Lemma eq_dec_refl : eq_dec x x = inl _ (id_refl x).
  Proof.
    case eq_dec; intros. apply ap. apply eq_proofs_unicity. 
    elim e. apply id_refl.
  Defined.

  (** The corollary *)
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
    case (eq_dec x x).
    intro e.
    elim e using K_dec. trivial.

    intros.
    case e; reflexivity.

    case X; reflexivity.
  Defined.

  Lemma inj_right_sigma_refl (P : A -> Type) (y : P x) :
    inj_right_sigma (y:=y) (y':=y) (id_refl _) = (id_refl _).
  Proof. unfold inj_right_sigma. intros. 
    unfold paths_ind. unfold projs. rewrite eq_dec_refl.
    unfold K_dec. simpl.
    unfold eq_proofs_unicity. subst projs.
    simpl. unfold nu_inv, comp, nu. simpl.
    unfold paths_ind, nu_left_inv, trans_sym_eq, nu_constant.
    rewrite eq_dec_refl. reflexivity.
  Defined.

End EqdepDec.

Definition transport {A : Type} {P : A -> Type} {x y : A} (p : x = y) : P x -> P y :=
  match p with id_refl => fun h => h end.

Lemma sigma_eq (A : Type) (P : A -> Type) (x y : sigma A P) :
  x = y -> &{ p : (x.1 = y.1) & transport p x.2 = y.2 }.
Proof.
  intros H; destruct H.
  destruct x as [x px]. simpl.
  refine &(id_refl & id_refl).
Defined.  

Theorem inj_sigma_r {A : Type} `{H : HSet A} :
  forall (P:A -> Type) {x} {y y':P x},
    sigmaI P x y = sigmaI P x y' -> y = y'.
Proof.
  intros P x y y' [H' H'']%sigma_eq. cbn in *.
  pose (is_hset H' id_refl).
  apply (transport (P:=fun h => transport h y = y') i H'').
Defined.

Definition apd {A} {B : A -> Type} (f : forall x : A, B x) {x y : A} (p : x = y) :
  transport p (f x) = f y.
Proof. now destruct p. Defined.

Definition apd_eq {A} {x y : A} (p : x = y) {z} (q : z = x) :
  transport (P:=@Id A z) p q = id_trans q p.
Proof. now destruct p, q. Defined.

Lemma id_trans_sym {A} (x y z : A) (p : x = y) (q : y = z) (r : x = z) :
  id_trans p q = r -> q = id_trans (id_sym p) r.
Proof. now destruct p, q. Defined.

Lemma hprop_hset {A} (h : HProp A) : HSet A.
Proof.
  intro x.
  set (g y := h x y).
  intros y z w.
  assert (forall y z (p : y = z), p = id_trans (id_sym (g y)) (g z)).
  intros. apply id_trans_sym. destruct (apd_eq p (g y0)). apply apd.
  rewrite X. now rewrite (X _ _ z).
Qed.

(** Proof that equality proofs in 0-truncated types are connected *)
Lemma hset_pi {A} `{HSet A} (x y : A) (p q : x = y) (r : p = q) : is_hset p q = r.
Proof.
  red in H.
  pose (hprop_hset (H x y)).
  apply h.
Defined.

Lemma is_hset_refl {A} `{HSet A} (x : A) : is_hset (id_refl x) id_refl = id_refl.
Proof.
  apply hset_pi.
Defined.  

Lemma inj_sigma_r_refl (A : Type) (H : HSet A) (P : A -> Type) x (y : P x) :
  inj_sigma_r (y:=y) (y':=y) (id_refl _) = (id_refl _).
Proof.
  unfold inj_sigma_r. intros.
  simpl. now rewrite is_hset_refl.
Defined.

Theorem K {A} `{HSet A} (x : A) :
  forall P:x = x -> Type, P (id_refl x) -> forall p:x = x, P p.
Proof.
  intros. exact (transport (is_hset id_refl p) X).
Defined.
