(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Equations Require Import Init DepElim HSets HoTTUtil.
Require Import Coq.Logic.JMeq.
Require Import HoTT.Basics.Overture.
Require Import HoTT.Basics.Decidable.

Local Open Scope list_scope.

Set Universe Polymorphism.

Instance eqdec_hset (A : Type) `(EqDec A) : HSet A.
Proof.
  red. red. apply eq_proofs_unicity.
Defined.

(** Standard instances. *)

Instance unit_eqdec : EqDec Unit.
Proof. eqdec_proof. Defined.

(* TODO These instance proofs should use eqdec_proof. *)

Require Import HoTT.Types.Bool.
Definition Bool_rect := Bool_ind.

Instance bool_eqdec : EqDec Bool.
Proof. unfold EqDec. intros; destruct x,y; try (apply inl; reflexivity).
apply inr; intro.
  refine (
    match X in Id _ b return
      match b with
      | true => Unit
      | false => _
      end
    with
    | id_refl => tt
    end).
apply inr; intro.
  refine (
    match X in Id _ b return
      match b with
      | false => Unit
      | true => _
      end
    with
    | id_refl => tt
    end).
Defined.

Require Import HoTT.Spaces.Nat.
Instance nat_eqdec : EqDec nat.
Proof. unfold EqDec. intros.
  destruct (dec_paths x y).
  - rewrite p; apply inl; reflexivity.
  - apply inr; intro. destruct n. rewrite X; reflexivity. Defined.

Instance prod_eqdec {A B} `(EqDec A) `(EqDec B) : EqDec (prod A B).
Proof. unfold EqDec; intros. destruct x,y. destruct (eq_dec fst fst0), (eq_dec snd snd0).
  - apply inl. rewrite i, i0; reflexivity.
  - apply inr; intro; apply e.
    apply (Id_rec _ (fst,snd) (fun a _ => Id snd (Coq.Init.Datatypes.snd a))
                  id_refl (fst0,snd0) X).
  - apply inr; intro; apply e.
    apply (Id_rec _ (fst,snd) (fun a _ => Id fst (Coq.Init.Datatypes.fst a))
                  id_refl (fst0,snd0) H1).
  - apply inr; intro; apply e.
    apply (Id_rec _ (fst,snd) (fun a _ => Id fst (Coq.Init.Datatypes.fst a))
                  id_refl (fst0,snd0) H1). Defined.

Local Lemma eqDecIsDecidablePaths {A} (X : EqDec A) : DecidablePaths A.
Proof. intros x y. destruct (eq_dec x y).
  - apply Datatypes.inl. rewrite i; reflexivity.
  - apply Datatypes.inr. intro H. rewrite H in e.
    destruct (e id_refl). Defined.

Require Import HoTT.Types.Sum.
Instance sum_eqdec {A B} `(x : EqDec A) `(y : EqDec B) : EqDec (A + B).
Proof. unfold EqDec; intros.
  set(x' := eqDecIsDecidablePaths x); set(y' := eqDecIsDecidablePaths y).
  destruct (dec_paths x0 y0).
  - apply inl; rewrite p. constructor.
  - apply inr; intro. rewrite X in n; destruct (n idpath). Defined.

Instance list_eqdec {A} `(EqDec A) : EqDec (list A).
Proof. unfold EqDec. intro x. induction x; intros; destruct y.
  - apply inl; reflexivity.
  - apply inr; intro.
    refine (match X in Id _ c return
      match c with
      | nil => Unit
      | _::_ => _
      end
    with
    | id_refl => tt
    end).
  - apply inr; intro.
    refine (match X in Id _ c return
      match c with
      | nil => _
      | _::_ => Unit
      end
    with
    | id_refl => tt
    end).
  - destruct (eq_dec a a0).
    + rewrite i. destruct (IHx y).
      * apply inl. rewrite i0; reflexivity.
      * apply inr. intro; apply e.
        apply(Id_rec _ (a0::x) (fun z _ => Id x (HoTTUtil.tl z)) id_refl (a0::y) X).
    + apply inr; intro. apply e.
      apply (Id_rec _ (a::x)
                    (fun z _ =>
                      match HoTTUtil.hd z with
                      | None => Id a a0
                      | Some h => Id a h
                      end)
                    id_refl (a0::y) H0).
Defined.

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
