From Equations Require Import Equations.

(** Telescopes: allows treating variable arity fixpoints *)
Set Universe Polymorphism.
Import Sigma_Notations.
Set Equations Transparent.

Inductive tele : Type :=
| tip (A : Type)
| ext (A : Type) (B : A -> tele) : tele.

Equations tele_sigma (t : tele) : Type :=
tele_sigma (tip A) := A;
tele_sigma (ext A B) := @sigma A (fun x => tele_sigma (B x)).

Coercion tele_sigma : tele >-> Sortclass.

Inductive tele_val : tele -> Type :=
| tip_val {A} (a : A) : tele_val (tip A)
| ext_val {A B} (a : A) (b : tele_val (B a)) : tele_val (ext A B).

Equations tele_type : tele -> Type :=
| tip A := A -> Type;
| ext A B := forall x : A, tele_type (B x).

Equations tele_pred : tele -> Type :=
| tip A := A -> Prop;
| ext A B := forall x : A, tele_pred (B x).

Equations tele_pred_fn : tele -> Type -> Type :=
| tip A | concl := A -> concl;
| ext A B | concl := forall x : A, tele_pred_fn (B x) concl.

Equations tele_rel : tele -> tele -> Type :=
| tip A | tip B := A -> B -> Prop;
| ext A B | ext A' B' := forall (x : A) (y : A'), tele_rel (B x) (B' y);
| _ | _ := False.

Equations tele_pred_app (T : tele) (P : tele_pred T) (x : tele_sigma T) : Type :=
tele_pred_app (tip A) P a := P a;
tele_pred_app (ext A B) P &( a & b ) := tele_pred_app (B a) (P a) b.

Equations tele_type_app (T : tele) (P : tele_type T) (x : tele_sigma T) : Type :=
tele_type_app (tip A) P a := P a;
tele_type_app (ext A B) P &( a & b ) := tele_type_app (B a) (P a) b.

Equations tele_rel_app (T U : tele) (P : tele_rel T U) (x : tele_sigma T) (y : tele_sigma U) : Type :=
tele_rel_app (tip A) (tip A') P a a' := P a a';
tele_rel_app (ext A B) (ext A' B') P &( a & b ) &(a' & b') := tele_rel_app (B a) (B' a') (P a a') b b'.

Equations tele_forall (T : tele) (P : tele_type T) : Type :=
| tip A | P := forall x : A, P x;
| ext A B | P := forall x : A, tele_forall (B x) (P x).

Equations tele_forall_impl (T : tele) (P : tele_type T) (Q : tele_type T) : Type :=
| tip A | P | Q := forall x : A, P x -> Q x;
| ext A B | P | Q := forall x : A, tele_forall_impl (B x) (P x) (Q x).

Equations tele_forall_app (T : tele) (P : tele_type T) (f : tele_forall T P) (x : T) : tele_type_app T P x :=
tele_forall_app (tip A)   P f x := f x;
tele_forall_app (ext A B) P f x := tele_forall_app (B x.1) (P x.1) (f x.1) x.2.

Equations tele_forall_type_app (T : tele) (P : tele_type T)
          (fn : forall t, tele_type_app T P t) : tele_forall T P :=
| (tip A) | P | fn := fn;
| ext A B | P | fn := fun a : A => tele_forall_type_app (B a) (P a) (fun b => fn &(a & b)).

Lemma tele_forall_app_type (T : tele) (P : tele_type T) (f : forall t, tele_type_app T P t) :
  forall x, tele_forall_app T P (tele_forall_type_app T P f) x = f x.
Proof.
  induction T; simpl. reflexivity. intros [a b]. simpl.
  rewrite H. reflexivity.
Defined.

Equations tele_forall_uncurry (T : tele) (P : T -> Type) : Type :=
| (tip A) | P := forall x : A, P x;
| ext A B | P := forall x : A, tele_forall_uncurry (B x) (fun y : tele_sigma (B x) => P &(x & y)).

Equations tele_rel_pack (T U : tele) (x : tele_rel T U) : tele_sigma T -> tele_sigma U -> Prop by struct T :=
tele_rel_pack (tip A) (tip A') P := P;
tele_rel_pack (ext A B) (ext A' B') P := fun x y => tele_rel_pack (B x.1) (B' y.1) (P _ _) x.2 y.2.

Equations tele_pred_pack (T : tele) (P : tele_pred T) : tele_sigma T -> Prop :=
tele_pred_pack (tip A) P := P;
tele_pred_pack (ext A B) P := fun x => tele_pred_pack (B x.1) (P x.1) x.2.

Equations tele_pred_fn_pack (T U : tele) (P : tele_pred_fn T (tele_pred U)) : tele_sigma T -> tele_sigma U -> Prop :=
tele_pred_fn_pack (tip A) U P := fun x => tele_pred_pack U (P x);
tele_pred_fn_pack (ext A B) U P := fun x => tele_pred_fn_pack (B x.1) U (P x.1) x.2.

Definition tele_rel_curried T := tele_pred_fn T (tele_pred T).

Equations tele_forall_pack (T : tele) (P : T -> Type) (f : tele_forall_uncurry T P) (t : T) : P t :=
| (tip A) | P | f | t := f t;
| ext A B | P | f | &(a & b) := tele_forall_pack (B a) (fun b => P &(a & b)) (f a) b.

Equations tele_forall_unpack (T : tele) (P : T -> Type) (f : forall (t : T), P t) : tele_forall_uncurry T P :=
| (tip A) | P | f := f;
| ext A B | P | f := fun a : A => tele_forall_unpack (B a) (fun b => P &(a & b)) (fun b => f &(a & b)).

Lemma tele_forall_pack_unpack (T : tele) (P : T -> Type) (f : forall t, P t) :
  forall x, tele_forall_pack T P (tele_forall_unpack T P f) x = f x.
Proof.
  induction T; simpl. reflexivity. intros [a b]. simpl.
  rewrite H. reflexivity.
Defined.

Section Fix.
  Context {T : tele} (R : T -> T -> Prop).
  Context (wf : well_founded R).
  Context (P : tele_type T).

  (* (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x *)
  Definition functional_type :=
    tele_forall_uncurry T (fun x =>
      ((tele_forall_uncurry T (fun y =>
         R y x -> tele_type_app T P y))) ->
      tele_type_app T P x).

  Context (fn : functional_type).

  Lemma tele_Fix : tele_forall T P.
  Proof.
    refine (tele_forall_type_app _ _
     (@Fix (tele_sigma T) _ wf (tele_type_app T P)
           (fun x H => tele_forall_pack T _ fn x (tele_forall_unpack T _ H)))).
  Defined.
End Fix.

(* Monomorphic Inductive Acc_tel (T : tele) (R : tele_rel_curried T) (x : T) : Prop := *)
(*     Acc_intro : (tele_forall_uncurry T (fun y => tele_pred_fn_pack T T R y x -> Acc_tel T R y)) -> Acc_tel _ R x. *)

Section Fix.
  Context {T : tele} (R : T -> T -> Prop).
  Context (wf : well_founded R).
  Context (P : tele_type T).

  (* (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x *)
  Context (fn : functional_type R P).

  Lemma FixWf_unfold x :
    tele_forall_app T P (tele_Fix R wf P fn) x =
    tele_forall_pack T _ fn x
                     (tele_forall_unpack T _ (fun y _ => tele_forall_app T P (tele_Fix R wf P fn) y)).
  Proof.
    intros. unfold tele_Fix, Fix.
    rewrite tele_forall_app_type. destruct (wf x). simpl.
    f_equal. apply f_equal. extensionality y. extensionality h.
    rewrite tele_forall_app_type. apply f_equal. apply Subterm.Acc_pi.
  Defined.
End Fix.

Section TestFix.

  Definition T := ext nat (fun _ => ext nat (fun x => tip (x = x))).
  Definition R (_ : nat) (x : nat) (H : x = x) (_ : nat) (y : nat) (H' : y = y) := x < y.
  Lemma wfR : well_founded (tele_pred_fn_pack T T R).
    red. intros [n m]. simpl in *.
  Admitted.
  Definition P : tele_type T := fun _ x H => nat.

  Definition myfix : tele_forall T P.
    refine (tele_Fix _ wfR P _). unfold functional_type.
    simpl. unfold P, R.
    intros.
    destruct x0. exact 0.
    eapply H. exact 0. reflexivity. constructor.
  Defined.
End TestFix.

Definition myfix_fn := Eval compute in myfix.

Extraction Inline tele_forall_pack tele_forall_unpack tele_forall_type_app tele_Fix.
Extraction tele_Fix.

Extraction myfix.
Extraction myfix_fn.

(* Lemma existT_encode {A} {P : A -> Type} {a b : A} (p : P a) (q : P b) : *)
(*   existT _ a p = existT _ b q ->  *)
(*   { e : a = b & eq_rect a P p _ e = q}. *)
(* Proof. intros. dependent rewrite H. exists eq_refl. simpl. reflexivity. Defined. *)

(* Lemma existT_decode {A} {P : A -> Type} {a b : A} (p : P a) (q : P b) :  *)
(*   { e : a = b & eq_rect a P p _ e = q} ->  *)
(*   existT _ a p = existT _ b q. *)
(* Proof. intros. destruct H. destruct x. destruct e. reflexivity. Defined. *)

(* Lemma existT_encode_decode A {P : A -> Type} (a b : A) (p : P a) (q : P b)  *)
(*   (prf : { e : a = b & eq_rect a P p _ e = q}) : existT_encode _ _ (existT_decode _ _ prf) = prf. *)
(* Proof.  *)
(*   destruct prf; cbn. destruct x, e. cbn in *. apply eq_refl. *)
(* Defined. *)

(* Notation " x .1 " := (projT1 x) (at level 3). *)
(* Notation " x .2 " := (projT2 x) (at level 3). *)

(* Lemma existT_encode' {A} {P : A -> Type} (x y : {x : A & P x}): *)
(*   x = y -> *)
(*   { e : x.1 = y.1 & eq_rect x.1 P x.2 _ e = y.2}. *)
(* Proof. intros ->. exists eq_refl. simpl. reflexivity. Defined. *)

(* Lemma existT_decode' {A} {P : A -> Type} (x y : {x : A & P x}): *)
(*   { e : x.1 = y.1 & eq_rect x.1 P x.2 _ e = y.2} -> x = y. *)
(* Proof. intros [e1 e2]. destruct x as [x px], y as [y py]; simpl in *.  *)
(*        destruct e1, e2. reflexivity.  *)
(* Defined. *)

(* Lemma existT_decode_encode' A {P : A -> Type} (x y : {x : A & P x}) *)
(*   (prf : x = y) : existT_decode' _ _ (existT_encode' _ _ prf) = prf. *)
(* Proof.  *)
(*   destruct prf. destruct x. reflexivity.  *)
(* Qed. *)

(* Lemma existT_encode_decode' A {P : A -> Type} (x y : {x : A & P x}) *)
(*   (prf : {e : x.1 = y.1 & eq_rect x.1 P x.2 _ e = y.2}) :  *)
(*   existT_encode' _ _ (existT_decode' _ _ prf) = prf. *)
(* Proof.  *)
(*   destruct prf as [e1 e2].  *)
(*   destruct x as [x px], y as [y py].  *)
(*   simpl in *. destruct e1. destruct e2. reflexivity.  *)
(* Defined. *)

(* Lemma existT_decode_encode A {P : A -> Type} (a b : A) (p : P a) (q : P b)  *)
(*   (prf : existT _ a p = existT _ b q) : existT_decode _ _ (existT_encode _ _ prf) = prf. *)
(* Proof. apply existT_decode_encode'. Defined. *)
