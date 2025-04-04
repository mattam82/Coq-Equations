From Equations.Prop Require Import Loader.
From Equations.Prop Require Import FunctionalExtensionality.
From Equations.Prop Require Import DepElim.
From Equations.Prop Require Import Tactics.
From Equations.Prop Require Import FunctionalInduction.
(** Telescopes: allows treating variable arity fixpoints *)
Set Universe Polymorphism.
Import Sigma_Notations.
Local Open Scope equations_scope.

Set Equations Transparent.

Cumulative Inductive tele@{i} : Type :=
| tip (A : Type@{i})
| ext (A : Type@{i}) (B : A -> tele) : tele.

Register tele as equations.tele.type.
Register tip as equations.tele.tip.
Register ext as equations.tele.ext.

Section TeleSigma.
  Universe i.

  Equations tele_sigma (t : tele@{i}) : Type@{i} :=
  tele_sigma (tip A) := A ; 
  tele_sigma (ext A B) := @sigma A (fun x => tele_sigma (B x)).

  Coercion tele_sigma : tele >-> Sortclass.

  Inductive tele_val : tele@{i} -> Type@{i+1} :=
  | tip_val {A} (a : A) : tele_val (tip A)
  | ext_val {A B} (a : A) (b : tele_val (B a)) : tele_val (ext A B).

  Equations tele_pred : tele -> Type :=
  | tip A := A -> Prop;
  | ext A B := forall x : A, tele_pred (B x).

  Equations tele_rel : tele -> tele -> Type :=
  | tip A | tip B := A -> B -> Prop;
  | ext A B | ext A' B' := forall (x : A) (y : A'), tele_rel (B x) (B' y);
  | _ | _ := False.

  Equations tele_rel_app (T U : tele) (P : tele_rel T U) (x : tele_sigma T) (y : tele_sigma U) : Type :=
  tele_rel_app (tip A) (tip A') P a a' := P a a';
  tele_rel_app (ext A B) (ext A' B') P (a, b) (a', b') := tele_rel_app (B a) (B' a') (P a a') b b'.

  Universes j k.

  Equations tele_fn : tele@{i} -> Type@{j} -> Type@{k} :=
  | tip A | concl := A -> concl;
  | ext A B | concl := forall x : A, tele_fn (B x) concl.

  Equations tele_MR (T : tele@{i}) (A : Type@{j}) (f : tele_fn T A) : T -> A :=
  tele_MR (tip A)   C f := f;
  tele_MR (ext A B) C f := fun x => tele_MR (B x.1) C (f x.1) x.2.

  Equations tele_measure (T : tele@{i}) (A : Type@{i}) (f : tele_fn T A) (R : A -> A -> Prop) : T -> T -> Prop :=
  tele_measure T C f R := fun x y => R (tele_MR T C f x) (tele_MR T C f y).

  Equations tele_type : tele@{i} -> Type@{k} :=
  | tip A := A -> Type@{j};
  | ext A B := forall x : A, tele_type (B x).

  Equations tele_type_app (T : tele@{i}) (P : tele_type T) (x : tele_sigma T) : Type@{k} :=
  tele_type_app (tip A) P a := P a;
  tele_type_app (ext A B) P (a, b) := tele_type_app (B a) (P a) b.

  Equations tele_forall (T : tele@{i}) (P : tele_type T) : Type@{k} :=
  | tip A | P := forall x : A, P x;
  | ext A B | P := forall x : A, tele_forall (B x) (P x).

  Equations tele_forall_impl (T : tele@{i}) (P : tele_type T) (Q : tele_type T) : Type :=
  | tip A | P | Q := forall x : A, P x -> Q x;
  | ext A B | P | Q := forall x : A, tele_forall_impl (B x) (P x) (Q x).

  Equations tele_forall_app (T : tele@{i}) (P : tele_type T) (f : tele_forall T P) (x : T) : tele_type_app T P x :=
  tele_forall_app (tip A)   P f x := f x;
  tele_forall_app (ext A B) P f x := tele_forall_app (B x.1) (P x.1) (f x.1) x.2.

  Equations tele_forall_type_app (T : tele@{i}) (P : tele_type T)
            (fn : forall t, tele_type_app T P t) : tele_forall T P :=
  | (tip A) | P | fn := fn;
  | ext A B | P | fn := fun a : A => tele_forall_type_app (B a) (P a) (fun b => fn (a, b)).

  Lemma tele_forall_app_type (T : tele@{i}) (P : tele_type T) (f : forall t, tele_type_app T P t) :
    forall x, tele_forall_app T P (tele_forall_type_app T P f) x = f x.
  Proof.
    induction T; simpl. reflexivity. cbn. intros [a b]. simpl. rewrite H. reflexivity.
  Defined.

  Equations tele_forall_uncurry (T : tele@{i}) (P : T -> Type@{j}) : Type@{k} :=
  | tip A   | P := forall x : A, P x;
  | ext A B | P := forall x : A, tele_forall_uncurry (B x) (fun y : tele_sigma (B x) => P (x, y)).

  Equations tele_rel_pack (T U : tele) (x : tele_rel T U) : tele_sigma T -> tele_sigma U -> Prop by struct T :=
  tele_rel_pack (tip A) (tip A') P := P;
  tele_rel_pack (ext A B) (ext A' B') P := fun x y => tele_rel_pack (B x.1) (B' y.1) (P _ _) x.2 y.2.

  Equations tele_pred_pack (T : tele) (P : tele_pred T) : tele_sigma T -> Prop :=
  tele_pred_pack (tip A) P := P;
  tele_pred_pack (ext A B) P := fun x => tele_pred_pack (B x.1) (P x.1) x.2.

  Equations tele_type_unpack (T : tele) (P : tele_sigma T -> Type) : tele_type T :=
  tele_type_unpack (tip A) P := P;
  tele_type_unpack (ext A B) P := fun x => tele_type_unpack (B x) (fun y => P (x, y)).

  Equations tele_pred_fn_pack (T U : tele) (P : tele_fn T (tele_pred U)) : tele_sigma T -> tele_sigma U -> Prop :=
  tele_pred_fn_pack (tip A) U P := fun x => tele_pred_pack U (P x);
  tele_pred_fn_pack (ext A B) U P := fun x => tele_pred_fn_pack (B x.1) U (P x.1) x.2.

  Definition tele_rel_curried T := tele_fn T (tele_pred T).

  Equations tele_forall_pack (T : tele) (P : T -> Type) (f : tele_forall_uncurry T P) (t : T) : P t :=
  | (tip A) | P | f | t := f t;
  | ext A B | P | f | (a, b) := tele_forall_pack (B a) (fun b => P (a, b)) (f a) b.

  Equations tele_forall_unpack (T : tele@{i}) (P : T -> Type@{j}) (f : forall (t : T), P t) : tele_forall_uncurry T P :=
  | (tip A) | P | f := f;
  | ext A B | P | f := fun a : A => tele_forall_unpack (B a) (fun b => P (a, b)) (fun b => f (a, b)).

  Lemma tele_forall_pack_unpack (T : tele) (P : T -> Type) (f : forall t, P t) :
    forall x, tele_forall_pack T P (tele_forall_unpack T P f) x = f x.
  Proof.
    induction T; simpl. reflexivity. intros [a b]. simpl.
    rewrite H. reflexivity.
  Defined.

End TeleSigma.

Register tele_sigma as equations.tele.interp.
Register tele_measure as equations.tele.measure.

#[export]
Instance wf_tele_measure@{i j k}
         {T : tele@{i}} (A : Type@{j}) (f : tele_fn@{i j k} T A) (R : A -> A -> Prop) :
  WellFounded R -> WellFounded (tele_measure@{i j k} T A f R).
Proof.
  intros. apply Program.Wf.measure_wf. apply H.
Defined.

Section Fix.
  Universe i j k.
  Context {T : tele@{i}} (R : T -> T -> Prop).
  Context (wf : WellFounded R).
  Context (P : tele_type@{i j k} T).

  (* (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x *)
  Definition tele_fix_functional_type :=
    tele_forall_uncurry T (fun x =>
      ((tele_forall_uncurry T (fun y =>
         R y x -> tele_type_app T P y))) ->
      tele_type_app T P x).

  Context (fn : tele_fix_functional_type).

  Lemma tele_fix : tele_forall T P.
  Proof.
    refine (tele_forall_type_app _ _
     (@Subterm.FixWf (tele_sigma T) _ wf (tele_type_app T P)
           (fun x H => tele_forall_pack T _ fn x (tele_forall_unpack T _ H)))).
  Defined.
End Fix.

Register tele_fix as equations.tele.fix.
Register tele_MR as equations.tele.MR.
Register tele_fix_functional_type as equations.tele.fix_functional_type.

Register tele_type_app as equations.tele.type_app.
Register tele_forall_type_app as equations.tele.forall_type_app.
Register tele_forall_uncurry as equations.tele.forall_uncurry.
Register tele_forall as equations.tele.forall.
Register tele_forall_pack as equations.tele.forall_pack.
Register tele_forall_unpack as equations.tele.forall_unpack.

Extraction Inline tele_forall_pack tele_forall_unpack tele_forall_type_app tele_fix.

Lemma poly_f_equal@{i j} : forall (A : Type@{i}) (B : Type@{j}) (f : A -> B) (x y : A), x = y -> f x = f y.
Proof. intros. destruct H. reflexivity. Defined.

Section FixUnfold.
  Universes i j k.

  Context {T : tele@{i}} (x : T) (R : T -> T -> Prop).
  Context (wf : well_founded R).
  Context (P : tele_type@{i j k} T).

  (* (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x *)
  Context (fn : tele_fix_functional_type@{i j k} R P).

  Lemma tele_fix_unfold :
    tele_forall_app T P (tele_fix R wf P fn) x =
    tele_forall_pack T _ fn x
                     (tele_forall_unpack T _ (fun y _ => tele_forall_app T P (tele_fix R wf P fn) y)).
  Proof.
    intros. unfold tele_fix, Subterm.FixWf, Fix.
    rewrite tele_forall_app_type@{i j k}. destruct (wellfounded x). simpl.
    apply poly_f_equal@{k k}. apply poly_f_equal@{k k}. extensionality y. extensionality h.
    rewrite tele_forall_app_type@{i j k}. apply poly_f_equal@{k k}. apply Subterm.Acc_pi.
  Defined.

End FixUnfold.

Register tele_fix_unfold as equations.tele.fix_unfold.
