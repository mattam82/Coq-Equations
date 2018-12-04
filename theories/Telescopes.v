From Equations Require Import Equations.

(** Telescopes: allows treating variable arity fixpoints *)
Set Universe Polymorphism.
Import Sigma_Notations.
Set Equations Transparent.

Cumulative Inductive tele@{i} : Type :=
| tip (A : Type@{i})
| ext (A : Type@{i}) (B : A -> tele) : tele.

Section TeleSigma.
  Universe i.

  Equations tele_sigma (t : tele@{i}) : Type@{i} :=
  tele_sigma (tip A) := A;
  tele_sigma (ext A B) := @sigma A (fun x => tele_sigma (B x)).

  Coercion tele_sigma : tele >-> Sortclass.

  Inductive tele_val : tele@{i} -> Type@{i+1} :=
  | tip_val {A} (a : A) : tele_val (tip A)
  | ext_val {A B} (a : A) (b : tele_val (B a)) : tele_val (ext A B).

  Universes j k.

  Equations tele_type : tele@{i} -> Type@{k} :=
  | tip A := A -> Type@{j};
  | ext A B := forall x : A, tele_type (B x).

  Equations tele_pred : tele -> Type :=
  | tip A := A -> Prop;
  | ext A B := forall x : A, tele_pred (B x).

  Equations tele_fn : tele@{i} -> Type@{j} -> Type :=
  | tip A | concl := A -> concl;
  | ext A B | concl := forall x : A, tele_fn (B x) concl.

  Equations tele_rel : tele -> tele -> Type :=
  | tip A | tip B := A -> B -> Prop;
  | ext A B | ext A' B' := forall (x : A) (y : A'), tele_rel (B x) (B' y);
  | _ | _ := False.

  Equations tele_type_app (T : tele@{i}) (P : tele_type T) (x : tele_sigma T) : Type@{k} :=
  tele_type_app (tip A) P a := P a;
  tele_type_app (ext A B) P &( a & b ) := tele_type_app (B a) (P a) b.

  Equations tele_rel_app (T U : tele) (P : tele_rel T U) (x : tele_sigma T) (y : tele_sigma U) : Type :=
  tele_rel_app (tip A) (tip A') P a a' := P a a';
  tele_rel_app (ext A B) (ext A' B') P &( a & b ) &(a' & b') := tele_rel_app (B a) (B' a') (P a a') b b'.

  Equations tele_forall (T : tele@{i}) (P : tele_type T) : Type@{k} :=
  | tip A | P := forall x : A, P x;
  | ext A B | P := forall x : A, tele_forall (B x) (P x).

  Equations tele_forall_impl (T : tele@{i}) (P : tele_type T) (Q : tele_type T) : Type :=
  | tip A | P | Q := forall x : A, P x -> Q x;
  | ext A B | P | Q := forall x : A, tele_forall_impl (B x) (P x) (Q x).

  Equations tele_forall_app (T : tele@{i}) (P : tele_type T) (f : tele_forall T P) (x : T) : tele_type_app T P x :=
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

  Equations tele_forall_uncurry (T : tele@{i}) (P : T -> Type@{j}) : Type@{k} :=
  | tip A   | P := forall x : A, P x;
  | ext A B | P := forall x : A, tele_forall_uncurry (B x) (fun y : tele_sigma (B x) => P &(x & y)).

  Equations tele_rel_pack (T U : tele) (x : tele_rel T U) : tele_sigma T -> tele_sigma U -> Prop by struct T :=
  tele_rel_pack (tip A) (tip A') P := P;
  tele_rel_pack (ext A B) (ext A' B') P := fun x y => tele_rel_pack (B x.1) (B' y.1) (P _ _) x.2 y.2.

  Equations tele_pred_pack (T : tele) (P : tele_pred T) : tele_sigma T -> Prop :=
  tele_pred_pack (tip A) P := P;
  tele_pred_pack (ext A B) P := fun x => tele_pred_pack (B x.1) (P x.1) x.2.

  Equations tele_type_unpack (T : tele) (P : tele_sigma T -> Type) : tele_type T :=
  tele_type_unpack (tip A) P := P;
  tele_type_unpack (ext A B) P := fun x => tele_type_unpack (B x) (fun y => P &(x & y)).

  Equations tele_pred_fn_pack (T U : tele) (P : tele_fn T (tele_pred U)) : tele_sigma T -> tele_sigma U -> Prop :=
  tele_pred_fn_pack (tip A) U P := fun x => tele_pred_pack U (P x);
  tele_pred_fn_pack (ext A B) U P := fun x => tele_pred_fn_pack (B x.1) U (P x.1) x.2.

  Definition tele_rel_curried T := tele_fn T (tele_pred T).

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

  Equations tele_MR (T : tele@{i}) (A : Type@{j}) (f : tele_fn@{i} T A) : T -> A :=
  tele_MR (tip A)   C f := f;
  tele_MR (ext A B) C f := fun x => tele_MR (B x.1) C (f x.1) x.2.
End TeleSigma.

Section Fix.
  Universe i j k.
  Context {T : tele@{i}} (R : T -> T -> Prop).
  Context (wf : well_founded R).
  Context (P : tele_type@{i j k} T).

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
Lemma tele_forall_uncurry' (T : tele) (P : tele_type T) (Q : T -> Type)
      (f : tele_forall_uncurry T (fun x => Q x -> tele_type_app T P x))
      (H : forall x, Q x) : tele_forall T P.
(* | tip A | P | Q | f := f; *)
(* | ext A | P | Q | f := f; *)

induction T; simpl in *. intros. apply f. apply H.
intros x. eapply X. apply f. simpl. intros. eapply H.
Defined.

Section Fix.
  Context {T : tele} (R : T -> T -> Prop).
  Context (wf : well_founded R).
  Context (P : tele_type T).

  (* (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall x : A, P x *)
  Context (fn : functional_type R P).


  Let foo x :=
    tele_forall_unpack _ _ (fun y (_ : R y x) => tele_forall_app T P (tele_Fix R wf P fn) y).

  Lemma FixWf_unfold :
    tele_Fix R wf P fn = tele_forall_uncurry' T P _ fn foo.
  Proof.
    intros. unfold tele_Fix, Fix.
    unfold tele_forall_uncurry'. simpl.
    induction T. simpl.
  Admitted.

  (*   rewrite tele_forall_app_type. destruct (wf x). simpl. *)
  (*   f_equal. apply f_equal. extensionality y. extensionality h. *)
  (*   rewrite tele_forall_app_type. apply f_equal. apply Subterm.Acc_pi. *)
  (* Defined. *)

  (* Lemma FixWf_unfold x : *)
  (*   tele_forall_app T P (tele_Fix R wf P fn) x = *)
  (*   tele_forall_pack T _ fn x *)
  (*                    (tele_forall_unpack T _ (fun y _ => tele_forall_app T P (tele_Fix R wf P fn) y)). *)
  (* Proof. *)
  (*   intros. unfold tele_Fix, Fix. *)
  (*   rewrite tele_forall_app_type. destruct (wf x). simpl. *)
  (*   f_equal. apply f_equal. extensionality y. extensionality h. *)
  (*   rewrite tele_forall_app_type. apply f_equal. apply Subterm.Acc_pi. *)
  (* Defined. *)
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

  Equations myfix_unfold (n m : nat) (H : m = m) : nat :=
    | x | 0   | _ := 0;
    | x | S n | _ := myfix 0 n eq_refl.


  Lemma myfix_unfold_eq n m H : myfix n m H = myfix_unfold n m H.
  Proof.
    unfold myfix. rewrite FixWf_unfold.
    simpl. destruct m; try reflexivity.
  Qed.

End TestFix.

Definition myfix_fn := Eval compute in myfix.

Extraction Inline tele_forall_pack tele_forall_unpack tele_forall_type_app tele_Fix.
