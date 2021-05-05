Set Warnings "-notation-overridden".
From Equations Require Import Equations.
Require Import Utf8 Arith Compare_dec List Lia.
Require Import Relation_Operators.
Arguments clos_trans [A].
Import Sigma_Notations.
Set Equations Transparent.

Require Import fin.

Equations lift_fin {n} (k : nat) (f : fin n) : fin (S n) :=
  lift_fin 0 f := fs f;
  lift_fin (S k) fz := fz;
  lift_fin (S k) (fs f) := fs (lift_fin k f).
Open Scope list_scope.
Derive Signature for Forall2.
#[local] Hint Constructors Forall2 : core.
Local Open Scope program_scope.
Local Open Scope equations_scope.
Arguments map {A B}.
(* end hide *)

Require Import Equations.Prop.Subterm.

Derive Subterm for nat.

(* Hint Extern 30 (@NoCycle ?A (NoCycle_WellFounded ?R ?wfr) _ _) => *)
(*   hnf ; typeclasses eauto with subterm_relation : typeclass_instances. *)

Lemma nocycle_nat x : S x = x -> False.
  simplify ?.
Qed.

Goal forall x, S (S x) = x -> False.
  intros x.
  simplify ?.
Qed.

Inductive tree := leaf : tree | node : tree -> tree -> tree.
Derive NoConfusion Subterm for tree.

Goal forall x y, node x y = x -> False.
  intros x y.
  simplify ?.
Qed.

Goal forall x y, node y (node y x) = x -> False.
  intros x y.
  simplify ?.
Qed.

Goal forall x y, node y (node y x) = x -> False.
  intros x y.
  simplify ?.
Qed.

Goal forall x y, x = node y (node y x) -> False.
  intros x y.
  simplify ?. Show Proof.
Qed.

Goal forall x y z, x = node (node y z) (node y x) -> False.
  intros x y z.
  simplify ?.
Qed.

(** It would be hard to come up with an example for vector, but for indexed terms
    in some language, yes *)
Derive NoConfusion Subterm for list.

Reserved Notation " x ∈ s " (at level 70, s at level 10).
Polymorphic Inductive In {A} (x : A) : list A -> Type :=
| here {xs} : x ∈ (x :: xs)
| there {y xs} : x ∈ xs -> x ∈ (y :: xs)
(* begin hide *)
  where "x ∈ s" := (In x s).
Derive Signature NoConfusion for In.
Arguments here {A x xs}.
Arguments there {A x y xs} _.
(* end hide *)

Set Equations With UIP.

Set Universe Polymorphism.
Section InNoconfusion.

  Context {A} {hset : UIP A}.

  Global Instance list_UIP: UIP (list A).
  Proof.
    intros inx inx' e. depelim e. induction inx.
    - now simplify *.
    - simplify $. simpl. simplify ?.
      intros. specialize (IHinx e). simpl. destruct IHinx.
      reflexivity.
  Defined.

  Instance In_UIP (x : A) l : UIP (x ∈ l).
  Abort. (* Impossible! As defined, x ∈ l is not proof irrelevant, it contains an index into the list *)
End InNoconfusion.
Unset Universe Polymorphism.
(* end hide *)

Inductive type : Set :=
| tbool | tunit | tarrow : type -> type -> type.
Derive NoConfusion Subterm for type.

#[export]
Instance type_uip : UIP type.
Proof.
  red. intros x y ->. induction y; try repeat (simplify ?; simpl); trivial.
  intros. specialize (IHy1 e'). specialize (IHy2 e). destruct IHy1. destruct IHy2.
  reflexivity.
Qed.

Inductive term : forall (ctx : list type), type -> Set :=
| ttrue {ctx} : term ctx tbool
| tfalse{ctx} : term ctx tbool
| tvar {ctx} {τ} (x : τ ∈ ctx) : term ctx τ
| tapp {ctx} {τ τ'} (f : term ctx (tarrow τ τ')) (a : term ctx τ) : term ctx τ
| tlam {ctx} {τ τ'} (abs : term (τ :: ctx) τ') : term ctx (tarrow τ τ').

Derive Signature for term.
Derive NoConfusionHom for term.

(* FIXME subterm and non-uniform indices and universe issue... *)
(*
Derive Subterm for term.

Lemma wft : WellFounded term_subterm.
  solve_subterm. destruct index. simpl in *.
  revert H. simplify *.
  destruct index. simpl in *. revert H. simplify *.
Defined.

Existing Instance wft.

Goal forall ctx τ (f : term ctx (tarrow τ τ)) (a : term ctx τ), signature_pack (tapp f a) = signature_pack a -> False.
Proof.
  intros *.
  simplify <>.
Qed.

Goal forall ctx τ (f : term ctx (tarrow τ τ)) (a : term ctx τ), tapp f a = a -> False.
Proof.
  intros *.
  refine (simplify_ind_pack (A:=Σ ctx : list type, type) (fun x => term x.1 x.2) (ctx, τ) _ _ (fun _ => False) _).
  simplify <>.
Defined.

*)