Require Import Equations.Equations.
Test Universe Polymorphism.

Inductive TupleT : nat -> Type :=
| nilT : TupleT 0
| consT {n} A : (A -> TupleT n) -> TupleT (S n).

Inductive Tuple : forall n, TupleT n -> Type :=
  nil : Tuple _ nilT
| cons {n A} (x : A) (F : A -> TupleT n) : Tuple _ (F x) -> Tuple _ (consT A F).

Inductive TupleMap : forall n, TupleT n -> TupleT n -> Type :=
  tmNil : TupleMap _ nilT nilT
| tmCons {n} {A B} (F : A -> TupleT n) (G : B -> TupleT n)
  : (forall x, sigT (TupleMap _ (F x) ∘ G)) -> TupleMap _ (consT A F) (consT B G).

Unset Printing Primitive Projection Parameters.

Derive Signature for TupleMap.

Program Instance TupleMap_depelim n T U : DependentEliminationPackage (TupleMap n T U)
:= { elim_type := ∀ (P : forall n t t0, TupleMap n t t0 -> Type),
   P _ _ _ tmNil ->
  (∀ n A B (F : A -> TupleT n) (G : B -> TupleT n)
    (s : ∀ x, sigT (TupleMap _ (F x) ∘ G))
    (r : ∀ x, P _ _ _ (projT2 (s x))),
    P _ _ _ (tmCons F G s))
  -> ∀ (tm : TupleMap n T U), P _ _ _ tm }.
Next Obligation.
  revert n T U tm.
  fix IH 4.
  intros.
  Ltac destruct' x := destruct x.
  on_last_hyp destruct'; [ | apply X0 ]; auto. 
Defined.

(* Doesn't know how to deal with the nested TupleMap  *)
(* Derive Subterm for TupleMap. *)

Inductive TupleMap_direct_subterm
  : ∀ (n : nat) (H H0 : TupleT n) (n0 : nat) 
      (H1 H2 : TupleT n0),
    TupleMap n H H0 → TupleMap n0 H1 H2 → Prop :=
|   TupleMap_direct_subterm_1_1 : ∀ n {A B} (F : A -> TupleT n) (G : B -> TupleT n)
  (H : forall x, sigT (TupleMap _ (F x) ∘ G)) (x : A),
  TupleMap_direct_subterm _ _ (G (projT1 (H _))) _ _ _ (projT2 (H x)) (tmCons _ _ H).
Hint Constructors TupleMap_direct_subterm : subterm_relation.
Definition TupleMap_subterm := Relation_Operators.clos_trans _
  (λ x y : {index : {n : nat & sigma _ (λ _ : TupleT n, TupleT n)} &
                   TupleMap (pr1 index) (pr1 (pr2 index)) (pr2 (pr2 index))},
          TupleMap_direct_subterm _ _ _ _ _ _ (pr2 x) (pr2 y)).

Program Instance WellFounded_TupleMap_subterm : WellFounded TupleMap_subterm.

Solve All Obligations with solve_subterm.
  
Hint Extern 3 (TupleMap_subterm _ _) =>
  unfold TupleMap_subterm; simpl : subterm_relation.
Hint Extern 5 => progress simpl : subterm_relation.

Equations myComp {n} {B C : TupleT n} (tm1 : TupleMap _ B C) {A : TupleT n} (tm2 : TupleMap _ A B)
: TupleMap _ A C :=
myComp tm1 tm2 by rec tm1 TupleMap_subterm :=
myComp tmNil tmNil := tmNil;
myComp (tmCons G H g) (tmCons F ?(G) f) :=
  tmCons _ _ (fun x => existT (fun y => TupleMap _ _ (_ y)) (projT1 (g (projT1 (f x))))
                           (myComp (projT2 (g (projT1 (f x)))) (projT2 (f x)))).
