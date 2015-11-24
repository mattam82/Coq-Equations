Inductive TupleT : nat -> Type :=
nilT : TupleT 0
| consT {n} A : (A -> TupleT n) -> TupleT (S n).

Require Import Equations.Equations.

Ltac wf_subterm := intro;
  simp_exists;
  on_last_hyp depind; split; intros; simp_exists;
    on_last_hyp ltac:(fun H => red in H);
    [ exfalso | ];
    on_last_hyp depind;
    intuition.

Inductive Tuple : forall n, TupleT n -> Type :=
  nil : Tuple _ nilT
| cons {n A} (x : A) (F : A -> TupleT n) : Tuple _ (F x) -> Tuple _ (consT A F).

Inductive TupleMap : forall n, TupleT n -> TupleT n -> Type :=
  tmNil : TupleMap _ nilT nilT
| tmCons {n} {A B} (F : A -> TupleT n) (G : B -> TupleT n)
  : (forall x, sigT (TupleMap _ (F x) ∘ G)) -> TupleMap _ (consT A F) (consT B G).

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

(* Doesn't know how to deal with the nested TupleMap 
   Derive Subterm for TupleMap. *)

Inductive TupleMap_direct_subterm
              : ∀ (n : nat) (H H0 : TupleT n) (n0 : nat) 
                (H1 H2 : TupleT n0),
                TupleMap n H H0 → TupleMap n0 H1 H2 → Prop :=
    TupleMap_direct_subterm_0_0 : ∀ (n : nat) (H H0 : TupleT n) 
                                  (n0 : nat) (H1 H2 : TupleT n0) 
                                  (n1 : nat) (H3 H4 : TupleT n1)
                                  (x : TupleMap n H H0)
                                  (y : TupleMap n0 H1 H2)
                                  (z : TupleMap n1 H3 H4),
                                  TupleMap_direct_subterm n H H0 n0 H1 H2 x y
                                  → TupleMap_direct_subterm n0 H1 H2 n1 H3 H4
                                      y z
                                    → TupleMap_direct_subterm n H H0 n1 H3 H4
                                        x z
|   TupleMap_direct_subterm_1_1 : ∀ n {A B} (F : A -> TupleT n) (G : B -> TupleT n)
  (H : forall x, sigT (TupleMap _ (F x) ∘ G)) (x : A),
  TupleMap_direct_subterm _ _ (G (projT1 (H _))) _ _ _ (projT2 (H x)) (tmCons _ _ H).

Definition TupleMap_subterm := 
λ x y : {index : {n : nat & sigT (λ _ : TupleT n, TupleT n)} &
     TupleMap (projT1 index) (projT1 (projT2 index)) (projT2 (projT2 index))},
TupleMap_direct_subterm (projT1 (projT1 x)) (projT1 (projT2 (projT1 x)))
  (projT2 (projT2 (projT1 x))) (projT1 (projT1 y))
  (projT1 (projT2 (projT1 y))) (projT2 (projT2 (projT1 y))) 
  (projT2 x) (projT2 y).

Program Instance WellFounded_TupleMap_subterm : WellFounded TupleMap_subterm.
Solve All Obligations with wf_subterm.

Equations myComp {n} {B C : TupleT n} (tm1 : TupleMap _ B C) {A : TupleT n} (tm2 : TupleMap _ A B)
: TupleMap _ A C :=
myComp tmNil tmNil := tmNil;
myComp (tmCons G H g) (tmCons F ?(G) f)
:= tmCons _ _ (fun x => existT (fun y => TupleMap _ _ (_ y)) (projT1 (g (projT1 (f x)))) (myComp (projT2 (g (projT1 (f x)))) (projT2 (f x)))).