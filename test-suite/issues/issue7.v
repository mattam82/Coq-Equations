Set Warnings "-notation-overridden".
Require Import ssreflect.
Require Import Utf8 Program.
Require Import Equations.Equations.

Inductive TupleT : nat -> Type :=
| nilT : TupleT 0
| consT {n} A : (A -> TupleT n) -> TupleT (S n).

Derive Signature NoConfusion NoConfusionHom for TupleT.

Inductive Tuple : forall n, TupleT n -> Type :=
  nil : Tuple _ nilT
| cons {n A} (x : A) (F : A -> TupleT n) : Tuple _ (F x) -> Tuple _ (consT A F).

Derive Signature NoConfusionHom for Tuple.

Inductive TupleMap@{i j} : forall n, TupleT n -> TupleT n -> Type@{j} :=
  tmNil : TupleMap _ nilT nilT
| tmCons {n} {A B : Type@{i}} (F : A -> TupleT n) (G : B -> TupleT n)
  : (forall x, sigT (TupleMap _ (F x) ∘ G)) -> TupleMap _ (consT A F) (consT B G).

Derive Signature NoConfusion for TupleMap.
Derive NoConfusionHom for TupleMap.

Equations TupleMap_noconf {n : nat} {x y : TupleT n}
  (f g : TupleMap n x y) : Prop :=
TupleMap_noconf tmNil tmNil := True;
TupleMap_noconf (tmCons _ _ fn) (tmCons F G fn') := fn = fn'.

Unset Printing Primitive Projection Parameters.

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
  intros. destruct tm; [ | apply X0 ]; auto.
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
Derive Signature for TupleMap_direct_subterm.
#[local] Hint Constructors TupleMap_direct_subterm : subterm_relation.

Import Sigma_Notations.

Definition TupleMap_subterm := Relation_Operators.clos_trans _
  (λ x y : Σ index : Σ (n : nat) (_ : TupleT n), TupleT n,
           TupleMap (pr1 index) (pr1 (pr2 index)) (pr2 (pr2 index)),
          TupleMap_direct_subterm _ _ _ _ _ _ (pr2 x) (pr2 y)).
#[local] Hint Unfold TupleMap_subterm : subterm_relation.

Program Instance WellFounded_TupleMap_subterm : WellFounded TupleMap_subterm.

(* Solve All Obligations with solve_subterm. *)
  

Ltac wf_subterm := intro;
  simp_sigmas;
  on_last_hyp depind; split; intros; simp_sigmas;
    on_last_hyp ltac:(fun H => red in H);
    [ exfalso | ];
    on_last_hyp depind;
    intuition.

Next Obligation.
  unfold TupleMap_subterm.
  apply Transitive_Closure.wf_clos_trans.
  red. intros ((n&H1&H2)&map). simpl in map.
  match goal with |- context [ Acc ?R _ ] => set(rel:=R) end.
  move rel at top.
  set (foo := elim (A:= TupleMap n H1 H2)). simpl in foo. induction map using foo.
  + constructor. intros ((n'&H1'&H2')&map'). simpl in *.
    move=> H. red in H. simpl in H. depelim H.
    
  + constructor. intros ((n'&H1'&H2')&map'). simpl in *.
    unfold rel; cbn. intros H; depelim H. apply r.
Defined.

Derive NoConfusion for Tuple.

#[local] Hint Extern 100 => progress simpl : Below.

Time Equations myComp {n} {B C : TupleT n} (tm1 : TupleMap _ B C) {A : TupleT n} (tm2 : TupleMap _ A B)
: TupleMap _ A C :=
myComp tmNil tmNil := tmNil;
myComp (tmCons _ H g) (tmCons F G f) :=
  tmCons _ _ (fun x => existT (fun y => TupleMap _ _ (_ y)) (projT1 (g (projT1 (f x))))
                           (myComp (projT2 (g (projT1 (f x)))) (projT2 (f x)))).

Time Equations myComp_wf {n} {B C : TupleT n} (tm1 : TupleMap _ B C) {A : TupleT n} (tm2 : TupleMap _ A B)
: TupleMap _ A C by wf (signature_pack tm1) TupleMap_subterm :=
myComp_wf tmNil tmNil := tmNil;
myComp_wf (n:=_) (tmCons (B:=C) _ H g) (tmCons (n:=n) (A:=A) (B:=B) F G f) :=
  tmCons _ _ (fun x => existT (fun y => TupleMap _ _ (_ y)) (projT1 (g (projT1 (f x))))
                           (myComp_wf (projT2 (g (projT1 (f x)))) (projT2 (f x)))).

Print Assumptions myComp.
(* Print Assumptions myComp_wf. *)