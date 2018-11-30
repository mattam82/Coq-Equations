
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

Import Sigma_Notations.

Definition TupleMap_subterm := Relation_Operators.clos_trans _
  (λ x y : &{index : &{n : nat & sigma _ (λ _ : TupleT n, TupleT n)} &
                   TupleMap (pr1 index) (pr1 (pr2 index)) (pr2 (pr2 index))},
          TupleMap_direct_subterm _ _ _ _ _ _ (pr2 x) (pr2 y)).
Require Import DepElimDec.
Derive Signature for TupleMap_direct_subterm.

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
  depelim map.
  + constructor. intros ((n'&H1'&H2')&map'). simpl in *.
    intros H. red in H. simpl in H.
    depelim H.
    
  + constructor. intros ((n'&H1'&H2')&map'). simpl in *.
    intros H; red in H. simpl in H.
    depelim H. simpl in *. apply r.
Qed.

Print Assumptions WellFounded_TupleMap_subterm.

Hint Extern 3 (TupleMap_subterm _ _) =>
  unfold TupleMap_subterm; simpl : subterm_relation.
Hint Extern 5 => progress simpl : subterm_relation.

(* Global Transparent simplification_existT2 simplification_existT2_dec *)
(*        simplification_sigma2 simplification_sigma2_dec *)
(*        simplification_heq simplification_K simplification_K_dec *)
(*        simplify_ind_pack forK Id_simplification_sigma2. *)

(* Hint Unfold simplification_sigma2 simplification_existT2 simplification_heq *)
(*   simplification_existT2_dec simplification_K simplification_K_dec : equations. *)
(* Derive Signature for Tuple. *)
(* Derive NoConfusion for Tuple. *)
(* Derive Signature for TupleMap. *)
(* Derive NoConfusion for TupleMap. *)

(* Ltac simpl_equations ::= idtac. *)
  (* repeat ((red_eq || rewrite_sigma2_refl); simpl). *)
  (* repeat ((rewrite_sigma2_refl || autounfold_one with equations); simpl). *)
  (* repeat (hnf_eq ; unfold_equations; rewrite_refl_id). *)
  (* repeat (repeat (simpl; (rewrite_refl_id; simpl) || hnf_eq); *)
  (*         try progress autounfold with equations). *)

Time Equations myComp {n} {B C : TupleT n} (tm1 : TupleMap _ B C) {A : TupleT n} (tm2 : TupleMap _ A B)
: TupleMap _ A C :=
myComp tmNil tmNil := tmNil;
myComp (tmCons _ H g) (tmCons F G f) :=
  tmCons _ _ (fun x => existT (fun y => TupleMap _ _ (_ y)) (projT1 (g (projT1 (f x))))
                           (myComp (projT2 (g (projT1 (f x)))) (projT2 (f x)))).

Time Equations myComp_wf {n} {B C : TupleT n} (tm1 : TupleMap _ B C) {A : TupleT n} (tm2 : TupleMap _ A B)
: TupleMap _ A C by rec (signature_pack tm1) TupleMap_subterm :=
myComp_wf tmNil tmNil := tmNil;
myComp_wf (tmCons _ H g) (tmCons F G f) :=
  tmCons _ _ (fun x => existT (fun y => TupleMap _ _ (_ y)) (projT1 (g (projT1 (f x))))
                           (myComp_wf (projT2 (g (projT1 (f x)))) (projT2 (f x)))).

Print Assumptions myComp.
Print Assumptions myComp_wf.