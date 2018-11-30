(* begin hide *)
(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2017 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)
(* end hide *)
(** * Normalization of Simply Typed Lambda-Calculus through Hereditary Substitutions.

  Uses extrinsic encoding of terms, with de Bruijn indices, lifting and
  substitution. Derive hereditary substitution function justified by a
  well-founded order on typable terms and conclude with a normalizer building
  beta-short eta-long normal forms, typable in a bidirectional type system. *)

Require Import Program.
Require Equations.Equations.
Import DepElim FunctionalInduction.
Require Import Omega.
Require Import List Utf8.
From Equations Require Import EqDec.

Derive Signature for le CompareSpec.

Inductive term := 
| Var (n : nat)
| Lambda (t : term)
| App (t u : term)
| Pair (t u : term)
| Fst (t : term) | Snd (t : term)
| Tt.

Derive NoConfusion Subterm EqDec for term.

Coercion Var : nat >-> term.

Delimit Scope term_scope with term.
Bind Scope term_scope with term.

Notation " @( f , x ) " := (App (f%term) (x%term)).
Notation " 'λ' t " := (Lambda (t%term)) (at level 0).
Notation " << t , u >> " := (Pair (t%term) (u%term)).

Parameter atomic_type : Set.
Parameter atomic_type_eqdec : EqDec.EqDec atomic_type.
Existing Instance atomic_type_eqdec.

Inductive type :=
| atom (a : atomic_type)
| product (a b : type)
| unit
| arrow (a b : type).

Derive NoConfusion Subterm EqDec for type.

Coercion atom : atomic_type >-> type.
Notation " x × y " := (product x y) (at level 90).
Notation " x ---> y " := (arrow x y) (at level 30).

Require Import Arith.

Equations lift (k n : nat) (t : term) : term :=
lift k n (Var i) with Nat.compare i k := {
  | Lt := Var i ;
  | _ := Var (i + n) } ;
lift k n (Lambda t) := Lambda (lift (S k) n t) ;
lift k n (App t u) := @(lift k n t, lift k n u) ;
lift k n (Pair t u) := << lift k n t, lift k n u >> ;
lift k n (Fst t) := Fst (lift k n t) ;
lift k n (Snd t) := Snd (lift k n t) ;
lift k n Tt := Tt.

Tactic Notation "absurd"  tactic(tac) := elimtype False; tac.

Ltac term_eq := 
  match goal with
    | |- Var _ = Var _ => f_equal ; omega
    | |- @eq nat _ _ => omega || absurd omega
    | |- lt _ _ => omega || absurd omega
    | |- le _ _ => omega || absurd omega
    | |- gt _ _ => omega || absurd omega
    | |- ge _ _ => omega || absurd omega
  end.

Hint Extern 4 => term_eq : term.

Ltac term := typeclasses eauto with term core arith.

Ltac do_rewrites :=
  repeat
    match goal with
        H : ?lhs = ?rhs |- context [?lhs] => rewrite H; clear H
    end.

Ltac crush := do_rewrites; auto; try term.

Lemma lift0 k t : lift k 0 t = t.
Proof.
  funelim (lift k 0 t); term || rewrite ?H; crush.
Qed.
Hint Rewrite lift0 : lift.
Require Import Omega.

Lemma lift_k_lift_k k n m t : lift k n (lift k m t) = lift k (n + m) t.
Proof.
  funelim (lift k m t); intros; simp lift; try rewrite H ; try rewrite H0; auto.
       
  destruct (Nat.compare_spec n0 k0); try discriminate. subst.
  case_eq (Nat.compare (k0 + m) k0); intro H; simp lift; try term.
  rewrite Nat.compare_lt_iff in H; term.
  rewrite Heq; simp lift; term.

  rewrite Heq. rewrite Nat.compare_gt_iff in Heq. simp lift.
  destruct (Nat.compare_spec (n0 + m) k0); try discriminate; simp lift; term.
Qed.
Hint Rewrite lift_k_lift_k : lift.

Equations subst (k : nat) (t : term) (u : term) : term :=
subst k (Var i) u with Nat.compare i k := {
  | Eq := lift 0 k u ;
  | Lt := i ;
  | Gt := Var (pred i) } ;
subst k (Lambda t) u := Lambda (subst (S k) t u) ;
subst k (App a b) u := @(subst k a u, subst k b u) ;
subst k (Pair a b) u := << subst k a u, subst k b u >> ;
subst k (Fst t) u := Fst (subst k t u) ;
subst k (Snd t) u := Snd (subst k t u) ;
subst k Tt _ := Tt.

Lemma substnn n t : subst n n t = lift 0 n t.
Proof. funelim (subst n n t) ; try rewrite H ; try rewrite H0; simp lift; auto.
  rewrite Nat.compare_lt_iff in Heq; absurd omega.
  rewrite Nat.compare_gt_iff in Heq; absurd omega.
Qed.
Hint Rewrite substnn : subst.
Notation ctx := (list type).

Delimit Scope lf with lf.

Reserved Notation " Γ |-- t : A " (at level 70, t, A at next level).

Inductive types : ctx -> term -> type -> Prop :=
| axiom Γ i : i < length Γ -> (Γ |-- i : nth i Γ unit) 

| abstraction Γ A B t :
  A :: Γ |-- t : B -> Γ |-- λ t : A ---> B

| application Γ A B t u : 
  Γ |-- t : A ---> B -> Γ |-- u : A -> Γ |-- @(t, u) : B

| unit_intro Γ : Γ |-- Tt : unit

| pair_intro Γ A B t u :
  Γ |-- t : A -> Γ |-- u : B ->
    Γ |-- << t , u >> : (A × B)

| pair_elim_fst Γ A B t : Γ |-- t : (A × B) -> Γ |-- Fst t : A

| pair_elim_snd Γ A B t : Γ |-- t : (A × B) -> Γ |-- Snd t : B

where "Γ |-- i : A " := (types Γ i A).

Derive Signature for types.

Notation " [ t ] u " := (subst 0 u t) (at level 10).

Notation " x @ y " := (app x y) (at level 30, right associativity).

Lemma nth_length {A} x t (l l' : list A) : nth (length l) (l @ (t :: l')) x = t.
Proof. induction l; simpl; auto. Qed.

Hint Constructors types : term.

Lemma nat_compare_elim (P : nat -> nat -> comparison -> Prop)
  (PEq : forall i, P i i Eq)
  (PLt : forall i j, i < j -> P i j Lt)
  (PGt : forall i j, i > j -> P i j Gt) :
  forall i j, P i j (Nat.compare i j).
Proof. intros. case (Nat.compare_spec i j); intros; subst; auto. Qed.

Lemma nth_extend_left {A} (a : A) n (l l' : list A) : nth n l a = nth (length l' + n) (l' @ l) a.
Proof. induction l'; auto. Qed.

Lemma nth_app_l {A} (a : A) {n} (l l' : list A) : n < length l -> nth n (l @ l') a = nth n l a.
Proof.
  revert l l' n; induction l; intros; auto. depelim H. destruct n; trivial.
  simpl. eapply IHl. simpl in H. omega.
Qed.

Lemma nth_app_r {A} (a : A) {n} (l l' : list A) : length l <= n -> 
  nth n (l @ l') a = nth (n - length l) l' a.
Proof.
  revert l l' n; induction l; intros; auto. simpl in H. depelim H; auto.
  destruct n; simpl in H. depelim H. simpl; apply IHl; omega.
Qed.

Lemma nth_extend_middle {A} (a : A) n (l l' l'' : list A) : 
  match Nat.compare n (length l') with
    | Lt => nth n (l' @ l) a = nth n (l' @ l'' @ l) a
    | _ => nth n (l' @ l) a = nth (n + length l'') (l' @ l'' @ l) a
  end.
Proof.
  assert (foo:=Nat.compare_spec n (length l')).
  depelim foo; fold (length l') in H;
  try rewrite H0; try rewrite H. rewrite <- nth_extend_left.
  replace (length l'') with (length l'' + 0) by auto with arith. rewrite <- nth_extend_left.
  replace (length l') with (length l' + 0) by auto with arith.
  now rewrite <- nth_extend_left.

  clear H0. now rewrite !nth_app_l by trivial.
  clear H0. rewrite !nth_app_r by omega. f_equal. omega.
Qed.
  
Hint Rewrite <- app_assoc in_app_iff in_inv : list.

Lemma type_lift Γ t T Γ' : Γ' @ Γ |-- t : T -> 
  forall Γ'', Γ' @ Γ'' @ Γ |-- lift (length Γ') (length Γ'') t : T.
Proof.
  intros H.
  depind H; intros; simp lift; eauto with term.

  generalize (nth_extend_middle unit i Γ0 Γ' Γ'').
  destruct Nat.compare; intros H'; rewrite H'; simp lift;
    apply axiom; autorewrite with list in H |- *; omega.
  
  apply abstraction. rewrite app_comm_cons. now apply IHtypes. 
Qed.

Lemma type_lift1 Γ t T A : Γ |-- t : T -> A :: Γ |-- lift 0 1 t : T.
Proof. intros. apply (type_lift Γ t T [] H [A]). Qed.

Lemma type_liftn Γ Γ' t T : Γ |-- t : T -> Γ' @ Γ |-- lift 0 (length Γ') t : T.
Proof. intros. apply (type_lift Γ t T [] H Γ'). Qed.
Hint Resolve type_lift1 type_lift type_liftn : term.

Ltac crush ::= do_rewrites; simpl; do_rewrites; auto; try term.

Lemma app_cons_snoc_app {A} l (a : A) l' : l ++ (a :: l') = (l ++ a :: nil) ++ l'.
Proof. induction l; crush. Qed.

Hint Extern 5 => progress (simpl ; autorewrite with list) : term.
Ltac term ::= simp lift subst; try typeclasses eauto with core term.

Lemma substitutive Γ t T Γ' u U : 
  (Γ' @ (U :: Γ)) |-- t : T -> Γ |-- u : U ->
  Γ' @ Γ |-- subst (length Γ') t u : T.
Proof with term.
  intros H. depind H; term. intros.
  
  (* Var *)
  assert (spec:=Nat.compare_spec i (length Γ')).
  depelim spec; try fold (length Γ') in H1; subst;
  try rewrite H1; try rewrite H2 ; simp subst.

  (* Eq *)
  generalize (type_lift Γ0 u U [] H0 Γ'); simpl; intros.
  rewrite app_cons_snoc_app, app_nth1, app_nth2; try (simpl; omega).
  now rewrite <- minus_n_n. term.

  (* Lt *) 
  rewrite app_nth1 by omega. rewrite <- (app_nth1 _ Γ0); term.

  (* Gt *)
  rewrite app_nth2; term.
  change (U :: Γ0) with ((cons U nil) @ Γ0). rewrite app_nth2; term.
  simpl. rewrite (nth_extend_left unit _ Γ0 Γ').
  replace (length Γ' + (i - length Γ' - 1)) with (pred i); term.
  apply axiom. autorewrite with list in H |- *. simpl in H. omega.

  (* Abstraction *)
  intros. apply abstraction. now eapply (IHtypes _ _ _ (A :: Γ')).
Qed.

Lemma subst1 Γ t T u U : U :: Γ |-- t : T -> Γ |-- u : U -> Γ |-- subst 0 t u : T.
Proof. intros; now apply (substitutive Γ t T [] u U). Qed.
  
Reserved Notation " t --> u " (at level 55, right associativity).

Inductive reduce : term -> term -> Prop :=
| red_beta t u : @((Lambda t) , u) --> subst 0 t u
| red_fst t u : Fst << t , u >> --> t
| red_snd t u : Snd << t , u >> --> u

where " t --> u " := (reduce t u). 
Derive Signature for reduce.

Require Import Relations.

Definition reduces := clos_refl_trans term reduce.
Notation " t -->* u " := (reduces t u) (at level 55).

Require Import Setoid.

Instance: Transitive reduces.
Proof. red; intros. econstructor 3; eauto. Qed.

Instance: Reflexive reduces.
Proof. red; intros. econstructor 2; eauto. Qed.

Inductive value : term -> Prop :=
| val_var (i : nat) : value i
| val_unit : value Tt
| val_pair a b : value a -> value b -> value << a, b >>
| val_lambda t : value λ t.
Derive Signature for value.

Hint Constructors value : term.

Inductive reduce_congr : relation term :=
| reduce1 t u : reduce t u -> reduce_congr t u
| reduce_app_l t t' u : reduce_congr t t' ->
  reduce_congr (@(t, u)) (@(t', u))
| reduce_app_r t u u' : reduce_congr u u' ->
  reduce_congr (@(t, u)) (@(t, u'))
| reduce_pair_l t t' u : reduce_congr t t' ->
  reduce_congr (<< t, u >>) (<< t', u >>)
| reduce_pair_r t u u' : reduce_congr u u' ->
  reduce_congr (<< t, u >>) (<< t, u' >>)
| reduce_fst t t' : reduce_congr t t' -> reduce_congr (Fst t) (Fst t')
| reduce_snd t t' : reduce_congr t t' -> reduce_congr (Snd t) (Snd t').
Derive Signature for reduce_congr.

Ltac find_empty := 
  match goal with
      [ H : _ |- _ ] => solve [ depelim H ]
  end.

Lemma preserves_red1 Γ t τ : Γ |-- t : τ → forall u, t --> u → Γ |-- u : τ.
Proof.
  intros H; induction H; intros t' redtt'; term; try find_empty; depelim redtt'.
  apply subst1 with A. now depelim H. apply H0.
  now depelim H.
  now depelim H.
Qed.

Lemma preserves_redpar Γ t τ : Γ |-- t : τ → forall u, reduce_congr t u → Γ |-- u : τ.
Proof.
  intros H. induction H; intros t' rtt'; depelim rtt'; term; try find_empty. 

  depelim H1. depelim H. eapply subst1; eauto.

  depelim H0; depelim H; term.
  depelim H0; depelim H; term.
Qed.

Lemma subject_reduction Γ t τ : Γ |-- t : τ → forall u, t -->* u → Γ |-- u : τ.
Proof. induction 2; eauto using preserves_red1. Qed.
Hint Constructors reduce reduce_congr : term.
Lemma progress_ t τ : nil |-- t : τ → (exists t', reduce_congr t t') \/ value t.
Proof.
  intros H; depind H; auto with term.

  destruct IHtypes1 as [[t' tt']|vt].
  left; eauto with term.
  destruct IHtypes2 as [[u' uu']|vu].
  left; eauto with term.
  depelim H; [depelim H|depelim vt..].
  left. exists ([u]t). eauto with term. 

  destruct IHtypes1 as [[t' tt']|vt]; eauto with term.
  destruct IHtypes2 as [[u' uu']|vu]; eauto with term.

  destruct IHtypes as [[t' tt']|vt]; eauto with term.
  depelim vt; depelim H;
  eauto with term. depelim H.

  destruct IHtypes as [[t' tt']|vt]; eauto with term.
  depelim vt; depelim H;
  eauto with term. depelim H.
Qed.

Reserved Notation " Γ |-- t => A " (at level 70, t, A at next level).
Reserved Notation " Γ |-- t <= A " (at level 70, t, A at next level).

Inductive atomic : type -> Prop :=
| atomic_atom a : atomic (atom a).

Derive Signature for atomic.
Hint Constructors atomic : term.

Equations(nocomp) atomic_dec (t : type) : { atomic t } + { ~ atomic t } :=
atomic_dec (atom a) := left (atomic_atom a) ;
atomic_dec _ := right _.

  Solve Obligations with intros; intro H; inversion H. 

Inductive check : ctx -> term -> type -> Prop :=
| abstraction_check Γ A B t :
  A :: Γ |-- t <= B ->
  Γ |-- λ t <= A ---> B

| pair_intro_check Γ A B t u :
  Γ |-- t <= A -> Γ |-- u <= B ->
    Γ |-- << t , u >> <= (A × B)

| unit_intro_check Γ : Γ |-- Tt <= unit

| check_synth Γ t T : atomic T -> Γ |-- t => T -> Γ |-- t <= T

with synthetize : ctx -> term -> type -> Prop :=

| axiom_synth Γ i : i < length Γ -> 
  Γ |-- i => nth i Γ unit
 
| application_synth {Γ A B t u} : 
  Γ |-- t => A ---> B -> Γ |-- u <= A -> Γ |-- @(t, u) => B

| pair_elim_fst_synth {Γ A B t} : Γ |-- t => (A × B) -> Γ |-- Fst t => A

| pair_elim_snd_synth {Γ A B t} : Γ |-- t => (A × B) -> Γ |-- Snd t => B

where "Γ |-- i => A " := (synthetize Γ i A)
and  "Γ |-- i <= A " := (check Γ i A).
Derive Signature for check synthetize.

Hint Constructors synthetize check : term.

Scheme check_mut_ind := Elimination for check Sort Prop
  with synthetize_mut_ind := Elimination for synthetize Sort Prop.

Combined Scheme check_synthetize from check_mut_ind, synthetize_mut_ind.

Lemma synth_arrow {Γ t T} : forall A : Prop, Γ |-- λ (t) => T -> A.
Proof. intros A H. depelim H. Qed.

Lemma synth_pair {Γ t u T} : forall A : Prop, Γ |-- << t, u >> => T -> A.
Proof. intros A H. depelim H. Qed.

Lemma synth_unit {Γ T} : forall A : Prop, Γ |-- Tt => T -> A.
Proof. intros A H. depelim H. Qed.

Hint Extern 3 => 
  match goal with
    | H : ?Γ |-- ?t => ?T |- _ => apply (synth_arrow _ H) || apply (synth_pair _ H) || apply (synth_unit _ H)
  end : term.

Lemma check_types : (forall Γ t T, Γ |-- t <= T -> Γ |-- t : T)
with synthetizes_types : (forall Γ t T, Γ |-- t => T -> Γ |-- t : T).
Proof. intros. destruct H; try econstructor; term.
  intros. destruct H; try solve [ econstructor; term ].
Qed.

Hint Resolve check_types synthetizes_types : term.

Inductive normal : term -> Prop :=
| normal_unit : normal Tt
| normal_pair a b : normal a -> normal b -> normal << a, b >>
| normal_abs t : normal t -> normal λ t
| normal_neutral r : neutral r -> normal r

with neutral : term -> Prop :=
| neutral_var i : neutral (Var i)
| neutral_fst t : neutral t -> neutral (Fst t)
| neutral_snd t : neutral t -> neutral (Snd t)
| neutral_app t n : neutral t -> normal n -> neutral (@(t, n)).

Derive Signature for normal neutral.
Hint Constructors normal neutral : term.

Lemma check_lift_gen Δ t T (H : Δ |-- t <= T) : forall Γ Γ', Δ = Γ' @ Γ ->
  forall Γ'', Γ' @ Γ'' @ Γ |-- lift (length Γ') (length Γ'') t <= T
with synthetize_lift_gen Δ t T (H : Δ |-- t => T) : forall Γ Γ', Δ = Γ' @ Γ ->
  forall Γ'', Γ' @ Γ'' @ Γ |-- lift (length Γ') (length Γ'') t => T.
Proof.
  destruct H; intros; simp lift. 

  econstructor. 
  change (S (length Γ')) with (length (A :: Γ')). change (A :: Γ' @ Γ'' @ Γ0) with ((A :: Γ') @ Γ'' @ Γ0).
  eapply check_lift_gen; try eassumption. subst. rewrite app_comm_cons; subst; try eassumption; trivial.
  
  econstructor; eapply check_lift_gen; eassumption.
  econstructor. 
  
  econstructor. eassumption.
  eapply synthetize_lift_gen; eassumption.
       
  destruct H; intros; simp lift; try solve [econstructor; term].
  clear check_lift_gen synthetize_lift_gen. subst.
  generalize (nth_extend_middle unit i Γ0 Γ' Γ'').
  destruct Nat.compare; intros H'; rewrite H'; simp lift; apply axiom_synth; autorewrite with list in H |- *; omega.
Qed.

Definition check_lift Γ t T Γ' (H : Γ' @ Γ |-- t <= T) : 
  forall Γ'', Γ' @ Γ'' @ Γ |-- lift (length Γ') (length Γ'') t <= T :=
  check_lift_gen (Γ' @ Γ) _ _ H _ _ eq_refl.
Definition synthetize_lift Γ t T Γ' (H : Γ' @ Γ |-- t => T) :
  forall Γ'', Γ' @ Γ'' @ Γ |-- lift (length Γ') (length Γ'') t => T :=
  synthetize_lift_gen (Γ' @ Γ) _ _ H _ _ eq_refl.

Lemma check_lift1 {Γ t T A} : Γ |-- t <= T -> A :: Γ |-- lift 0 1 t <= T.
Proof. intros. apply (check_lift Γ t T [] H [A]). Qed.

Lemma synth_lift1 {Γ t T A} : Γ |-- t => T -> A :: Γ |-- lift 0 1 t => T.
Proof. intros. apply (synthetize_lift Γ t T [] H [A]). Qed.
Hint Resolve @check_lift1 @synth_lift1 : term.

Lemma check_lift_ctx {Γ t T Γ'} : Γ |-- t <= T -> Γ' @ Γ |-- lift 0 (length Γ') t <= T.
Proof. intros. apply (check_lift Γ t T [] H Γ'). Qed.

Lemma synth_lift_ctx {Γ t T Γ'} : Γ |-- t => T -> Γ' @ Γ |-- lift 0 (length Γ') t => T.
Proof. intros. apply (synthetize_lift Γ t T [] H Γ'). Qed.
Hint Resolve @check_lift_ctx @synth_lift_ctx : term.

Equations(nocomp) η (a : type) (t : term) : term :=
η (atom _) t := t ;
η (product a b) t := << η a (Fst t), η b (Snd t) >> ;
η (arrow a b) t := (Lambda (η b @(lift 0 1 t, η a 0)))%term ;
η unit t := Tt.

Lemma checks_arrow Γ t A B : Γ |-- t <= A ---> B → ∃ t', t = λ t' ∧ A :: Γ |-- t' <= B.
Proof. intros H; inversion H; subst.
  exists t0; term.
  inversion H0.
Qed.

Lemma normal_lift {t k n} : normal t → normal (lift k n t) 
  with neutral_lift {t k n} : neutral t -> neutral (lift k n t).
Proof. destruct 1; simp lift; constructor; term.
  destruct 1; simp lift; try (constructor; term).
  destruct Nat.compare; term.
Qed.
Hint Resolve @normal_lift @neutral_lift : term.


Lemma check_normal {Γ t T} : Γ |-- t <= T -> normal t
 with synth_neutral {Γ t T} : Γ |-- t => T -> neutral t.
Proof. destruct 1; constructor; term. destruct 1; constructor; term. Qed.
Hint Resolve @check_normal @synth_neutral : term.

Lemma eta_expand Γ t A : neutral t → Γ |-- t => A -> Γ |-- η A t <= A.
Proof. revert Γ t; induction A; intros; simp η; constructor; term.

  assert(0 < length (A1 :: Γ)) by (simpl; omega).
  specialize (IHA1 (A1 :: Γ) 0 (neutral_var _) (axiom_synth (A1 :: Γ) 0 H1)).
  apply (IHA2 (A1 :: Γ) @(lift 0 1 t, η A1 0)); term.
Qed.

Lemma η_normal : forall Γ A t, neutral t -> Γ |-- t => A -> normal (η A t).
Proof. intros. now apply eta_expand in H0; term. Qed.

(** Going to use the subterm order *)

Ltac Below.rec ::= Subterm.rec_wf_eqns.
Require Import Arith Wf_nat.
Instance wf_nat : Classes.WellFounded lt := lt_wf.

Hint Constructors Subterm.lexprod : subterm_relation.

Derive Signature for Acc.
Notation lexicographic R S := (Subterm.lexprod _ _ R S).

From Equations Require Import EqDec.

Definition her_order : relation (type * term * term) :=
  lexicographic (lexicographic type_subterm term_subterm) term_subterm.  

Hint Unfold her_order : subterm_relation.

Obligation Tactic := program_simpl.

Arguments exist [A] [P].

Definition hereditary_type (t : type * term * term) :=
  (term * option { u : type | u = (fst (fst t)) \/ type_subterm u (fst (fst t)) })%type.

Inductive IsLambda {t} : hereditary_type t -> Set :=
| isLambda abs a b prf : IsLambda (Lambda abs, Some (exist (arrow a b) prf)).

Equations(nocomp) is_lambda {t} (h : hereditary_type t) : IsLambda h + term :=
is_lambda (pair (Lambda abs) (Some (exist (arrow a b) prf))) := inl (isLambda abs a b prf) ;
is_lambda (pair t' _) := inr t'.

Lemma is_lambda_inr {t} (h : hereditary_type t) : forall t', is_lambda h = inr t' -> fst h = t'.
Proof.
  destruct h. funelim (is_lambda (t0, o)); simpl; intros; try congruence.
Qed.

Inductive IsPair {t} : hereditary_type t -> Set :=
| isPair u v a b prf : IsPair (Pair u v, Some (exist (product a b) prf)).

Equations(nocomp) is_pair {t} (h : hereditary_type t) : IsPair h + term :=
is_pair (pair (Pair u v) (Some (exist (product a b) prf))) := inl (isPair u v a b prf) ;
is_pair (pair t' _) := inr t'.
  
Lemma is_pair_inr {t} (h : hereditary_type t) : forall t', is_pair h = inr t' -> fst h = t'.
Proof.
  destruct h. funelim (is_pair (t0, o)); simpl; intros; try congruence.
Qed.

Lemma nth_extend_right {A} (a : A) n (l l' : list A) : n < length l -> 
  nth n l a = nth n (l @ l') a.
Proof. revert n l'. induction l; simpl; intros; auto. depelim H. destruct n; auto.
  apply IHl. auto with arith.
Qed.

Definition her_type (t : type * term * term) :=
  let u' := fst (fst t) in
   { u : type | u = u' \/ type_subterm u u' }.

Remove Hints t_step : subterm_relation.
Remove Hints Subterm.clos_trans_stepr : subterm_relation.

Ltac apply_step :=
  match goal with
    |- clos_trans ?A ?R ?x ?y => not_evar y; eapply t_step
  end.
Hint Extern 30 (clos_trans _ _ _ _) => apply_step : subterm_relation.

Lemma clos_trans_inv {A} R (x y z : A) :
  clos_trans A R y z → clos_trans A R x y → clos_trans A R x z.
Proof. eauto using t_trans. Qed.

Ltac apply_transitivity :=
  match goal with
    |- clos_trans ?A ?R ?x ?y =>
    not_evar x; not_evar y; eapply clos_trans_inv
  end.
Hint Extern 31 (clos_trans _ _ _ _) => apply_transitivity : subterm_relation.

Equations hereditary_subst (t : type * term * term) (k : nat) :
  term * option (her_type t)
  by rec t her_order :=

hereditary_subst (pair (pair A a) t) k with t := {
  | Var i with Nat.compare i k := {
    | Eq := (lift 0 k a, Some (exist A _)) ;
    | Lt := (Var i, None) ;
    | Gt := (Var (pred i), None) } ;

  | Lambda t' := (Lambda (fst (hereditary_subst (A, a, t') (S k))), None) ;

  | App f arg with hereditary_subst (A, a, f) k := {
    | p with is_lambda p := {
        | inl (isLambda f' A' B' prf) :=
          let (f'', y) := hereditary_subst (A', fst (hereditary_subst (A, a, arg) k), f') 0 in
            (f'', Some (exist B' _)) ;
        | inr f' := (@(f', fst (hereditary_subst (A, a, arg) k)), None) } } ;

  | Pair i j :=
    (<< fst (hereditary_subst (A, a, i) k), fst (hereditary_subst (A, a, j) k) >>, None) ;

  | Fst t' with hereditary_subst (A, a, t') k := {
    | p with is_pair p := {
      | inl (isPair u v a' b' prf) := (u, Some (exist a' _)) ;
      | inr p' := (Fst p', None) } } ;

  | Snd t' with hereditary_subst (A, a, t') k := {
    | p with is_pair p := {
      | inl (isPair u v a' b' prf) := (v, Some (exist b' _)) ;
      | inr p' := (Snd p', None) } } ;

  | Tt := (Tt, None) }.

Solve Obligations with
   unfold her_type;
   intros; constructor 2; do 2 constructor.

Next Obligation.
  destruct prf; subst; eauto 10 with subterm_relation.
Defined.

Hint Unfold her_type : subterm_relation.

Obligation Tactic := idtac.

Solve Obligations with
  unfold her_type;
  simpl; intros;
  destruct prf; subst; eauto 10 with subterm_relation.

Solve Obligations.

Hint Unfold const : subterm_relation.

Solve All Obligations.
Ltac autoh :=
  unfold type_subterm in * ; try typeclasses eauto with hereditary_subst subterm_relation.
Ltac simph :=
  try (rewrite_strat (innermost (hints hereditary_subst)));
  autoh.

Hint Transparent type_subterm : subterm_relation.

Obligation Tactic := idtac.
Next Obligation.
Proof.
  intros.
  Subterm.rec_wf_rel hsubst t her_order.
  depelim t. depelim p. simph.
  constructor. depelim t1.
  constructor.
  destruct (Nat.compare n k); try constructor.

  simph. 

  constructor; autoh.

  set(foo:=(hereditary_subst (t, t0, t1_1) k)). clearbody foo.
  constructor.
  set(fr:=is_lambda foo). clearbody fr.
  depelim fr. depelim i.
  rewrite_strat (innermost (hints hereditary_subst)).
  constructor. autoh.

  simpl in prf. apply hsubst. 
  intuition subst. autoh.
  autoh.

  simph. 

  simph.

  constructor. autoh. 
  constructor.
  destruct (is_pair (hereditary_subst (t, t0, t1) k)).
  destruct i; simph.
  simph.

  constructor. autoh. 
  constructor.
  destruct (is_pair (hereditary_subst (t, t0, t1) k)).
  destruct i; simph.
  simph.

  simph.
Defined.

Ltac invert_term := 
  match goal with
    | [ H : check _ (Lambda _) _ |- _ ] => depelim H
    | [ H : check _ (Pair _ _) _ |- _ ] => depelim H
    | [ H : check _ Tt _ |- _ ] => depelim H
    | [ H : types _ ?t _ |- _ ] =>
      match t with
        | Var _ => depelim H
        | Lambda _ => depelim H
        | App _ _ => depelim H
        | Pair _ _ => depelim H
        | Fst _ => depelim H
        | Snd _ => depelim H
        | Tt => depelim H
      end
  end.

Set Regular Subst Tactic.

Lemma hereditary_subst_type Γ Γ' t T u U : Γ |-- u : U -> Γ' @ (U :: Γ) |-- t : T ->
  forall t' o, hereditary_subst (U, u, t) (length Γ') = (t', o) ->
    (Γ' @ Γ |-- t' : T /\ (forall ty prf, o = Some (exist ty prf) -> ty = T)).
Proof.
  intros. revert H1.
  funelim (hereditary_subst (U, u, t) (length Γ'));
    simpl_dep_elim; subst;
    try (split; [ (intros; try discriminate) | solve [ intros; discriminate ] ]).

  invert_term. simpl in *. simplify_IH_hyps. apply abstraction.
  specialize (H Γ (A :: Γ')). simpl in H. simplify_IH_hyps.
  on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
  simplify_IH_hyps.
  apply H; auto.

  on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
  on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
  depelim H2. constructor. now apply H. now apply H0.
  depelim H0. term.

  (* Var *)
  depelim H0.
  apply Nat.compare_eq in Heq; subst i.
  rewrite !nth_length. split. term. intros.
  noconf H1. auto.
 
  (* Lt *)
  apply Nat.compare_lt_iff in Heq. depelim H0.
  replace (nth i (Γ' @ (U :: Γ)) unit) with (nth i (Γ' @ Γ) unit).
  constructor. rewrite app_length. auto with arith.
  now do 2 rewrite <- nth_extend_right by auto. 
  
  (* Gt *)
  pose (substitutive _ _ _ _ _ _ H0 H).
  simp subst in t. rewrite Heq in t. simp subst in t.

  (* App *)
  simpl in *.
  on_call (hereditary_subst (U, t1, u)) ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
  on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
  noconf H3. simpl in H0.
  depelim H2.
  specialize (H _ A H1 H2_0).
  specialize (Hind _ (A ---> B) H1). rewrite Heq in Hind.
  specialize (Hind H2_ _ _ eq_refl).
  depelim Hind.
  noconf H2.
  depelim H1.
  destruct H.
  specialize (H0 _ [] _ _ _ _ H H1).
  simplify_IH_hyps.
  destruct H0 as [H0 H4].
  split; auto.
  intros ty prf0 Heq'.
  noconf Heq'. auto.

  (* App no redex *)
  apply is_lambda_inr in Heq. revert Heq.
  on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
  intros. subst t2. depelim H1.
  apply application with A; eauto.
  eapply Hind; eauto.
  destruct_call hereditary_subst.
  eapply H; eauto.

  simpl in *.
  (* Fst redex *)
  depelim H0. specialize (Hind _ _ H H0).
  rewrite Heq in Hind. specialize (Hind _ _ eq_refl).
  destruct Hind. depelim H1. intuition auto.
  simplify_IH_hyps. noconf H1.
  now noconf H2.

  (* Fst no redex *)
  apply is_pair_inr in Heq. revert Heq.
  on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
  simplify_IH_hyps. simpl in *. depelim H0. intros.
  specialize (Hind _ _ H H0); eauto.
  destruct Hind. subst t2. now apply pair_elim_fst with B.

  (* Snd redex *)
  depelim H0. specialize (Hind _ _ H H0).
  rewrite Heq in Hind. specialize (Hind _ _ eq_refl).
  destruct Hind. depelim H1. intuition auto.
  simplify_IH_hyps. noconf H1.
  now noconf H2.

  (* Snd no redex *)
  apply is_pair_inr in Heq. revert Heq.
  on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
  intros Ht2; subst t2. simplify_IH_hyps. simpl in *. depelim H0.
  specialize (Hind _ _ H H0); eauto. now apply pair_elim_snd with A.
Qed.

Print Assumptions hereditary_subst_type.
                                 
Instance: subrelation eq (flip impl).
Proof. reduce. subst; auto. Qed.

Lemma nth_pred Γ' Γ U n : n > length Γ' -> nth (pred n) (Γ' @ Γ) unit = nth n (Γ' @ (U :: Γ)) unit.
Proof.
  revert_until Γ'. induction Γ'; intros.
  
  destruct n; auto. depelim H.
  destruct n; auto. simpl pred. simpl.
  rewrite <- IHΓ'. destruct n; auto. simpl in H. depelim H. depelim H.
  simpl in *; omega.
Qed.

Lemma hereditary_subst_subst U u t Γ' :
  (forall Γ T, Γ |-- u <= U ->
    match hereditary_subst (U, u, t) (length Γ') with
      | (t', Some (exist ty _)) =>
         ((Γ' @ (U :: Γ) |-- t <= T -> Γ' @ Γ |-- t' <= T /\ ty = T) /\
          (Γ' @ (U :: Γ) |-- t => T -> Γ' @ Γ |-- t' <= T /\ ty = T))
      | (t', None) =>
        (Γ' @ (U :: Γ) |-- t <= T -> Γ' @ Γ |-- t' <= T) /\
        (Γ' @ (U :: Γ) |-- t => T -> Γ' @ Γ |-- t' => T)
    end).
Proof.
  funelim (hereditary_subst (U, u, t) (length Γ')); simpl in *.
  let Hind := fresh "Hind" in rename H into Hind; intros ?? Hu.
  simpl. simpl in *.

  (** Lambda *)
  - on_call hereditary_subst
            ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    split; intros Hsyn; [| elim (synth_arrow False Hsyn)].

    invert_term. constructor. 
    specialize (Hind U _ _ (A :: Γ') eq_refl). simpl in *.
    specialize (Hind _ B Hu).
    destruct o as [[ty prf]|], Hind as [Hind0 Hind1].
    apply Hind0; eauto. eauto.
    elim (synth_arrow False H0).

  (** Pairs *)
  - do 2 on_call hereditary_subst
          ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    split; intros Hsyn; [|elim (synth_pair False Hsyn)].
    invert_term.
    specialize (H0 _ B H1). specialize (H _ A H1).
    destruct o as [[ty prf]|], o0 as [[ty' prf']|], H, H0;
      destruct_conjs; constructor; eauto.
    now apply H. now apply H0. now apply H. now apply H0.

    elim (synth_pair False H3).

  (* Unit *)
  - split; intros Hsyn; [|elim (synth_unit False Hsyn)].
    depelim Hsyn. term.
    elim (synth_unit False H1).

  (* Var: eq *)
  - apply Nat.compare_eq in Heq; subst n.
    split; intros Hsyn; depelim Hsyn; rewrite ?nth_length.
    depelim H1; rewrite !nth_length.
    now split; term. split; term.
 
  (* Lt *)
  - apply Nat.compare_lt_iff in Heq.
    split; intros Hsyn; depelim Hsyn;
    [depelim H1;constructor;auto|];
    (rewrite nth_app_l by omega; rewrite <- nth_app_l with (l':=Γ) by omega;
     constructor; rewrite app_length; auto with arith). 
  
  (* Gt *)
  - apply Nat.compare_gt_iff in Heq.
    split; intros Hsyn; depelim Hsyn.
    depelim H1. constructor. auto.
    replace (nth i (Γ' @ (U :: Γ)) unit) with (nth (pred i) (Γ' @ Γ) unit).
    constructor. rewrite app_length in *. simpl in H1. omega.
    now apply nth_pred.

    replace (nth _ (Γ' @ (_ :: _)) unit) with (nth (pred i) (Γ' @ Γ) unit).
    constructor. rewrite app_length in *. simpl in H0. omega.
    now apply nth_pred.

  (* App *)
  - on_call (hereditary_subst (U,t1,u))
            ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    specialize (H0 _ _ _ [] eq_refl).
    rewrite Heq in Hind.
    revert H0.
    on_call hereditary_subst
            ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    intros.

    (* Redex *)
    assert((Γ' @ (U :: Γ) |-- @( t3, u) => T → Γ' @ Γ |-- t0 <= T ∧ b = T)).
    intros Ht; depelim Ht.
    destruct (Hind Γ (A ---> B) H1).
    specialize (H _ A H1).
    destruct (H4 Ht). noconf H6.
    depelim H5. split; auto. 
    
    destruct o; try destruct h; destruct H.
    destruct (H H2). subst x.
    specialize (H0 _ B0 H7).
    destruct o0 as [[ty typrf]|]; destruct H0 as [Hcheck Hinf].
    now apply Hcheck. now apply Hcheck.
    
    specialize (H0 _ B0 (H H2)).
    destruct o0 as [[ty typrf]|]; destruct H0 as [Hcheck Hinf].
    now apply Hcheck. now apply Hcheck.
    
    split; auto.
    depelim H5.
    
    split; eauto.
    intros Ht3u; apply H2.
    now depelim Ht3u.
  
  (* No redex *)
  - intros Γ T Hu.
    assert(Γ' @ (U :: Γ) |-- @( t3, u) => T
      → Γ' @ Γ |-- @( t2, fst (hereditary_subst (U, t1, u) (length Γ'))) => T).
    intros Ht; depelim Ht.
    on_call hereditary_subst
            ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    revert Heq.
    on_call hereditary_subst
            ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    intros.
    pose (Hind _ (A ---> B) Hu).
    destruct o0 as [[ty prf']|].
    + destruct y as [Hind' Hind''].
      specialize (Hind'' Ht). destruct Hind''; subst ty.
      specialize (H _ A Hu).
      destruct o as [[ty' prf'']|].
      ++ destruct H as [Hind0 Hind0'].
        specialize (Hind0 H0). destruct Hind0. subst ty'.
        eapply application_synth; eauto. simpl in *.
        depelim H1. simp is_lambda in Heq. noconf Heq.
        depelim H1.

      ++ depelim H1. simp is_lambda in Heq. noconf Heq. depelim H1. 
    + clear y. specialize (H _ A Hu).
      destruct (Hind _ (A ---> B) Hu).
      apply is_lambda_inr in Heq. subst t2. simpl.
      destruct o as [[ty prf]|]; destruct H as [Hindt0 Hindt0'].
      eapply application_synth; eauto.
      now apply Hindt0.
      eapply application_synth; eauto.

    + split; auto. intros H2.
      depelim H2.
      constructor; auto.
    
  (* Pair *)
  - simpl in Heq. autorewrite with is_pair in Heq. simpl in prf.
    intros Γ T Hu.
    assert( (Γ' @ (U :: Γ) |-- Fst t5 => T → Γ' @ Γ |-- u <= T ∧ a = T)).
    intros Ht; depelim Ht. specialize (Hind _ (A × B) Hu). revert Hind.
    on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    noconf Heq.
    intros [Hind Hind'].
    specialize (Hind' Ht). destruct Hind' as [H0 H1]. noconf H1.
    depelim H0. split; auto.
    depelim H.
    split; auto.
    intros H1. depelim H1. intuition.

  - intros Γ T Hu.
    assert (Γ' @ (U :: Γ) |-- Fst t5 => T → Γ' @ Γ |-- Fst t2 => T).
    intros Ht; depelim Ht.
    specialize (Hind _ (A × B) Hu). revert Hind.
    on_call hereditary_subst ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    destruct o as [[ty prf]|]. intros [Hind Hind'].
    destruct (Hind' Ht). subst ty.
    depelim H. simp is_pair in Heq. discriminate.
    depelim H.
    
    apply is_pair_inr in Heq. simpl in Heq ; subst t2.
    intros [Hind Hind']. eapply pair_elim_fst_synth. now apply Hind'.
    split; auto. intros H2. depelim H2. intuition auto with term.

  (* Snd *)
  - intros Γ T Hu.
    assert((Γ' @ (U :: Γ) |-- Snd t6 => T → Γ' @ Γ |-- v <= T ∧ b = T)).

    intros Ht; depelim Ht. specialize (Hind _ (A × B) Hu). revert Hind.
    on_call hereditary_subst
            ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *).
    noconf Heq.
    intros [Hind Hind'].
    specialize (Hind' Ht). destruct Hind' as [H0 H1]. noconf H1.
    depelim H0. split; auto. depelim H.
    split; auto.
    intros H1. depelim H1. intuition auto with term.

  - intros Γ T Hu.
    assert (Γ' @ (U :: Γ) |-- Snd t6 => T → Γ' @ Γ |-- Snd t2 => T).
    intros Ht; depelim Ht.
    specialize (Hind _ (A × B) Hu). revert Hind.
    on_call hereditary_subst
            ltac:(fun c => remember c as hsubst; destruct hsubst; simpl in *). 
    destruct o as [[ty prf]|]. intros [Hind Hind'].
    destruct (Hind' Ht). subst ty.
    depelim H. simp is_pair in Heq. discriminate.
    depelim H.

    intros [Hind Hind']. 
    apply is_pair_inr in Heq. subst t2. simpl in *.
    specialize (Hind' Ht). econstructor; eauto.
    
    split; auto. intros H1. depelim H1. term. 
Qed.

Print Assumptions hereditary_subst_subst.

Lemma check_liftn {Γ Γ' t T} : Γ |-- t <= T -> Γ' @ Γ |-- lift 0 (length Γ') t <= T.
Proof. intros. apply (check_lift Γ t T [] H Γ'). Qed.

Lemma synth_liftn {Γ Γ' t T} : Γ |-- t => T -> Γ' @ Γ |-- lift 0 (length Γ') t => T.
Proof. intros. apply (synthetize_lift Γ t T [] H Γ'). Qed.
Hint Resolve @check_liftn @synth_liftn : term.

(* Write normalization function *)
Lemma types_normalizes Γ t T : Γ |-- t : T → ∃ u, Γ |-- u <= T.
Proof. induction 1. (* eta-exp *)

  exists (η (nth i Γ unit) i).
  apply (eta_expand Γ i (nth i Γ unit) (neutral_var _)); term.

  destruct IHtypes as [t' tt'].
  exists λ t'; term.

  destruct IHtypes1 as [t' tt'].
  destruct IHtypes2 as [u' uu'].

  (* Hereditary substitution *)
  apply checks_arrow in tt'. destruct tt' as [t'' [t't'' t'B]]. subst.

  generalize (hereditary_subst_subst _ _ t'' [] Γ B uu').
  destruct_call hereditary_subst. destruct o. destruct h.
  simpl in *. intros. destruct H1. exists t0; intuition.
  simpl in *. intros. destruct H1. exists t0; intuition.

  (* Unit *)
  exists Tt; term.

  (* Pair *)
  destruct IHtypes1 as [t' tt'].
  destruct IHtypes2 as [u' uu'].
  exists << t' , u' >>. term.

  (* Fst *)
  destruct IHtypes as [t' tt'].
  depelim tt'. exists t0; term. 

  depelim H0.

  (* Snd *)
  destruct IHtypes as [t' tt'].
  depelim tt'. exists u; term. 

  depelim H0.
Qed.

Print Assumptions types_normalizes.
