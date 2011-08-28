Require Import Equations.
Require Import Omega.

Inductive term := 
| Var (n : nat)
| Lambda (t : term)
| App (t u : term)
| Pair (t u : term)
| Fst (t : term) | Snd (t : term)
| Tt.


Coercion Var : nat >-> term.

Delimit Scope term_scope with term.
Bind Scope term_scope with term.

Notation " @( f , x ) " := (App (f%term) (x%term)).
Notation " 'λ' t " := (Lambda (t%term)) (at level 0). 
Notation " << t , u >> " := (Pair (t%term) (u%term)).

Parameter atomic_type : Set.
Inductive type :=
| atom (a : atomic_type)
| product (a b : type)
| unit
| arrow (a b : type).

Derive Subterm for type.
(* Equations foo(t : type) (u : nat) (foo : t = t) : { u : type | t = t } := *)
(* foo t u foo with t := { *)
(*   | atom a := exist _ (atom a) _ ; *)
(*   | _ := exist _ unit _ }. *)

Coercion atom : atomic_type >-> type.
Notation " x × y " := (product x y) (at level 90).
Notation " x ---> y " := (arrow x y) (at level 30).

Require Import Arith.
Print comparison.
Ltac equations := idtac.

Equations(nocomp) lift (k n : nat) (t : term) : term :=
lift k n (Var i) with nat_compare i k := {
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

Ltac term := eauto with term.

Lemma lift0 k t : lift k 0 t = t.
Proof. funelim (lift k 0 t) ; try rewrite H ; try rewrite H0; auto. Qed.
Hint Rewrite lift0 : lift.
Require Import Omega.
Lemma lift_k_lift_k k n m t : lift k n (lift k m t) = lift k (n + m) t.
Proof. funelim (lift k m t) ; simp lift; try rewrite H ; try rewrite H0; auto.
  destruct (nat_compare_spec n0 k); try discriminate. subst.
  case_eq (nat_compare (k + n) k); intro H; simp lift; term. 
  rewrite <- nat_compare_lt in H; term.
  rewrite Heq; simp lift; term.

  rewrite Heq. rewrite <- nat_compare_gt in Heq. simp lift.
  destruct (nat_compare_spec (n0 + n) k); try discriminate; simp lift; term. 
Qed.
Hint Rewrite lift_k_lift_k : lift.

Equations(nocomp) subst (k : nat) (t : term) (u : term) : term :=
subst k (Var i) u with nat_compare i k := {
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
  rewrite <- nat_compare_lt in Heq; absurd omega.
  rewrite <- nat_compare_gt in Heq; absurd omega.
Qed.
Hint Rewrite substnn : subst.
Notation ctx := (list type).

Delimit Scope lf with lf.

Reserved Notation " Γ |-- t : A " (at level 70, t, A at next level).
Require Import List.

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

Notation " [ t ] u " := (subst 0 u t) (at level 10).

Notation " x @ y " := (app x y) (at level 30, right associativity).

Lemma nth_length {A} x t (l l' : list A) : nth (length l) (l @ (t :: l')) x = t.
Proof. induction l; simpl; auto. Qed.

Hint Constructors types : term.

Lemma nat_compare_elim (P : nat -> nat -> comparison -> Prop)
  (PEq : forall i, P i i Eq)
  (PLt : forall i j, i < j -> P i j Lt)
  (PGt : forall i j, i > j -> P i j Gt) :
  forall i j, P i j (nat_compare i j).
Proof. intros. case (nat_compare_spec i j); intros; subst; auto. Qed.

Lemma nth_extend_left {A} (a : A) n (l l' : list A) : nth n l a = nth (length l' + n) (l' @ l) a.
Proof. induction l'; auto. Qed.

Lemma nth_extend_middle {A} (a : A) n (l l' l'' : list A) : 
  match nat_compare n (length l') with
    | Lt => nth n (l' @ l) a = nth n (l' @ l'' @ l) a
    | _ => nth n (l' @ l) a = nth (n + length l'') (l' @ l'' @ l) a
  end.
Proof. 
  assert (foo:=nat_compare_spec n (length l')).
  depelim foo; try rewrite <- H; try rewrite <- H0; subst. rewrite <- nth_extend_left. 
  replace (length l'') with (length l'' + 0) by auto with arith. rewrite <- nth_extend_left. 
  replace (length l') with (length l' + 0) by auto with arith. now rewrite <- nth_extend_left.

  clear H0. revert l' H l''; induction n; intros; simpl; auto. destruct l'; now try solve [ inversion H ].
  destruct l'; try solve [ inversion H ]. simpl. rewrite <- (IHn l'); auto. simpl in H. omega.

  clear H0. revert l' H l''; induction n; intros; simpl; auto. inversion H.
  destruct l'; simpl. 
  replace (S (n + length l'')) with (length l'' + S n) by omega. now rewrite <- nth_extend_left.
  rewrite <- IHn; auto. simpl in H; omega.
Qed. 
  
Print Rewrite HintDb list.
Hint Rewrite <- app_assoc in_app_iff in_inv : list.


Lemma type_lift Γ t T Γ' : Γ' @ Γ |-- t : T -> forall Γ'', Γ' @ Γ'' @ Γ |-- lift (length Γ') (length Γ'') t : T.
Proof. intros H. depind H; intros; simp lift; eauto with term.

  generalize (nth_extend_middle unit i Γ Γ' Γ'').
  destruct nat_compare; intros H'; rewrite H'; simp lift; apply axiom; autorewrite with list in H |- *; omega.
  
  apply abstraction. change (S (length Γ')) with (length (A :: Γ')). 
  rewrite app_comm_cons. apply IHtypes. reflexivity.
Qed.

Lemma type_lift1 Γ t T A : Γ |-- t : T -> A :: Γ |-- lift 0 1 t : T.
Proof. intros. apply (type_lift Γ t T [] H [A]). Qed.

Lemma app_cons_snoc_app {A} l (a : A) l' : l ++ (a :: l') = (l ++ a :: nil) ++ l'.
Proof. induction l; simpl; auto. now rewrite IHl. Qed.

Hint Extern 5 => progress (simpl ; autorewrite with list) : term.
Ltac term ::= simp lift subst; eauto with term.

Lemma substitutive Γ t T Γ' u U : (Γ' @ (U :: Γ)) |-- t : T -> Γ |-- u : U -> Γ' @ Γ |-- subst (length Γ') t u : T.
Proof with term.
  intros H. depind H; term. intros.
  
  (* Var *)
  assert (spec:=nat_compare_spec i (length Γ')). depelim spec; try rewrite <- H1; try rewrite <- H2 ; simp subst.

  (* Eq *)
  generalize (type_lift Γ u U [] H0 Γ'); simpl; intros. 
  rewrite app_cons_snoc_app, app_nth1, app_nth2; try (simpl; omega).
  now rewrite <- minus_n_n. autorewrite with list; simpl. omega.

  (* Lt *)
  rewrite app_nth1; try omega. rewrite <- (app_nth1 _ Γ); term. 

  (* Gt *)
  rewrite app_nth2; term. 
  change (U :: Γ) with ((cons U nil) @ Γ). rewrite app_nth2; term.
  simpl. rewrite (nth_extend_left unit _ Γ Γ').
  replace (length Γ' + (i - length Γ' - 1)) with (pred i); term.
  apply axiom. autorewrite with list in H |- *. simpl in H. omega.

  (* Abstraction *)
  intros. apply abstraction. now apply (IHtypes Γ (A :: Γ') U).
Qed.

Lemma subst1 Γ t T u U : U :: Γ |-- t : T -> Γ |-- u : U -> Γ |-- subst 0 t u : T.
Proof. intros; now apply (substitutive Γ t T [] u U). Qed.
  
Reserved Notation " t --> u " (at level 55, right associativity).

Inductive reduce : term -> term -> Prop :=
| red_beta t u : @((Lambda t) , u) --> subst 0 t u
| red_fst t u : Fst << t , u >> --> t
| red_snd t u : Snd << t , u >> --> u

where " t --> u " := (reduce t u). 

Require Import Relations.

Definition reduces := clos_refl_trans term reduce.
Notation " t -->* u " := (reduces t u) (at level 55).

Require Import Setoid.

Instance: Transitive reduces.
Proof. red; intros. econstructor 3; eauto. Qed.

Instance: Reflexive reduces.
Proof. red; intros. econstructor 2; eauto. Qed.

Derive NoConfusion for term type.

(* Remark *)
Instance: Irreflexive reduce.
Proof. intros x H. depind H.
  induction t; simp subst in H; try discriminate.
  destruct (nat_compare_spec n 0). subst.
  simp subst lift in H.  admit.
  absurd omega. simp subst in H. destruct n; discriminate.
  noconf H. admit.
  admit. admit.
Qed.

Lemma preserves_red1 Γ t τ : Γ |-- t : τ → forall u, t --> u → Γ |-- u : τ.
Proof. induction 1; intros; term. inversion H0. inversion H0. inversion H1. subst.
  apply subst1 with A. now inversion H. apply H0.

  inversion H.
  inversion H1.

  inversion H0. subst.  inversion H. subst. assumption.
  inversion H0. subst.  inversion H. subst. assumption.
Qed.

Lemma subject_reduction Γ t τ : Γ |-- t : τ → forall u, t -->* u → Γ |-- u : τ.
Proof. induction 2; eauto using preserves_red1. Qed.

Inductive value : term -> Prop :=
| val_unit : value Tt
| val_pair a b : value a -> value b -> value << a, b >>
| val_lambda t : value λ t.

Hint Constructors value : term.

(* Lemma inv_abs A B t : nil |-- t : A ---> B -> ∃ u, (t = λ u /\ (A :: nil) |-- u : B). *)
(* Proof. intros H; depind H. inversion H. exists t; auto. *)

(*   destruct IHtypes1 as [t' [tt' Htt']]. *)
(*   subst t.  *)
  
(*   induction  *)

(* Lemma red_progress  t τ : nil |-- t : τ → *)
(*   exists u, t -->* u ∧ value u. *)
(* Proof. intros H. depind H; term.  *)

(*   inversion H. *)

(*   exists λ t; term. split; now term. *)
(*   destruct IHtypes1 as [t' [tt' vt']]. *)
(*   destruct IHtypes2 as [u' [uu' vu']]. *)
(*   inversion H. *)

Reserved Notation " Γ |-- t => A " (at level 70, t, A at next level).
Reserved Notation " Γ |-- t <= A " (at level 70, t, A at next level).

Inductive atomic : type -> Prop :=
| atomic_atom a : atomic (atom a).
Hint Constructors atomic : term.

Equations(nocomp) atomic_dec (t : type) : { atomic t } + { ~ atomic t } :=
atomic_dec (atom a) := left (atomic_atom a) ;
atomic_dec _ := right _.

  Solve Obligations using intros; intro H; inversion H. 
  Solve All Obligations.

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
Proof. intros. destruct H. apply abstraction. auto.
  apply pair_intro. auto. auto.
  apply unit_intro.
  apply synthetizes_types. apply H0.

  intros. destruct H. now apply axiom.
  apply application with A; auto.
  apply pair_elim_fst with B; auto.
  apply pair_elim_snd with A; auto.
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

Hint Constructors normal neutral : term.

Lemma check_lift Γ t T Γ' : Γ' @ Γ |-- t <= T -> 
  forall Γ'', Γ' @ Γ'' @ Γ |-- lift (length Γ') (length Γ'') t <= T
with synthetize_lift Γ t T Γ' : Γ' @ Γ |-- t => T -> 
  forall Γ'', Γ' @ Γ'' @ Γ |-- lift (length Γ') (length Γ'') t => T.
Proof. intros H. depelim H; intros; simp lift.

  constructor.
  change (S (length Γ')) with (length (A :: Γ')). rewrite app_comm_cons. now apply check_lift. 

  constructor; apply check_lift; assumption.
  constructor. constructor. auto. now apply synthetize_lift.

  intros H. depelim H; intros; simp lift; try (constructor; eauto with term).
  generalize (nth_extend_middle unit i Γ Γ' Γ'').
  destruct nat_compare; intros H'; rewrite H'; simp lift; apply axiom_synth; autorewrite with list in H |- *; omega.

  econstructor. apply synthetize_lift. apply H. apply check_lift. apply H0.
  econstructor. apply synthetize_lift. apply H.
  econstructor. apply synthetize_lift. apply H.
Admitted.

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

(* Lemma η_normal : forall Γ A t, neutral t -> Γ |-- t => A -> normal (η A t). *)
(* Proof. induction 2; term. induction i; term. Qed. *)

Lemma checks_arrow Γ t A B : Γ |-- t <= A ---> B → ∃ t', t = λ t' ∧ A :: Γ |-- t' <= B.
Proof. intros H; inversion H; subst.
  exists t0; term.
  inversion H0.
Qed.

Lemma normal_lift {t k n} : normal t → normal (lift k n t) 
  with neutral_lift {t k n} : neutral t -> neutral (lift k n t).
Proof. destruct 1; simp lift; constructor; term. 
  destruct 1; simp lift; try (constructor; term). 
  destruct nat_compare; term. 
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

Ltac rec ::= rec_wf_eqns.
Require Import Arith Wf_nat.
Instance wf_nat : WellFounded lt := lt_wf.

Derive Subterm for term.

Ltac solve_rec ::= idtac.

Require Import Lexicographic_Product.

Implicit Arguments lexprod [A B].

Definition lexicographic {A B} (R : relation A) (S : relation B) : relation (A * B) :=
  fun x y => 
    let (x1, x2) := x in 
    let (y1, y2) := y in
      lexprod R (const S) (existS _ x1 x2) (existS _ y1 y2).

Instance lexicographic_wellfounded {A R B S} `{WellFounded A R} `{WellFounded B S} : WellFounded (lexicographic R S).
Proof. red in H, H0. red. unfold lexicographic. 
  assert(wfS:forall x : A, well_founded (const S x)) by auto.
  assert(wfprod:=wf_lexprod A (fun _ => B) R (const S) H wfS).
  red in wfprod.
  intro. specialize (wfprod (existT (const B) (fst a) (snd a))).
  clear wfS H H0. depind wfprod. constructor; intros.
  destruct y; destruct a; simpl in *. apply H0 with (existT (const B) a0 b).
  assumption.
  simpl. reflexivity.
Qed.

Definition her_order : relation (type * term * term) :=
  lexicographic (lexicographic type_subterm term_subterm) term_subterm.

(* Instance: WellFounded her_order. *)
(* Proof. unfold her_order. intro.  *)
(*   induction (lexicographic_wellfounded (A:=type*term) (R:=lexicographic type_subterm term_subterm) (B:=term) a). *)
(*   constructor. intros. *)
(*   apply H0. destruct y. destruct p; auto. destruct x. destruct p. auto. *)
  

Obligation Tactic := idtac.
Set Printing All.

Equations hereditary_subst (t : type * term * term) (k : nat) : 
  term * option { u : type | u = (fst (fst t)) \/ type_subterm u (fst (fst t)) }  :=
hereditary_subst t k by rec t her_order :=

hereditary_subst (pair (pair A a) t) k with t := {
  | Var i with nat_compare i k := {
    | Eq := (lift 0 k a, Some (exist _ A _)) ;
    | Lt := (Var i, None) ;
    | Gt := (Var (pred i), None) } ;

  | Lambda t := (Lambda (fst (hereditary_subst (A, a, t) (S k))), None) ;

  | App f arg with hereditary_subst (A, a, f) k := {
    | pair (Lambda f) (Some (exist (arrow A' B') prf)) := 
      let (arg', _) := hereditary_subst (A, a, arg) k in
      let (f', y) := hereditary_subst (A', arg', f) 0 in
        (f', Some (exist _ B' _)) ;
    | pair f' _ := (@(f', fst (hereditary_subst (A, a, arg) k)), None) } ;

  | Pair i j :=
    (<< fst (hereditary_subst (A, a, i) k), fst (hereditary_subst (A, a, j) k) >>, None) ;

  | Fst t with hereditary_subst (A, a, t) k := {
(* FIXME: Warn of unused clauses !     | pair (Pair i j) (Some (product A' B')) := (i, Some (exist _ A' _)) ; *)
    | pair (Pair i j) (Some (exist (product A' B') prf)) := (i, Some (exist _ A' _)) ;
    | pair p _ := (Fst p, None) } ;

  | Snd t with hereditary_subst (A, a, t) k := {
    | pair (Pair i j) (Some (exist (product A' B') prf)) := (j, Some (exist _ B' _)) ;
    | pair p _ := (Snd p, None) } ;

  | _ := (Tt, None) }.

Unset Printing All.

Next Obligation. intros. simpl. auto. Defined. 
Solve Obligations using intros; apply hereditary_subst; constructor 2; constructor.


Next Obligation. intros. apply hereditary_subst.  
  destruct prf. simpl in *. subst. repeat constructor.
  simpl in H0. do 2 constructor 1. apply type_direct_subterm_0_0 with (A' ---> B'); eauto using type_direct_subterm.
Defined.

Next Obligation. simpl; intros. 
  destruct prf. subst. right. constructor. 
  right. apply type_direct_subterm_0_0 with (A' ---> B'); eauto using type_direct_subterm.
Defined.

(* Next Obligation. intros. apply hereditary_subst.   *)
(*   destruct prf. simpl in H. subst. repeat constructor. *)
(*   simpl in H. do 2 constructor 1. apply type_direct_subterm_0_0 with (A' ---> B'); eauto using type_direct_subterm. *)
(* Defined. *)

Next Obligation. simpl; intros. 
  destruct prf. subst. right. constructor. 
  right. apply type_direct_subterm_0_0 with (A' × B'); eauto using type_direct_subterm.
Defined.

Next Obligation. simpl; intros. 
  destruct prf. subst. right. constructor. 
  right. apply type_direct_subterm_0_0 with (A' × B'); eauto using type_direct_subterm.
Defined.

Next Obligation. simpl; intros. admit. Defined. 
Next Obligation. intros. admit. Defined.

Lemma solution_left_dep : ∀ {A} (t : A) {B : forall (x : A), (x = t -> Type)}, B t eq_refl -> (∀ x (Heq : x = t), B x Heq).
Proof. intros; subst. apply X. Defined.

Ltac simplify_one_dep_elim ::=
  match goal with
    | [ |- context [eq_rect_r _ _ eq_refl]] => unfold eq_rect_r at 1; simpl

    | [ |- forall H : ?x = ?y, _ ] => (* variables case *)
      (let hyp := fresh H in intros hyp ;
        move hyp before x ; move x before hyp; revert_blocking_until x; revert x;
          (match goal with
             | |- let x := _ in _ = _ -> @?B x =>
               refine (@solution_left_let _ B _ _ _)
             | |- _ => refine (@solution_left_dep _ _ _ _)
           end))

    | [ |- ?gl ] => simplify_one_dep_elim_term gl
  end.


Lemma hereditary_subst_type Γ Γ' t T u U : Γ |-- u <= U -> Γ' @ (U :: Γ) |-- t : T ->
  forall t' T' prf, hereditary_subst (U, u, t) (length Γ') = (t', Some (exist _ T' prf)) -> T' = T.
Proof. intros. revert H1. funelim (hereditary_subst (U, u, t) (length Γ')); 
    simpl_dep_elim; subst; try (intro; discriminate).
  
  apply nat_compare_eq in Heq. subst.
  depelim H2. now rewrite nth_length.

  destruct hereditary_subst. destruct (hereditary_subst (a, t, t3) 0).
  noconf H3. depelim H2.
  specialize (Hind Γ (A ---> B) H1 H2_ _ _ _ H0). noconf Hind.

  destruct hereditary_subst. simpl in *. noconf H1.
  depelim H3. specialize (Hind Γ (A × B) H2 H3). noconf Hind. 

  destruct hereditary_subst. simpl in *. noconf H1. depelim H3.
  specialize (Hind Γ (A × B) H2 H3). noconf Hind.
Qed.

About check_synthetize.

Instance: subrelation eq (flip impl).
Proof. reduce. subst; auto. Qed.
Ltac simp_hsubst := try (rewrite_strat (bottomup (hints hereditary_subst))); rewrite <- ?hereditary_subst_equation_1.



Lemma hereditary_subst_subst U u t Γ' :
  (forall Γ T, Γ' @ (U :: Γ) |-- t <= T -> Γ |-- u <= U -> 
    Γ' @ Γ |-- fst (hereditary_subst (U, u, t) (length Γ')) <= T) ∧
  (forall Γ T, Γ' @ (U :: Γ) |-- t => T -> Γ |-- u <= U ->
      match hereditary_subst (U, u, t) (length Γ') with
        | (t', Some a) => Γ' @ Γ |-- t' <= T
        | (t', None) => Γ' @ Γ |-- t' => T
      end).
Proof. 
  funelim (hereditary_subst (U, u, t) (length Γ')); simp_hsubst; simpl; term.

  depelim H0. 
    constructor. specialize (H (A :: Γ')). simplify_IH_hyps. destruct H. eauto.
    term.

  destruct H, H0.
  depelim H1; term. 

  (* Unit *)
  simpl. depelim H; term.
  
  (* Var *)
  (* Eq *)
  clear H0. 
  apply nat_compare_eq in Heq. subst.
  apply check_lift_ctx. depelim H1. depelim H1. now rewrite nth_length. 

  clear H0. 
  apply nat_compare_eq in Heq. subst.
  apply check_lift_ctx. depelim H1. now rewrite nth_length. 



  (* L
  clear H0. 
  apply nat_compare_eq in Heq. subst.
  apply check_lift_ctx. depelim H1. depelim H1. now rewrite nth_length. 

  term.


  
  specialize (H _ _ H1_ H2). 
  depelim H1. simp hereditary_subst. rewrite <- hereditary_subst_equation_1.

apply check_synthetize; simplify_dep_elim; simplify_IH_hyps;
  (rewrite_strat (bottomup (hints hereditary_subst))); 
  simpl; rewrite <- ?hereditary_subst_equation_1; 
    try constructor; simpl in *; term.



Lemma hereditary_subst_subst : (forall Δ t T, Δ |-- t <= T -> 
  forall Γ Γ' u U, Δ = Γ' @ (U :: Γ) -> Γ |-- u <= U -> 
    Γ' @ Γ |-- fst (hereditary_subst (U, u, t) (length Γ')) <= T) ∧
  (forall Δ t T, Δ |-- t => T -> 
    forall Γ Γ' u U, Γ |-- u <= U -> Δ = Γ' @ (U :: Γ) ->
      match hereditary_subst (U, u, t) (length Γ') with
        | (t', Some a) => Γ' @ Γ |-- t' <= T
        | (t', None) => Γ' @ Γ |-- t' => T
      end).
Proof. apply check_synthetize; simplify_dep_elim; simplify_IH_hyps;
  (rewrite_strat (bottomup (hints hereditary_subst))); 
  simpl; rewrite <- ?hereditary_subst_equation_1; 
    try constructor; simpl in *; term.

  (* Var *)
  change (A::Γ'@Γ) with ((A :: Γ') @ Γ). 
  apply (H Γ (A :: Γ')); auto.

  specialize (H _ H0). destruct hereditary_subst. destruct o; simpl; term.
  depelim H; now try solve [ depelim a ].



(*   (* subst_subst' *) *)
(*   intros. *)
(*   depelim H0; simp hereditary_subst; try solve [ constructor; term ]; try rewrite <- !hereditary_subst_equation_1. *)

  (* Var *)
  assert (spec:=nat_compare_spec i (length Γ')). depelim spec; try rewrite <- H0; try rewrite <- H1; simp hereditary_subst; simpl.

  (* Eq *)
  generalize (check_lift Γ u U [] H Γ'); simpl; intros. 
  rewrite app_cons_snoc_app, app_nth1, app_nth2; try (simpl; omega).
  now rewrite <- minus_n_n. autorewrite with list; simpl. omega.

  (* Lt *)
  rewrite app_nth1; try omega. rewrite <- (app_nth1 _ Γ); term.

  (* Gt *)
  rewrite app_nth2; term. 
  change (U :: Γ) with ((cons U nil) @ Γ). rewrite app_nth2; term.
  simpl. rewrite (nth_extend_left unit _ Γ Γ').
  replace (length Γ' + (i - length Γ' - 1)) with (pred i); term.
  intros.
  apply axiom_synth. autorewrite with list in l |- *. simpl in l. omega.

  (* Lambda *)
  assert (Hu0:=H _ H1).
  assert (Ht:=H0 _ H1).
  case_eq (hereditary_subst (U, u, t) (length Γ')). 
  intros t'' o Heq; rewrite Heq in *.
 
  destruct o.
  (* Some redex was found *)
  apply checks_arrow in Hu0.
  destruct Hu0 as [t' [eqt' Ht']].
  subst. simpl.
  destruct s0. simpl in *.
  eapply hereditary_subst_type with (T:=A ---> B) in Heq; term.
  subst. simpl. 

  case_eq (hereditary_subst (U, u, u0) (length Γ')). intros. 
  case_eq (hereditary_subst (A, t0, t') 0). intros.

  simpl in *.
  assert (Ht0:=H0 _ H1).
  rewrite H2 in Ht0. simpl in Ht0.
  change (A :: Γ' @ Γ) with ((A :: Γ') @ Γ) in Ht'.
  assert (Ht1:=H (Γ' @ Γ) [] _ _ _ _ Ht0 Ht'). 
  simpl in Ht1. rewrite H3 in Ht1. apply Ht1.

  (* No redex found *)
  simpl. destruct t0; simpl; econstructor; eauto.

  (* Fst *)
  generalize (H' _ _ _ _ _ _ H H0).
  case_eq (hereditary_subst (U, u, t) (length Γ')).
  intros t0 o Heq.

  destruct t0; destruct o; simpl; intros; term. 

  depelim H1. depelim H1. 

  depelim H1. depelim H1.

  depelim H1. depelim H1.

  depelim H1. 
  destruct s. simpl in *.
  eapply hereditary_subst_type with (T:=A × B) in Heq; term. 
  destruct x; simpl; try discriminate.
  assumption.

  repeat depelim H1. 
  repeat depelim H1. 
  repeat depelim H1.
  repeat depelim H1.

  (* Snd *)
  generalize (H' _ _ _ _ _ _ H H0).
  case_eq (hereditary_subst (U, u, t) (length Γ')).
  intros t0 o Heq.

  destruct t0; destruct o; simpl; intros; term. 

  repeat depelim H1. 
  repeat depelim H1. 
  repeat depelim H1. 

  depelim H1. 
  destruct s. simpl in *.
  eapply hereditary_subst_type with (T:=A × B) in Heq; term. 
  destruct x; simpl; try discriminate.
  assumption.

  repeat depelim H1. 
  repeat depelim H1. 
  repeat depelim H1.
  repeat depelim H1.




eapply H.
constructor. rewrite <- !hereditary_subst_equation_1.

Lemma hereditary_subst_subst Γ Γ' t T u U : Γ |-- u <= U -> Γ' @ (U :: Γ) |-- t <= T ->
  Γ' @ Γ |-- fst (hereditary_subst (U, u, t) (length Γ')) <= T 

with hereditary_subst_subst' Γ Γ' t T u U : Γ |-- u <= U -> Γ' @ (U :: Γ) |-- t => T ->
  match hereditary_subst (U, u, t) (length Γ') with
    | (t', Some a) => Γ' @ Γ |-- t' <= T
    | (t', None) => Γ' @ Γ |-- t' => T
  end.
Proof. intros. 
  depelim H0; simp hereditary_subst; constructor; term; rewrite <- !hereditary_subst_equation_1.

  change (A::Γ'@Γ) with ((A :: Γ') @ Γ). 
  apply (hereditary_subst_subst Γ (A :: Γ')); auto.

  apply (hereditary_subst_subst Γ Γ'); auto.

  apply (hereditary_subst_subst Γ Γ'); auto.

  specialize (hereditary_subst_subst' Γ Γ' _ _ _ _ H H1). destruct hereditary_subst. destruct o.
  simpl. depelim hereditary_subst_subst'; try solve [ depelim H0 ]. apply H0.
  simpl. apply hereditary_subst_subst'.

  (* subst_subst' *)
  intros.
  depelim H0; simp hereditary_subst; try solve [ constructor; term ]; try rewrite <- !hereditary_subst_equation_1.

  (* Var *)
  assert (spec:=nat_compare_spec i (length Γ')). depelim spec; try rewrite <- H1; try rewrite <- H2; simp subst; simpl.

  (* Eq *)
  generalize (check_lift Γ u U [] H Γ'); simpl; intros. 
  rewrite app_cons_snoc_app, app_nth1, app_nth2; try (simpl; omega).
  now rewrite <- minus_n_n. autorewrite with list; simpl. omega.

  (* Lt *)
  simpl.
  rewrite app_nth1; try omega. rewrite <- (app_nth1 _ Γ); term.

  (* Gt *)
  simpl.
  rewrite app_nth2; term. 
  change (U :: Γ) with ((cons U nil) @ Γ). rewrite app_nth2; term.
  simpl. rewrite (nth_extend_left unit _ Γ Γ').
  replace (length Γ' + (i - length Γ' - 1)) with (pred i); term.
  intros.
  apply axiom_synth. autorewrite with list in H0 |- *. simpl in H0. omega.

  (* Lambda *)
  assert (Hu0:=hereditary_subst_subst Γ Γ' _ _ _ _ H H1).
  assert (Ht:=hereditary_subst_subst' Γ Γ' _ _ _ _ H H0).
  case_eq (hereditary_subst (U, u, t) (length Γ')). intros. rewrite H2 in *.
 
  destruct o.
  (* Some redex was found *)
  apply checks_arrow in Ht.
  destruct Ht as [t' [eqt' Ht']].
  subst. simpl.
  destruct s. simpl in *.
  eapply hereditary_subst_type with (T:=A ---> B) in H2; term.
  subst. simpl. 

  case_eq (hereditary_subst (U, u, u0) (length Γ')). intros. 
  case_eq (hereditary_subst (A, t0, t') 0). intros.
  
  assert (Ht0:=hereditary_subst_subst _ _ _ _ _ _ H H1).
  rewrite H2 in Ht0. simpl in Ht0.
  change (A :: Γ' @ Γ) with ((A :: Γ') @ Γ) in Ht'.
  assert (Ht1:=hereditary_subst_subst (Γ' @ Γ) [] _ _ _ _ Ht0 Ht'). 
  simpl in Ht1. rewrite H3 in Ht1. apply Ht1.

  (* No redex found *)
  simpl. destruct t0; simpl; econstructor; eauto.

  (* Fst *)
  generalize (hereditary_subst_subst' _ _ _ _ _ _ H H0).
  case_eq (hereditary_subst (U, u, t) (length Γ')).
  intros t0 o Heq.

  destruct t0; destruct o; simpl; intros; term. 

  depelim H1. depelim H1. 

  depelim H1. depelim H1.

  depelim H1. depelim H1.

  depelim H1. 
  destruct s. simpl in *.
  eapply hereditary_subst_type with (T:=A × B) in Heq; term. 
  destruct x; simpl; try discriminate.
  assumption.

  repeat depelim H1. 
  repeat depelim H1. 
  repeat depelim H1.
  repeat depelim H1.

  (* Snd *)
  generalize (hereditary_subst_subst' _ _ _ _ _ _ H H0).
  case_eq (hereditary_subst (U, u, t) (length Γ')).
  intros t0 o Heq.

  destruct t0; destruct o; simpl; intros; term. 

  repeat depelim H1. 
  repeat depelim H1. 
  repeat depelim H1. 

  depelim H1. 
  destruct s. simpl in *.
  eapply hereditary_subst_type with (T:=A × B) in Heq; term. 
  destruct x; simpl; try discriminate.
  assumption.

  repeat depelim H1. 
  repeat depelim H1. 
  repeat depelim H1.
  repeat depelim H1.
Qed.


  (* Lambda *)
  Lemma check_lambda Γ t T : Γ |-- λ(t) <= T -> 
    exists A, exists B, A :: Γ |-- t <= B /\ T = A ---> B.
  Proof. intros H; depelim H. exists A B; intuition. depelim H0. Qed.
  apply check_lambda in H1.
  destruct H1 as [A [B [Ht2 Ht]]]. subst.
  constructor. change (A :: Γ' @ Γ) with ((A :: Γ') @ Γ). apply H; trivial.

  (* Pair *)
  depelim H2. term. depelim H3.

  (* Unit *)
  depelim H0; term. depelim H1.

  (* Var *)


Lemma check_liftn {Γ Γ' t T} : Γ |-- t <= T -> Γ' @ Γ |-- lift 0 (length Γ') t <= T.
Proof. intros. apply (check_lift Γ t T [] H Γ'). Qed.

Lemma synth_liftn {Γ Γ' t T} : Γ |-- t => T -> Γ' @ Γ |-- lift 0 (length Γ') t => T.
Proof. intros. apply (synthetize_lift Γ t T [] H Γ'). Qed.
Hint Resolve @check_liftn @synth_liftn : term.

  (* Eq: Substitution *)
  apply nat_compare_eq in Heq. subst.
  depelim H0. depelim H1. apply check_liftn. now rewrite nth_length.

  (* Lt *)
  depelim H0. depelim H1.
  generalize (nth_extend_middle unit n Γ Γ' [U]). rewrite Heq. intros.
  apply nat_compare_lt in Heq. rewrite app_nth1; try omega. 
  rewrite <- (app_nth1 _ Γ); term. constructor; term. 
  rewrite H2. apply H0.

  (* Gt *)
  generalize (nth_extend_middle unit n Γ Γ' [U]). rewrite Heq. intros.
  apply nat_compare_gt in Heq.
  depelim H0. depelim H1. constructor; term.
  rewrite app_nth2; term. 
  change (U :: Γ) with ((cons U nil) @ Γ). rewrite app_nth2; term.
  simpl. rewrite (nth_extend_left unit _ Γ Γ').
  replace (length Γ' + (n - length Γ' - 1)) with (pred n); term.
  apply axiom_synth. autorewrite with list in H1 |- *. simpl in H1. omega.


  (* App (Var, ...) *)
  depelim H2. depelim H3. rewrite H0 in Hind. simpl in Hind.
  constructor; term. econstructor; eauto. 

Focus 2. 
  depelim H2. depelim H3. rewrite H0 in Hind. simpl in Hind.
  constructor; term. econstructor. 
  specialize (Hind _ (A ---> B) H1).


constructor.

  
  

  
  
Admitted.  

(*
  Proof. intros. 
    rec_wf_rel t IH her_order.
    destruct x as [[U u] t].
    simp hereditary_subst. constructor. 
    destruct t. 

    simp hereditary_subst.
    constructor;
    destruct nat_compare; autorewrite with hereditary_subst;
    constructor.

    simp hereditary_subst.
    rewrite <- hereditary_subst_equation_1. 
    constructor.

    apply IH. constructor 2; constructor.

    constructor. apply IH. constructor 2; constructor.

    simp hereditary_subst. rewrite <- hereditary_subst_equation_1.
    destruct hereditary_subst.

    destruct t; try solve [ constructor; apply IH; constructor 2; constructor ].
    destruct o. destruct s. 
    
    destruct x. constructor. apply IH. constructor 2; constructor.
    constructor. apply IH. constructor 2; constructor.
    constructor. apply IH. constructor 2; constructor.
    constructor. apply IH. do 2 constructor 1. 
    destruct o; simpl in H. subst. constructor.
    apply type_direct_subterm_0_0 with (x1 ---> x2); eauto using type_direct_subterm.

    constructor. apply IH. constructor 2; constructor.

    constructor. apply IH. constructor 2; constructor.
    apply IH. constructor 2; constructor.

    (* Fst *)
    constructor. apply IH. constructor 2; constructor.
    destruct hereditary_subst.

    destruct t0; try solve [ constructor; apply IH; constructor 2; constructor ].
    destruct o. destruct s. 
    
    destruct x; try solve [ constructor ]. 
    constructor.

    (* Snd *)
    constructor. apply IH. constructor 2; constructor.
    destruct hereditary_subst.

    destruct t0; try solve [ constructor; apply IH; constructor 2; constructor ].
    destruct o. destruct s. 
    
    destruct x; try solve [ constructor ]. 
    constructor.

    (* Tt *)
    constructor.
  Defined. *)

(* Equations hereditary_subst (k : nat) (t : term) (u : term) (U : type) : term * option type := *)
(* hereditary_subst k t u U by rec t := *)

(* hereditary_subst k (Var i) u U with nat_compare i k := { *)
(*   | Eq := (lift 0 k u, Some U) ; *)
(*   | Lt := (Var i, None) ; *)
(*   | Gt := (Var (pred i), None) } ; *)

(* hereditary_subst k (Lambda t) u U := (Lambda (fst (hereditary_subst (S k) t u U)), None) ; *)

(* hereditary_subst k (App a x) u U with hereditary_subst k a u U := { *)
(*   | pair (Lambda t) (Some (arrow A B)) := hereditary_subst k t x A ;  *)
(*   | pair f _ := (@(f, fst (hereditary_subst k x u U)), None) } ; *)

(* hereditary_subst k (Pair a b) u U :=  *)
(*   (<< fst (hereditary_subst k a u U), fst (hereditary_subst k b u U) >>, None) ; *)

(* hereditary_subst k (Fst t) u U with hereditary_subst k t u U := { *)
(*   | pair (Pair a b) (Some (product A B)) := (a, Some A) ; *)
(*   | pair p _ := (Fst p, None) } ; *)

(* hereditary_subst k (Snd t) u U with hereditary_subst k t u U := { *)
(*   | pair (Pair a b) (Some (product A B)) := (b, Some B) ; *)
(*   | pair p _ := (Snd p, None) } ; *)

(* hereditary_subst k Tt _ _ := (Tt, None). *)

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

  admit.

  (* Unit *)
  exists Tt; term.

  (* Pair *)
  destruct IHtypes1 as [t' tt'].
  destruct IHtypes2 as [u' uu'].
  exists << t' , u' >>. term.

  (* Fst *)
  destruct IHtypes as [t' tt'].
  depelim tt'. exists t0; term. 

  pose (synth_neutral H1). exists (η A (Fst t0)). apply eta_expand; term.

  (* Snd *)
  destruct IHtypes as [t' tt'].
  depelim tt'. exists u; term. 

  pose (synth_neutral H1). exists (η B (Snd t0)). apply eta_expand; term.
Qed.
