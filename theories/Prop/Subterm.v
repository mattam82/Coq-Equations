(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2020 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

From Coq Require Import Wf_nat Relations.
From Coq Require Import Wellfounded Relation_Definitions.
From Coq Require Import Relation_Operators Lexicographic_Product Wf_nat.
From Coq Require Export Program.Wf FunctionalExtensionality.

From Equations Require Import Init Signature.
Require Import Equations.CoreTactics.
Require Import Equations.Prop.Classes Equations.Prop.EqDec
        Equations.Prop.DepElim Equations.Prop.Constants.

Generalizable Variables A R S B.

Scheme Acc_dep := Induction for Acc Sort Prop.

(** The fixpoint combinator associated to a well-founded relation,
   just reusing the [Wf.Fix] combinator. *)

Definition FixWf `{WF:WellFounded A R} (P : A -> Type)
  (step : forall x : A, (forall y : A, R y x -> P y) -> P x) : forall x : A, P x :=
  Fix wellfounded P step.

Definition step_fn_ext {A} {R} (P : A -> Type) :=
  fun step : forall x : A, (forall y : A, R y x -> P y) -> P x =>
    forall x (f g : forall y (H : R y x), P y),
      (forall y H, f y H = g y H) ->
      step x f = step x g.

Lemma FixWf_unfold `{WF : WellFounded A R} (P : A -> Type)
      (step : forall x : A, (forall y : A, R y x -> P y) -> P x)
      (step_ext : step_fn_ext P step) (x : A) :
  FixWf P step x = step x (fun y _ => FixWf P step y).
Proof.
  intros.
  unfold FixWf.
  rewrite Init.Wf.Fix_eq. apply step_ext. intros. reflexivity.
  intros x' f g H. apply step_ext. apply H.
Qed.

Lemma FixWf_unfold_step :
  forall (A : Type) (R : relation A) (WF : WellFounded R) (P : A -> Type)
    (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A)
    (step_ext : step_fn_ext P step)
    (step' : forall y : A, R y x -> P y),
    step' = (fun (y : A) (_ : R y x) => FixWf P step y) ->
    FixWf P step x = step x step'.
Proof. intros. rewrite FixWf_unfold, H. reflexivity. apply step_ext. Qed.

Ltac unfold_FixWf :=
  match goal with
    |- context [ @FixWf ?A ?R ?WF ?P ?f ?x ] =>
    let step := fresh in
    set(step := fun y (_ : R y x) => @FixWf A R WF P f y) in *;
     unshelve erewrite (@FixWf_unfold_step A R WF P f x _ step);
     [red; intros; simp_sigmas; red_one_eq (* Extensionality proof *)
     |hidebody step; red_eq_lhs (* Unfold the functional *)
     |reflexivity]
  end.

Ltac unfold_recursor := unfold_FixWf.

Lemma Acc_pi (A : Type) (R : relation A) i (x y : Acc R i) : x = y.
Proof.
  revert y.
  induction x using Acc_dep.
  intros. destruct y.
  f_equal.
  extensionality y. extensionality H'. apply H.
Qed.

Lemma FixWf_unfold_ext `{WF : WellFounded A R} (P : A -> Type)
  (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) :
  FixWf P step x = step x (fun y _ => FixWf P step y).
Proof.
  intros. unfold FixWf, Fix. destruct wellfounded.
  simpl. f_equal. extensionality y. extensionality h.
  f_equal. apply Acc_pi.
Qed.

#[global]
Hint Rewrite @FixWf_unfold_ext : Recursors.

Lemma FixWf_unfold_ext_step :
  forall (A : Type) (R : relation A) (WF : WellFounded R) (P : A -> Type)
    (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A)
    (step' : forall y : A, R y x -> P y),
    step' = (fun (y : A) (_ : R y x) => FixWf P step y) ->
    FixWf P step x = step x step'.
Proof. intros. rewrite FixWf_unfold_ext, H. reflexivity. Qed.

#[global]
Hint Rewrite @FixWf_unfold_ext_step : Recursors.

Ltac unfold_FixWf_ext :=
  match goal with
    |- context [ @FixWf ?A ?R ?WF ?P ?f ?x ] =>
    let step := fresh in
    set(step := fun y (_ : R y x) => @FixWf A R WF P f y) in *;
    rewrite (@FixWf_unfold_ext_step A R WF P f x step);
    [hidebody step; try red_eq_lhs (* Unfold the functional *)
    |reflexivity]
  end.

Ltac unfold_recursor_ext := unfold_FixWf_ext.

(** Inline so that we get back a term using general recursion. *)

Extraction Inline FixWf Fix Fix_F.

(** This hint database contains the constructors of every derived
   subterm relation. It is used to automatically find proofs that
   a term is a subterm of another.
   *)

Create HintDb subterm_relation discriminated.
Create HintDb rec_decision discriminated.

(** This is used to simplify the proof-search for recursive call obligations. *)

Ltac simpl_let :=
  match goal with
    [ H : let _ := ?t in _ |- _ ] =>
    match t with
    | fixproto => fail 1
    | _ => cbv zeta in H
    end
  end.

#[global]
Hint Extern 40 => progress (cbv beta in * || simpl_let) : Below.

(* This expands lets in the context to simplify proof search for recursive call
  obligations, as [eauto] does not do matching up-to unfolding of let-bound variables.
*)

#[global]
Hint Extern 10 => 
  match goal with
  [ x := _ |- _ ] => 
    lazymatch goal with
    |- context [ x ] => subst x 
    end
  end : Below.

(** We can automatically use the well-foundedness of a relation to get
   the well-foundedness of its transitive closure.
   Note that this definition is transparent as well as [wf_clos_trans],
   to allow computations with functions defined by well-founded recursion.
   *)

Lemma WellFounded_trans_clos `(WF : WellFounded A R) : WellFounded (clos_trans A R).
Proof. apply wf_clos_trans. apply WF. Defined.

#[global]
Hint Extern 4 (WellFounded (clos_trans _ _)) => 
  apply @WellFounded_trans_clos : typeclass_instances.

Lemma wf_MR {A R} `(WellFounded A R) {B} (f : B -> A) : WellFounded (MR R f).
Proof. red. apply measure_wf. apply H. Defined.

(* Do not apply [wf_MR] agressively, as Coq's unification could "invent" an [f] otherwise
   to unify. *)
#[global]
Hint Extern 0 (WellFounded (MR _ _)) => apply @wf_MR : typeclass_instances.

#[global]
Hint Extern 0 (MR _ _ _ _) => red : Below.

Instance lt_wf : WellFounded lt := lt_wf.

#[global]
Hint Resolve Arith.Lt.lt_n_Sn : Below.

(** We also add hints for transitive closure, not using [t_trans] but forcing to 
   build the proof by successive applications of the inner relation. *)

#[global]
Hint Resolve t_step : subterm_relation.

Lemma clos_trans_stepr A (R : relation A) (x y z : A) :
  R y z -> clos_trans A R x y -> clos_trans A R x z.
Proof. intros Hyz Hxy. exact (t_trans _ _ x y z Hxy (t_step _ _ _ _ Hyz)). Defined.

#[global]
Hint Resolve clos_trans_stepr : subterm_relation.

(** The default tactic to build proofs of well foundedness of subterm relations. *)

Create HintDb solve_subterm discriminated.

#[global]
Hint Extern 4 (_ = _) => reflexivity : solve_subterm.
#[global]
Hint Extern 10 => eapply_hyp : solve_subterm.

Ltac solve_subterm := intros;
  apply Transitive_Closure.wf_clos_trans;
  red; intros; simp_sigmas; on_last_hyp ltac:(fun H => depind H); constructor;
  intros; simp_sigmas; on_last_hyp ltac:(fun HR => depind HR);
  simplify_dep_elim; try typeclasses eauto with solve_subterm.

(** A tactic to launch a well-founded recursion. *)

Ltac rec_wf_fix recname kont :=
  let hyps := fresh in intros hyps;
  intro; on_last_hyp ltac:(fun x => rename x into recname;
                           unfold MR at 1 in recname) ;
  destruct_right_sigma hyps; try curry recname; simpl in recname;
  kont recname.

(* Ltac rec_wf_fix x recname fixterm := *)
(*   apply fixterm ; clear_local ;  *)
(*   intros until 1 ; simp_sigmas ;  *)
(*     on_last_hyp ltac:(fun x => rename x into recname) ; *)
(*   simplify_dep_elim ; intros ; unblock_goal ; intros ; *)
(*   move recname at bottom ; try curry recname ; simpl in recname. *)

(** The [do] tactic but using a Coq-side nat. *)

Ltac do_nat n tac :=
  match n with
    | 0 => idtac
    | S ?n' => tac ; do_nat n' tac
  end.

(** Generalize an object [x], packing it in a sigma type if necessary. *)

Ltac sigma_pack n t :=
  let packhyps := fresh "hypspack" in
  let xpack := fresh "pack" in
  let eos' := fresh "eos" in
  match constr:(n) with
  | 0%nat => set (eos' := the_end_of_the_section); move eos' at top
  | _ => do_nat n ltac:(idtac; revert_last); set (eos' := the_end_of_the_section);
         do_nat n intro
  end;
  uncurry_hyps packhyps;
  (progress (set(xpack := t) in |- ;
             cbv beta iota zeta in xpack; revert xpack;
             pattern sigma packhyps;
             clearbody packhyps;
             revert packhyps;
             clear_nonsection; clear eos')).

(** We specialize the tactic for [x] of type [A], first packing 
   [x] with its indices into a sigma type and finding the declared 
   relation on this type. *)

Ltac rec_wf recname t kont := 
  sigma_pack 0 t;
    match goal with
      [ |- forall (s : ?T) (s0 := @?b s), @?P s ] => 
      let fn := constr:(fun s : T => b s) in
      let c := constr:(wellfounded (R:=MR _ fn)) in
      let wf := constr:(FixWf (WF:=c)) in
      intros s _; revert s; refine (wf P _); simpl ;
      rec_wf_fix recname kont
    end. 

Ltac rec_wf_eqns recname x := 
  rec_wf recname x 
         ltac:(fun rechyp => add_pattern (hide_pattern rechyp)).

Ltac rec_wf_rel_aux recname n t rel kont :=
  sigma_pack n t;
    match goal with
      [ |- forall (s : ?T) (s0 := @?b s), @?P s ] => 
      let fn := constr:(fun s : T => b s) in
      let c := constr:(wellfounded (R:=MR rel fn)) in
      let wf := constr:(FixWf (WF:=c)) in
      intros s _; revert s; refine (wf P _); simpl ;
      rec_wf_fix recname kont
    end.

Ltac rec_wf_rel recname x rel :=
  rec_wf_rel_aux recname 0 x rel ltac:(fun rechyp => idtac).

(** Define non-dependent lexicographic products *)

Arguments lexprod [A] [B] _ _.

Section Lexicographic_Product.

  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Inductive lexprod : A * B -> A * B -> Prop :=
    | left_lex :
      forall (x x':A) (y:B) (y':B),
        leA x x' -> lexprod (x, y) (x', y')
    | right_lex :
      forall (x:A) (y y':B),
        leB y y' -> lexprod (x, y) (x, y').

  Lemma acc_A_B_lexprod :
    forall x:A, Acc leA x -> (well_founded leB) ->
                forall y:B, Acc leB y -> Acc lexprod (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros H2 y.
    induction 1 as [x0 H IHAcc0]; intros.
    apply Acc_intro.
    destruct y as [x2 y1]; intro H6.
    simple inversion H6; intro.
    injection H1. injection H3. intros. subst. clear H1 H3.
    apply IHAcc; auto with sets.
    injection H1. intros; subst.
    injection H3. intros; subst.
    auto.
  Defined.

  Theorem wf_lexprod :
    well_founded leA ->
    well_founded leB -> well_founded lexprod.
  Proof.
    intros wfA wfB; unfold well_founded.
    destruct a. 
    apply acc_A_B_lexprod; auto with sets; intros.
  Defined.

End Lexicographic_Product.

Instance wellfounded_lexprod A B R S `(wfR : WellFounded A R, wfS : WellFounded B S) : 
  WellFounded (lexprod A B R S) := wf_lexprod A B R S wfR wfS.

#[global]
Hint Constructors lexprod : Below.

(* NoCycle from well-foundedness. *)

Lemma well_founded_irreflexive {A} {R : relation A}{wfR : WellFounded R} :
  forall x y : A, R x y -> x = y -> False.
Proof.
  intros x y Ryy ->. red in wfR.
  induction (wfR y) as [y accy IHy].
  apply (IHy _ Ryy Ryy).
Qed.

Definition NoCycle_WellFounded {A} (R : relation A) (wfR : WellFounded R) : NoCyclePackage A :=
  {| NoCycle := R;
     noCycle := well_founded_irreflexive |}.
Existing Instance NoCycle_WellFounded.

#[global]
Hint Extern 30 (@NoCycle ?A (NoCycle_WellFounded ?R ?wfr) _ _) =>
  hnf; typeclasses eauto with subterm_relation : typeclass_instances.
