(**********************************************************************)
(* Equations                                                          *)
(* Copyright (c) 2009-2016 Matthieu Sozeau <matthieu.sozeau@inria.fr> *)
(**********************************************************************)
(* This file is distributed under the terms of the                    *)
(* GNU Lesser General Public License Version 2.1                      *)
(**********************************************************************)

Require Import Wf_nat Arith.Lt Bvector Relations Wellfounded.
From Equations Require Import Init Classes Below Signature EqDec NoConfusion.
Require Import ConstantsSProp.

Generalizable Variables A R S B.

Scheme sAcc_dep := Induction for sAcc Sort Prop.

(** The fixpoint combinator associated to a well-founded relation,
   just reusing the [Wf.Fix] combinator. *)

Definition sAcc_inv {A : Type} {R : A -> A -> SProp} {x : A} (a : sAcc R x) : forall {y : A}, R y x -> sAcc R y :=
  match a with
  | sAcc_intro _ _ H => H
  end.

Definition Fix_F {A : Type} {R : A -> A -> SProp} (P : A -> Type)
           (F : forall x : A, (forall y : A, R y x -> P y) -> P x) : forall {x : A}, sAcc R x -> P x :=
  fix Fix_F (x : A) (a : sAcc R x) { struct a } :=
    F x (fun (y : A) (h : R y x) => Fix_F y (sAcc_inv a h)).

Definition Fix :=
  fun {A : Type} {R : A -> A -> SProp} (Rwf : swell_founded R) (P : A -> Type)
      (F : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) => Fix_F P F (Rwf x).

Definition FixWf `{WF:SWellFounded A R} (P : A -> Type)
  (step : forall x : A, (forall y : A, R y x -> P y) -> P x) : forall x : A, P x :=
  Fix swellfounded P step.

Lemma Acc_pi (A : Type) (R : srelation A) i (x y : sAcc R i) : x = y.
Proof.
  revert y.
  induction x using sAcc_dep.
  intros. destruct y.
  f_equal.
  extensionality y.
Admitted.

Lemma FixWf_unfold `{WF : SWellFounded A R} (P : A -> Type)
  (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A) :
  FixWf P step x = step x (fun y _ => FixWf P step y).
Proof.
  intros. unfold FixWf, Fix. destruct swellfounded.
  simpl. f_equal. extensionality y. extensionality h.
  f_equal. apply Acc_pi.
Admitted.

Hint Rewrite @FixWf_unfold : Recursors.

Lemma FixWf_unfold_step : 
  forall (A : Type) (R : srelation A) (WF : SWellFounded R) (P : A -> Type)
    (step : forall x : A, (forall y : A, R y x -> P y) -> P x) (x : A)
    (step' : forall y : A, R y x -> P y),
    step' = (fun (y : A) (_ : R y x) => FixWf P step y) ->
    FixWf P step x = step x step'.
Proof. intros. rewrite FixWf_unfold, H. reflexivity. Qed.

Hint Rewrite @FixWf_unfold_step : Recursors.

Ltac unfold_FixWf :=
  match goal with
    |- context [ @FixWf ?A ?R ?WF ?P ?f ?x ] =>
    let step := fresh in
    set(step := fun y (_ : R y x) => @FixWf A R WF P f y) in *;
    rewrite (@FixWf_unfold_step A R WF P f x step); [hidebody step|reflexivity]
  end.

Ltac unfold_recursor := unfold_FixWf.

(** Inline so that we get back a term using general recursion. *)

Extraction Inline FixWf Fix Fix_F.

(** This hint database contains the constructors of every derived
   subterm relation. It is used to automatically find proofs that
   a term is a subterm of another.
   *)

Create HintDb subterm_relation discriminated.
Create HintDb Recursors discriminated.
Create HintDb rec_decision discriminated.

(** We can automatically use the well-foundedness of a relation to get
   the well-foundedness of its transitive closure.
   Note that this definition is transparent as well as [wf_clos_trans],
   to allow computations with functions defined by well-founded recursion.
   *)

Lemma WellFounded_trans_clos `(WF : SWellFounded A R) : SWellFounded (@strans_clos A R).
Proof. Admitted. (* apply wf_trans_clos. apply WF. Defined. *)

Hint Extern 4 (WellFounded (clos_trans _ _)) => 
  apply @WellFounded_trans_clos : typeclass_instances.

Definition sMR {A B} (R : B -> B -> SProp) (f : A -> B) := fun x y => R (f x) (f y).

Section Measure_well_founded.

  (* Measure relations are well-founded if the underlying relation is well-founded. *)

  Variables T M: Type.
  Variable R: M -> M -> SProp.
  Hypothesis wf: swell_founded R.
  Variable m: T -> M.

  Lemma measure_wf: swell_founded (sMR R m).
  Proof with auto.
    unfold swell_founded.
    cut (forall (a: M) (a0: T), m a0 = a -> sAcc (sMR R m) a0).
      intros H x.
      apply (H (m x))...
    apply (@Fix M R wf (fun mm => forall a, m a = mm -> sAcc (sMR R m) a)).
    intros.
    apply sAcc_intro.
    intros.
    unfold sMR in H1.
    rewrite H0 in H1.
    apply (H (m y))...
  Defined.

End Measure_well_founded.

Instance wf_MR {A R} `(SWellFounded A R) {B} (f : B -> A) : SWellFounded (sMR R f).
Proof. red. apply measure_wf. apply H. Defined.

Hint Extern 0 (sMR _ _ _ _) => red : Below.

Fixpoint le (n m : nat) : SProp :=
  match n with
  | O => sTrue
  | S n' => match m with
            | O => sFalse
            | S m' => le n' m'
            end
  end.
Lemma le_x_x x : le x x.
Proof.
  induction x; simpl; try constructor. auto.
Defined.

Lemma le_trans x y z : le x y -> le y z -> le x z.
Proof.
  induction x in y, z |- *; simpl; try constructor.
  destruct y. intros [].
  intros Hx Hy. destruct z. elim Hy. simpl in Hy. eauto.
Defined.

Definition lt (n m : nat) : SProp := le (S n) m.

Instance lt_wf : SWellFounded lt.
Proof.
  red. red. intros x. generalize (le_x_x x). generalize x at 1 3.
  induction x. intros. destruct x. constructor. intros. elim H0. elim H.
  intros.
  destruct x0. constructor. intros. elim H0.
  constructor. intros. red in H0. simpl in *.
  apply IHx. apply le_trans with x0; auto.
Defined.

Hint Resolve lt_n_Sn : Below.

(** We also add hints for transitive closure, not using [t_trans] but forcing to 
   build the proof by successive applications of the inner relation. *)

Hint Resolve t_step : subterm_relation.

Lemma clos_trans_stepr A (R : relation A) (x y z : A) :
  R y z -> clos_trans A R x y -> clos_trans A R x z.
Proof. intros Hyz Hxy. exact (t_trans _ _ x y z Hxy (t_step _ _ _ _ Hyz)). Defined.

Hint Resolve clos_trans_stepr : subterm_relation.

(** The default tactic to build proofs of well foundedness of subterm relations. *)

Ltac simp_sigmas := repeat destruct_one_sigma ; simpl in *.

Ltac eapply_hyp :=
  match goal with 
    [ H : _ |- _ ] => eapply H
  end.

Create HintDb solve_subterm discriminated.

Hint Extern 4 (_ = _) => reflexivity : solve_subterm.
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
                           unfold sMR at 1 in recname) ;
  destruct_right_sigma hyps; try curry recname; simpl in recname;
  kont recname.

(* Ltac rec_wf_fix x recname fixterm := *)
(*   apply fixterm ; clear_local ;  *)
(*   intros until 1 ; simp_sigmas ;  *)
(*     on_last_hyp ltac:(fun x => rename x into recname) ; *)
(*   simplify_dep_elim ; intros ; unblock_goal ; intros ; *)
(*   move recname at bottom ; try curry recname ; simpl in recname. *)

(** Generalize an object [x], packing it in a sigma type if necessary. *)


Ltac sigma_pack t :=
  let packhyps := fresh "hypspack" in
  let xpack := fresh "pack" in
  uncurry_hyps packhyps; 
    (progress (set(xpack := t) in |- ;
               cbv beta iota zeta in xpack; revert xpack;
               pattern sigma packhyps; 
               clearbody packhyps;
               revert packhyps;
               clear_nonsection)).

(** We specialize the tactic for [x] of type [A], first packing 
   [x] with its indices into a sigma type and finding the declared 
   relation on this type. *)

Ltac rec_wf recname t kont := 
  sigma_pack t;
    match goal with
      [ |- forall (s : ?T) (s0 := @?b s), @?P s ] => 
      let fn := constr:(fun s : T => b s) in
      let c := constr:(swellfounded (R:=MR _ fn)) in
      let wf := constr:(FixWf (WF:=c)) in
      intros s _; revert s; refine (wf P _); simpl ;
      rec_wf_fix recname kont
    end. 

Ltac rec_wf_eqns recname x := 
  rec_wf recname x 
         ltac:(fun rechyp => add_pattern (hide_pattern rechyp)).

Ltac rec_wf_rel_aux recname t rel kont := 
  sigma_pack t;
    match goal with
      [ |- forall (s : ?T) (s0 := @?b s), @?P s ] => 
      let fn := constr:(fun s : T => b s) in
      let c := constr:(swellfounded (R:=sMR rel fn)) in
      let wf := constr:(FixWf (WF:=c)) in
      intros s _; revert s; refine (wf P _); simpl ;
      rec_wf_fix recname kont
    end. 

Ltac rec_wf_eqns_rel recname x rel :=
  rec_wf_rel_aux recname x rel ltac:(fun rechyp => add_pattern (hide_pattern rechyp)).

Ltac rec_wf_rel recname x rel :=
  rec_wf_rel_aux recname x rel ltac:(fun rechyp => idtac).

(** The [pi] tactic solves an equality between applications of the same function,
   possibly using proof irrelevance to discharge equality of proofs. *)

Ltac pi := repeat progress (f_equal || reflexivity) ; apply proof_irrelevance.


(** Define non-dependent lexicographic products *)

Require Import Wellfounded Relation_Definitions.
Require Import Relation_Operators Lexicographic_Product Wf_nat.
Arguments lexprod [A] [B] _ _.

Section Lexicographic_Product.

  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> SProp.
  Variable leB : B -> B -> SProp.

  Inductive lexprod : A * B -> A * B -> SProp :=
    | left_lex :
      forall (x x':A) (y:B) (y':B),
        leA x x' -> lexprod (x, y) (x', y')
    | right_lex :
      forall (x:A) (y y':B),
        leB y y' -> lexprod (x, y) (x, y').

  Lemma acc_A_B_lexprod :
    forall x:A, sAcc leA x -> (swell_founded leB) ->
                forall y:B, sAcc leB y -> sAcc lexprod (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros H2 y.
    induction 1 as [x0 H IHAcc0]; intros.
    apply sAcc_intro.
    destruct y as [x2 y1]; intro H6.
  Admitted.
  (*   apply sAcc_inv in H6. auto. *)

  (*   apply IHAcc; auto with sets. *)
  (*   noconf H3; noconf H1.  *)
  (* Defined. *)

  Theorem wf_lexprod :
    swell_founded leA ->
    swell_founded leB -> swell_founded lexprod.
  Proof.
    intros wfA wfB; unfold swell_founded.
    destruct x.
    apply acc_A_B_lexprod; auto with sets; intros.
  Defined.
End Lexicographic_Product.

Instance wellfounded_lexprod A B R S `(wfR : SWellFounded A R, wfS : SWellFounded B S) :
  SWellFounded (lexprod A B R S) := wf_lexprod A B R S wfR wfS.

Hint Constructors lexprod : Below.
