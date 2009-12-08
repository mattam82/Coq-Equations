Require Import Bvector.
Require Import Equations.Init Equations.Below Relations Wellfounded.

Generalizable Variables A R S B.

(** A class for well foundedness proofs. *)

Class WellFounded {A : Type} (R : relation A) :=
  wellfounded : well_founded R.

(** The fixpoint combinator associated to a well-founded relation,
   just reusing the [Wf.Fix] combinator. *)

Definition FixWf `{WF:WellFounded A R} (P : A -> Type)
  (step : Π x : A, (Π y : A, R y x -> P y) -> P x) : Π x : A, P x :=
  Fix wellfounded P step.

Lemma FixWf_unfold `{WF : WellFounded A R} (P : A -> Type)
  (step : Π x : A, (Π y : A, R y x -> P y) -> P x) (x : A) : 
  FixWf P step x = step x (fun y _ => FixWf P step y).
Proof. intros. unfold FixWf, Fix. destruct (wellfounded x).
  simpl. f_equal. extensionality y. extensionality h. pi.
Qed.
  
Hint Rewrite @FixWf_unfold : Recursors.

(** Inline so that we get back a term using general recursion. *)

Extraction Inline FixWf Fix Fix_F.

(** A class for subterm relations accompanied by their well foundedness 
   proofs. Instances can be derived automatically using 
   [Derive Subterm for ind] *)

Class SubtermRelation (A : Type) := 
  { subterm_relation : relation A ;
    subterm_relation_wf :> WellFounded subterm_relation }.

(** This hint database contains the constructors of every derived
   [SubtermRelation]. It is used to automatically find proofs that
   a term is a subterm of another.
   *)

Create HintDb subterm_relation discriminated.

(** We can automatically use the well-foundedness of a relation to get
   the well-foundedness of its transitive closure.
   Note that this definition is transparent as well as [wf_clos_trans],
   to allow computations with functions defined by well-founded recursion.
   *)

Lemma WellFounded_trans_clos `(WF : WellFounded A R) : WellFounded (clos_trans A R).
Proof. exact wf_clos_trans. Defined.

Hint Extern 4 (WellFounded (clos_trans _ _)) => 
  apply @WellFounded_trans_clos : typeclass_instances.

(** We also add hints for transitive closure, not using [t_trans] but forcing to 
   build the proof by successive applications of the inner relation. *)

Hint Resolve t_step : subterm_relation.

Lemma clos_trans_stepr A R (x y z : A) : clos_trans A R x y -> R y z -> clos_trans A R x z.
Proof. intros A R x y z Hxy Hyz. exact (t_trans _ _ x y z Hxy (t_step _ _ _ _ Hyz)). Defined.

Hint Resolve clos_trans_stepr : subterm_relation.

(** The default tactic to build proofs of well foundedness of subterm relations. *)

Ltac simp_exists := destruct_exists ; simpl in *.

Ltac solve_subterm := intros ; apply wf_clos_trans ;
  red ; intros; simp_exists;
  on_last_hyp ltac:(fun i => induction i); constructor ; 
  simpl; intros; simp_exists; on_last_hyp ltac:(fun H => now depelim H).

(** A tactic to launch a well-founded recursion. *)

Ltac rec_wf x recname fixterm :=
  apply fixterm ; clear_local ; 
  intros until 1 ; simp_exists ; 
    on_last_hyp ltac:(fun x => rename x into recname) ;
  simplify_dep_elim ; intros ; unblock_goal ; intros ;
  move recname at bottom ; repeat curry recname ; simpl in recname.

(** Generalize an object [x], packing it in a sigma type if necessary. *)

Ltac generalize_pack x :=
  let xpack := fresh x "pack" in
    (progress (generalize_eqs_vars x ; pack x as xpack ; 
      move xpack before x; clearbody xpack; clear; rename xpack into x))
    || revert_until x.

(** We specialize the tactic for [x] of type [A], first packing 
   [x] with its indices into a sigma type and find the declared 
   relation on this type. *)

Ltac rec_wf_eqns x recname := 
  move x at top; revert_until x; generalize_pack x; pattern x;
  let ty := type of x in
  let ty := eval simpl in ty in
  let wfprf := constr:(wellfounded (A:=ty)) in
  let fixterm := constr:(FixWf (WF:=wfprf)) in
    rec_wf x recname fixterm ; intros ;
      add_pattern (hide_pattern recname) ; instantiate.

Ltac solve_rec ::= simpl in * ; cbv zeta ; intros ; 
  try typeclasses eauto with subterm_relation Below.

(** The [pi] tactic solves an equality between applications of the same function,
   possibly using proof irrelevance to discharge equality of proofs. *)

Ltac pi := repeat progress (f_equal || reflexivity) ; apply proof_irrelevance.

(** We need a theory of well-founded relations on inductive families to use 
   this with dependent inductive types. *)

(** A family relation is just a heterogeneous relation, where the indices of
   the related objects might vary. *)

Class FamRelation {A} (I : A -> Type) : Type := 
  fam_relation : forall {i i'}, I i -> I i' -> Prop.

(** The accessibility predicate is a natural generalization of the non-dependent one. *)

Inductive Acc_family {A : Type} {I : A -> Type} (R : Π i i', I i -> I i' -> Prop) (i : A) (x : I i) : Prop :=
  Acc_intro : (Π (i' : A) (y : I i'), R i' i y x -> Acc_family R i' y) -> Acc_family R i x.

(** The inversion principle for [Acc_family]. *)

Definition Acc_family_inv {A I} (R : @FamRelation A I) (i : A) (x : I i) (H : Acc_family R i x) : 
  Π i' (y : I i'), fam_relation y x -> Acc_family R i' y :=
  let 'Acc_intro f := H in f.

(** A class for well-founded family relations. *)

Class WfFam {A} {I : A -> Type} (R : FamRelation I) : Prop :=
  wf_fam : Π {i} a, Acc_family R i a.

(** The associated fixpoint combinator. *)

Definition Fix_fam {A I} `(R : FamRelation A I) (P : Π a : A, I a -> Type)
  (ind : Π (i : A) (x : I i), (Π (i' : A) (y : I i'), R i' i y x -> P i' y) -> P i x) 
  i (x : I i) (acc : Acc_family R i x) : P i x.
  intros. unfold FamRelation in *. revert P ind.
  induction acc. intros.
  apply ind. intros. apply X. assumption. auto.
Defined.

Definition FixWfFam {A I R} {WF : @WfFam A I R} (P : Π a : A, I a -> Type)
  (step : Π (i : A) (x : I i), (Π (i' : A) (y : I i'), R i' i y x -> P i' y) -> P i x)
  i x : P i x :=
  Fix_fam R P step i x (wf_fam x).

(** Again we can take the transitive closure of family relations and prove that
   it preserves well-foundedness. *)

Inductive trans_clos_fam {A} {I : A -> Type} (R : FamRelation I) : FamRelation I :=
| trans_clos_fam_one : Π {i i'} (x : I i) (y : I i'), R _ _ x y -> trans_clos_fam R _ _ x y
| trans_clos_fam_step : Π {i i' i''} (x : I i) (y : I i') (z : I i''), 
  trans_clos_fam R _ _ x y -> R _ _ y z -> trans_clos_fam R _ _ x z.

Implicit Arguments trans_clos_fam [ [A] [I] [i] [i'] ].

Hint Constructors trans_clos_fam : subterm_relation.

Lemma trans_clos_fam_trans {A} {I : A -> Type} (R : FamRelation I) 
  (i i' i'' : A) (x : I i) (x : I i) (y : I i') (z : I i'') : 
  trans_clos_fam R x y -> trans_clos_fam R y z -> trans_clos_fam R x z.
Proof. intros. revert x0 H.
  induction H0; intros. eapply trans_clos_fam_step ; eauto.

  pose (IHtrans_clos_fam _ H1).
  eapply trans_clos_fam_step ; eauto.
Defined.

Section WfTransClos.
  Context {A} {I : A -> Type} (R : FamRelation I).

  Let trans_clos : FamRelation I := @trans_clos_fam _ _ R.

  Lemma Acc_family_trans_clos : forall {i} (x:I i), Acc_family R i x -> Acc_family trans_clos i x.
    induction 1. 
    apply Acc_intro.
    intros i' y.
    induction 1; auto with sets.
    apply Acc_family_inv with i' y; auto with sets.
  Defined.

  Hint Resolve @Acc_family_trans_clos.

  Global Instance wf_fam_trans_clos : WfFam R -> WfFam trans_clos.
  Proof.
    unfold WfFam in |- *; auto with sets.
  Defined.
End WfTransClos.

(** To launch a well-founded proof using a family relation. *)

Class SubtermFamRelation (A : Type) := 
  { subterm_fam_index : Type ;
    subterm_fam_fam : subterm_fam_index -> Type ;
    subterm_fam_relation : FamRelation subterm_fam_fam ;
    subterm_fam_relation_wf :> WfFam subterm_fam_relation }.

Ltac rec_fam x recname :=
  let ty := type of x in
  let wfprf := constr:(subterm_fam_relation_wf (A:=ty)) in
  let transwfprf := constr:(wf_fam_trans_clos _ wfprf) in
  let fixterm := constr:(FixWfFam (WF:=transwfprf)) in
    rec_wf x recname fixterm ; 
    add_pattern (hide_pattern recname) ; instantiate.
