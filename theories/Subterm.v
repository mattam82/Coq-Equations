Require Import Bvector.
Require Import Equations.Init Equations.Below Relations Wellfounded.

Generalizable Variables A R S B.

(** A class for well foundedness proofs.
   Instances can be derived automatically using [Derive Subterm for ind]. *)

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
Proof. intros. unfold FixWf, Fix. destruct wellfounded.
  simpl. f_equal. extensionality y. extensionality h. pi.
Qed.
  
Hint Rewrite @FixWf_unfold : Recursors.

(** Inline so that we get back a term using general recursion. *)

Extraction Inline FixWf Fix Fix_F.

(** This hint database contains the constructors of every derived
   subterm relation. It is used to automatically find proofs that
   a term is a subterm of another.
   *)

Create HintDb subterm_relation discriminated.
Create HintDb Recursors discriminated.

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

Lemma clos_trans_stepr A (R : relation A) (x y z : A) : R y z -> clos_trans A R x y -> clos_trans A R x z.
Proof. intros A R x y z Hyz Hxy. exact (t_trans _ _ x y z Hxy (t_step _ _ _ _ Hyz)). Defined.

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
   [x] with its indices into a sigma type and finding the declared 
   relation on this type. *)

Ltac rec_wf_eqns x recname := 
  move x at top; revert_until x; generalize_pack x; pattern x;
  let ty := type of x in
  let ty := eval simpl in ty in
  let wfprf := constr:(wellfounded (A:=ty)) in
  let fixterm := constr:(FixWf (WF:=wfprf)) in
    rec_wf x recname fixterm ; intros ;
      add_pattern (hide_pattern recname) ; instantiate.

Ltac rec_wf_eqns_rel x recname rel := 
  move x at top; revert_until x; generalize_pack x; pattern x;
  let ty := type of x in
  let ty := eval simpl in ty in
  let wfprf := constr:(wellfounded (A:=ty) (R:=rel)) in
  let fixterm := constr:(FixWf (WF:=wfprf)) in
    rec_wf x recname fixterm ; intros ;
      add_pattern (hide_pattern recname) ; instantiate.

Ltac solve_rec ::= simpl in * ; cbv zeta ; intros ; 
  try typeclasses eauto with subterm_relation Below.

(** The [pi] tactic solves an equality between applications of the same function,
   possibly using proof irrelevance to discharge equality of proofs. *)

Ltac pi := repeat progress (f_equal || reflexivity) ; apply proof_irrelevance.
