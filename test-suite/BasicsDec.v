Require Import Equations.Equations Bvector.
  
Inductive bar1 (A : Type) : A -> Prop := .
Inductive bar2 (A : Type) : (A -> A) -> Prop := .
Inductive bar3 (A B : Type) : A -> Prop := .
Inductive bar4 (A B : Type) : B -> Prop := .

Derive Signature for bar1 bar2 bar3 bar4.
Derive Signature for eq.

Goal forall (U V : Type), Some U = Some V -> U = V.
Proof. intros. depelim H. reflexivity. Qed.

Notation vector := Vector.t.

Derive Signature NoConfusionHom for Vector.t.

Unset Printing All.

Inductive foo (A : Type)
            : forall H H0 : nat, vector A H -> vector A H0 -> Prop :=.

Derive Signature for foo.

Instance vector_eqdec {A n} `(EqDec A) : EqDec (vector A n).
Proof. intros. intros x. induction x. left. now depelim y.
  intro y; depelim y.
  destruct (eq_dec h h0) as [eq|neq]; subst. 
  destruct (IHx y) as [eqy|neqy]. subst.
  left; reflexivity.
  right. intro H0. apply neqy. injection H0. revert H0.
  repeat simplify ?. simpl. reflexivity.
  right. intro H0. apply neq. now noconf H0.
Defined.

Derive Subterm for vector.

Print Assumptions well_founded_t_subterm.

(** A closed proof of well-foundedness relying on the decidability
   of [A]. *)

Lemma well_founded_vector_direct_subterm' :
  forall A : Type, EqDec A -> WellFounded (t_subterm A).
Proof. intros.
  apply Transitive_Closure.wf_clos_trans.
  intro. simp_sigmas.
  induction a; constructor; intros;
  simp_sigmas. simpl in *.
  depelim H. 
  depelim H. apply IHa.
Defined.
Print Assumptions well_founded_vector_direct_subterm'.
