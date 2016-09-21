Require Import Equations.Equations Equations.DepElimDec Bvector.
  
Inductive bar1 (A : Type) : A -> Prop := .
Inductive bar2 (A : Type) : (A -> A) -> Prop := .
Inductive bar3 (A B : Type) : A -> Prop := .
Inductive bar4 (A B : Type) : B -> Prop := .

Derive Signature for bar1.
Derive Signature for bar2.
Derive Signature for bar3.
Derive Signature for bar4.

Derive Signature for @eq.

Goal forall (U V : Type), Some U = Some V -> U = V.
Proof. intros. depelim H. reflexivity. Qed.

Notation " x ~=~ y " := ((existT _ _ x) = (existT _ _ y)).

Unset Printing All.

Inductive foo (A : Type)
            : forall H H0 : nat, vector A H -> vector A H0 -> Prop :=.

Derive Signature for foo.

Require Import Equations.EqDec.

Derive Signature for Vector.t.

Instance vector_eqdec {A n} `(EqDec A) : EqDec (vector A n). 
Proof. intros. intros x. induction x. left. now depelim y.
  intro y; depelim y.
  destruct (eq_dec h h0); subst. 
  destruct (IHx y). subst.
  left; reflexivity.
  right. intro. apply n. injection H0. simpdep. reflexivity.
  right. intro. apply n. injection H0. simpdep. reflexivity.
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
  induction H; constructor; intros;
  simp_sigmas. simpl in *.
  depelim H; assumption.
  depelim H0. apply IHt.
Defined.
Print Assumptions well_founded_vector_direct_subterm'.
