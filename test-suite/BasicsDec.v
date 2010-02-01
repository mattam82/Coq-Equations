Require Import Equations DepElimDec Bvector.

Notation " x ~=~ y " := ((existT _ _ x) = (existT _ _ y)).

Unset Printing All.

Inductive foo (A : Type)
            : forall H H0 : nat, vector A H -> vector A H0 -> Prop :=.

Derive Signature for foo.

Require Import EqDec.

Instance vector_eqdec {A n} `(EqDec A) : EqDec (vector A n). 
Proof. intros. intros x. induction x. left. now depelim y.
  intro y; depelim y.
  destruct (eq_dec a a0); subst. 
  destruct (IHx y0). subst.
  left; reflexivity.
  right. intro. apply n. injection H0. simpdep. reflexivity.
  right. intro. apply n. injection H0. simpdep. reflexivity.
Defined.

Derive Subterm for vector.

Print Assumptions well_founded_vector_direct_subterm.

(** A closed proof of well-foundedness relying on the decidability
   of [A]. *)

Lemma well_founded_vector_direct_subterm' :
  forall A : Type, EqDec A -> WellFounded (vector_subterm A).
Proof. intros.
  apply Transitive_Closure.wf_clos_trans.
  intro. simp_exists. induction X0. constructor; intros.
  simp_exists. depelim H.
  constructor; intros.
  simp_exists. depelim H.
  assumption.
Defined.
