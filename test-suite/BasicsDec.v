Require Import Equations.Equations Equations.DepElimDec Bvector.

Ltac generalize_sig id cont ::=
  let id' := fresh id in
  get_signature_pack id id';
  hnf in (value of id'); hnf in (type of id');
  match goal with
  | |- context[ id ] =>
    generalize (@eq_refl _ id' : id' = id') ;
    unfold id' at 1;
    clearbody id'; simpl in id'; move id' after id;
    revert_until id'; rename id' into id;
      cont id
  | |- _ =>
    let id'1 := fresh id' in let id'2 := fresh id' in
    set (id'2 := pr2 id'); set (id'1 := pr1 id') in id'2;
    hnf in (value of id'1), (value of id'2);
    generalize (@eq_refl _ id'1 : id'1 = id'1);
    unfold id'1 at 1; clearbody id'2 id'1;
    clear id' id; compute in id'2;
    rename id'2 into id;
      cont id'1
  end.
  
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

(* FIXME Should not have to do that here. *)
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


(* FIXME Cannot prove well-foundedness automatically. *)
Derive Subterm for vector.
Print Assumptions well_founded_t_subterm.

(* FIXME Should not have to do that here.
         Also, the name should be [vector], not [t]. *)
Derive Signature for t_direct_subterm.

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
