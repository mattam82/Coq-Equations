From Stdlib Require Import List String.
From Equations.Prop Require Import Equations.

Module A.
Section test.
  Set Equations Transparent.
  Set Universe Polymorphism.
  Import Sigma_Notations.

  Open Scope nat.

  Inductive term := T  | L (t: list term).

  Definition env_ty :Type := string -> option (list string *  term).

  Inductive ty : forall (A B  : Type), (A -> B -> Type) -> Type :=
    | f_a : ty env_ty term (fun  _ _ => nat)
    | f_b : ty env_ty  string (fun  _ _ =>  nat)
    .

    Derive Signature NoConfusion for ty.

    Fixpoint T_size (t:term) :nat := match t with
    | T => 0
    | L ts => List.fold_left (fun acc t => acc + (T_size t)) ts 1
    end.

    Equations measure : (Σ A B P (_ : A) (_ : B) , ty A B P) -> nat :=
        | (_,_,_, _,t,f_a) => T_size t
        | (_,_,_,_,_,f_b)  =>  0

.
Definition rel := Program.Wf.MR lt measure.

#[global] Instance: WellFounded rel.
Proof.
  red. apply Wf.measure_wf. apply Wf_nat.lt_wf.
Defined.

Definition pack {A B } {P} (x1 : A) (x2 : B) (t : ty A B P) :=
     (A,B,P, x1, x2, t) : (Σ A B  P (_ : A) (_ : B) , ty A B  P).

End test.
Equations mutrecf {A B} {P} (t : ty A B P) (a : A) (b : B)  : P a b   by wf (pack a b t) rel :=
| f_a , _, _  => 0
| f_b,env,fname with env fname =>
    {
        | Some (_,t) =>
            let heretofail := 0 in
            let reccall := mutrecf f_a env t in
            0
        | None =>  0
    }
.

Solve Obligations with intros; red ;red ; cbn ; auto with arith.
Parameter h :forall b, (T_size b < 0)%nat.
Next Obligation. red. red. cbn. apply h. Qed.
End A.

Module B.
Section todo.
  Set Equations Transparent.
  Set Universe Polymorphism.

  Definition M (T : Type) : Type := nat -> T * nat.

  Definition bind {A B : Type} (m : M A) (f : A -> M B) : M B :=
      fun c =>  let (a, c') := m c in f a c'.

  Inductive termA := T (p:termB) with termB := P.

  Inductive ty : forall (A  : Type), (A  -> Type) -> Type :=
  | f_a : ty  termB (fun _  => @M nat)
  | f_b : ty  termA (fun _ => @M nat)
  .
  Derive Signature NoConfusion for ty.
  Import Sigma_Notations.

  Equations measure : (Σ A P (_ : A) , ty A P) -> nat :=
      | (_,_,p,f_a) => 0
      | (_,_,t,f_b) => 1
  .

  Definition rel := Program.Wf.MR lt measure.
  #[global] Instance: WellFounded rel.
  Proof.
      red. apply Wf.measure_wf. apply Wf_nat.lt_wf.
  Defined.

  Definition pack {A } {P} (x1 : A)  (t : ty A P) :=
       (A,P, x1, t) : (Σ A  P (_ : A) , ty A  P).
End todo.

Equations mutrec {A} {P} (t : ty A  P) (x: A) : P x  by wf (pack x t) rel :=

| f_a , _ => fun _ => (0,0)%nat
| f_b ,T p =>
    bind (fun _ => (0,0%nat)) (fun c =>
        let heretofail := 0 in
        bind (mutrec f_a p) (fun _ =>
            fun _ => (0,0)%nat
        )
    )
.
Solve Obligations with red ;red ; cbn ; auto with arith.
About mutrec_elim.
End B.