From Equations.Prop Require Import Equations.
Inductive T1: Type :=
| C { T: Type }: T1
.
Parameter t1: T1.
Record T2: Type := mkT2 { }.

Equations f (t2: T2): T2
  by wf 0 lt :=

  f t2 :=
    match t1 with
    | C =>
      let x := fun (N': T2) => f N' in
      t2
    end
.

Axiom  admit : forall{A}, A.
Next Obligation. Admitted.
Print HintDb f_wf_obligations.
Next Obligation. apply admit. Defined.  Print   f_elim.
Admitted.
