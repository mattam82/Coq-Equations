Require Import Equations.Tactics Equations.Type.DepElim Equations.Type.WellFounded.

Ltac Equations.Init.simpl_equations ::= Equations.Type.DepElim.simpl_equations.

Ltac Equations.Init.depelim H ::= Equations.Type.DepElim.depelim H.
Ltac Equations.Init.depind H ::= Equations.Type.DepElim.depind H.

Ltac Equations.Init.noconf H ::= Equations.Type.DepElim.noconf H.

Create HintDb solve_subterm discriminated.

Hint Extern 4 (_ = _) => reflexivity : solve_subterm.
Hint Extern 10 => eapply_hyp : solve_subterm.

Ltac solve_subterm := intros;
  apply WellFounded.wf_trans_clos;
  red; intros; simp_sigmas; on_last_hyp ltac:(fun H => depind H); constructor;
  intros; simp_sigmas; on_last_hyp ltac:(fun HR => depind HR);
  simplify_dep_elim; try typeclasses eauto with solve_subterm.

Ltac Equations.Init.solve_subterm ::= solve_subterm.
