From Equations Require Import Equations.
Import Equations.Prop.Subterm Equations.Prop.DepElim.

Unset Equations With Funext.

Parameter size : forall {A}, list A -> nat.

Set Equations Debug.
Ltac unfold_FixWf :=
match goal with
     |- context [ @FixWf ?A ?R ?WF ?P ?f ?x ] =>
     let step := fresh in
     set(step := fun y (_ : R y x) => @FixWf A R WF P f y) in *;
     unshelve erewrite (@FixWf_unfold_step A R WF P f x _ step);
     [red; intros (* Extensionality proof *)
     |hidebody step; DepElim.red_eq_lhs (* Unfold the functional *)
     |reflexivity]
end.

Equations test (s : list bool) : list bool by wf (size s) lt:=
  test pn with true => {
  | true := nil;
  | false := nil }.
  Obligation Tactic := idtac.
  Next Obligation.
  unfold test, test_unfold. intros.
  unfold_FixWf.
  red_eq.
  unfold test_functional.

  Defined.
  
Equations(noeqns) test_unfold (s : list bool) : list bool :=
  test_unfold pn with true => {
  | true := nil;
  | false := nil }.

Lemma test_unfold_eq s : test s = test_unfold s.
Proof.

  Inspect 10.