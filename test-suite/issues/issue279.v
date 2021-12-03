From Equations Require Import Equations.
Set Equations Transparent.

Module Initial.
Inductive term :=
| tBox
| tConstruct (ind : nat) (c : nat)
| tConst (kn : nat).

Equations eta_exp_discr (t : term) : Prop :=
eta_exp_discr (tConstruct ind c) := False;
eta_exp_discr (tConst kn) := False;
eta_exp_discr _ := True.

Inductive eta_exp_view : term -> Type :=
| eta_exp_view_Construct ind c : eta_exp_view (tConstruct ind c)
| eta_exp_view_Const kn : eta_exp_view (tConst kn)
| eta_exp_view_other t : eta_exp_discr t -> eta_exp_view t.

Equations eta_exp_viewc (t : term) : eta_exp_view t :=
eta_exp_viewc (tConstruct ind c) := eta_exp_view_Construct ind c;
eta_exp_viewc (tConst kn) := eta_exp_view_Const kn;
eta_exp_viewc t := eta_exp_view_other t _.

Definition decompose_app (t : term) : term * nat := (t, 0).

Definition inspect {A} (a : A) : { x : A | x = a } :=
  exist _ a eq_refl.

Fail Equations eta_expand (t : term) : nat :=
eta_expand t with inspect (decompose_app t) := {
  | exist _ (t', n) _ with eta_exp_viewc t' := {
    | eta_exp_view_Construct ind c := 0;
    | eta_exp_view_Const n := n;
    | eta_exp_view_other t' discr := 0
    }
  }.
End Initial.

Fail Equations eta_expand : nat :=
eta_expand with 0 :=
  | n with 5 :=
    | n := n.

Equations test
  (n : nat) : nat :=
  test 1 := 17 ;
  test n with true := {
    | true => n
    | false => 17
  }.
    
Example test' := (eq_refl : test 2 = 2).