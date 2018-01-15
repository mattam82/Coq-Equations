Require Import Program Bvector List.
Require Import Relations.
From Equations Require Import Equations DepElimDec.

From Equations Require Import Equations.

Equations silly {A} (l : list A) : list A :=
silly l by rec ((fix Ffix (x : list A) : nat :=
         match x with
         | []%list => 0
         | (_ :: x1)%list => S (Ffix x1)
         end) l) lt :=
silly nil := nil;
silly (cons a l) := a :: silly l.


Set Equations Debug.
Equations(noeqns noind) silly {A} (l : list A) : list A :=
silly l by rec (length l) lt :=
silly nil := nil;
silly (cons a l) := a :: silly l.

Definition silly_unfold {A} (l : list A) := match l with
                           | [] => []
                           | y :: l0 => y :: silly l0
                                            end.

Lemma silly_unfold_eq {A} (l : list A) : silly l = silly_unfold l.
Proof.
  unfold silly.  Subterm.unfold_recursor.
  Print Ltac do_depelim.
  do_depelim_nosimpl ltac:(fun x => idtac) l.
  do_case l.
  simplify_dep_elim.
  simplify_IH_hyps.

  intro. intros.
  unfold hidebody in H. revert H b0.
  match goal with
    |- context [ block ] => idtac
  end.

  unblock_dep_elim.

  do_intros l.
  generalize_by_eqs l.
  do_case l.
  unblock_goal.
  unfold block at 1.
  unblock_goal.

  Print Ltac depelim.
  destruct l.
  simpl in *.
  depelim l. reflexivity.

Module TestF.

Equations f (n : nat) : nat :=
f 0 := 42 ;
f (S m) with f m :=
{
f (S m) IH := _
}.

Write State bisect.
End TestF.