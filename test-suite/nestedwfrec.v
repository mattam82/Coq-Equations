Require Import Equations.Equations.
Require Import Lia.


    (* Ltac Equations.Subterm.rec_wf_eqns_rel recname x rel ::= *)
    (*   Subterm.rec_wf_rel_aux recname x rel ltac:(fun rechyp => add_pattern (hide_pattern rechyp)); *)
    (*   unfold MR in *; simpl in *; try match goal with *)
    (*   | [ H : unit |- _ ] => destruct H *)
    (*   end. *)

    (* Goal forall (n : nat) (f : (forall n' : nat, lt n' n -> nat)) *)
    (*             (m : nat) (H : m < S n), True. *)
    (*   set_eos. *)
    (*   (* intros. *) *)
    (*   (* assert (eos' := the_end_of_the_section). move eos' before f. *) *)
    (*   intros. *)
    (*   Subterm.rec_wf_eqns_rel fn m lt. *)
    (*   red. specialize (fn _ f). destruct m as [|m']. *)
    (*   exact I. *)
    (*   apply (fn m'). *)

    (* Admitted. *)

Equations f (n : nat) : nat by rec n lt :=
  f 0 := 0;
  f (S n) := g n _

  where g (n' : nat) (H : n' < S n) : nat by rec n' lt :=
  g 0 _ := 0;
  g (S n') H := f n' + g _ f n' _.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Next Obligation. lia. Qed.
