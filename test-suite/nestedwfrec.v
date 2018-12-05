Require Import Equations.Equations.
Require Import Lia.



    (* Admitted. *)
Axiom cheat : forall {A}, A.


    (* Goal forall (n : nat) (f : (forall n' : nat, lt n' n -> nat)) *)
    (*             (m : nat) (H : m < S n), True. *)
    (*   set_eos. *)
    (*   intros. *)
    (*   Subterm.rec_wf_eqns_rel fn 2 m lt. *)





    (*   red. specialize (fn _ f). destruct m as [|m']. *)
    (*   exact I. *)
    (*   apply (fn m'). *)

Equations f (n : nat) : nat by rec n lt :=
  f 0 := 0;
  f (S n) := g n (le_n (S n))

  where g (n' : nat) (H : n' < S n) : nat by rec n' lt :=
  g 0 _ := 0;
  g (S n') H := f n' + g n' (PeanoNat.Nat.lt_le_incl (S n') (S n) H).

Next Obligation. lia. Qed.

Lemma g_unfold_eq : forall n n' p,
    f_obligation_3 n (fun n0 _ => f n0) n' p =
    f_unfold_obligation_1 n n' p.
Proof.
  intros.
  unfold f_obligation_3. Subterm.unfold_recursor. destruct n'; reflexivity.
Qed.
Hint Rewrite g_unfold_eq : f.
Next Obligation.
  unfold f. Subterm.unfold_recursor. destruct n.
  reflexivity.
  simpl.
  rewrite g_unfold_eq. reflexivity.
Defined.

Next Obligation.
  Subterm.rec_wf_rel IH n lt.
  destruct n. simp f.
  simp f.
  assert (forall n' H, f_ind_1 n n' H (f_unfold_obligation_1 n n' H)).
  intros.
  Subterm.rec_wf_rel_aux IH' 2 n' lt ltac:(fun _ => idtac).
  destruct n'. simp f. intros.
  constructor. apply IH. lia.
  auto.
  rewrite g_unfold_eq. apply IH'. lia. constructor.
  apply H.
Defined.

