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

Set Equations Debug.

Equations f (n : nat) : nat by rec n lt :=
  f 0 := 0;
  f (S k) := g k (le_n (S k))

  where g (n' : nat) (H : n' < S k) : nat by rec n' lt :=
  g 0 _ := 0;
  g (S n') H := f n' + g n' _. (* (PeanoNat.Nat.lt_le_incl (S n') (S k) H). *)

Hint Extern 0 (_ < _) => lia : f.
Set Typeclasses Debug.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

(* Equations(noind noeqns) f_funind (n : nat) : f_ind n (f n) by rec n lt := *)
(*   f_funind 0 := _; *)
(*   f_funind (S ) := _ g2 *)

(*   where g2 (n' : nat) (H : n' < S n) : f_ind_1 n n' H (f_unfold_obligation_1 n n' H) by rec n' lt := *)
(*   g2 0 _ := _; *)
(*   g2 (S n') H := _. *)
(* Next Obligation. constructor. Defined. *)
(* Next Obligation. constructor. Defined. *)
(* Next Obligation. rewrite g_unfold_eq. constructor. apply f_funind. lia. apply g2. lia. Defined. *)
(* Next Obligation. autorewrite with f. constructor. apply x. Defined. *)

Next Obligation.
  Subterm.rec_wf_rel IH n lt.
  destruct n. simp f.
  simp f.
  constructor.
  assert (forall n' H, f_ind_1 n n' H (f_unfold_obligation_1 n n' H)).
  intros.
  Subterm.rec_wf_rel_aux IH' 2 n' lt ltac:(fun _ => idtac).
  destruct n'. simp f. intros.
  simp f.
  constructor. apply IH. lia.
  auto. apply H.
Defined.
