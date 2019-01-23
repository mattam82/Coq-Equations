


(** In general, one can require more elaborate loop invariants.
    This [fast_length] function computes the length of a list using
    tail recursion: *)

Equations fast_length {A} (l : list A) : nat :=
fast_length l := go 0 l
    where go : nat -> list A -> nat :=
          go n [] := n;
          go n (_ :: l) := go (S n) l.

(** To prove its correctness, we show its pointwise equivalence to
    regular [length l]. *)
Lemma fast_length_length : forall {A} (l : list A), length l = fast_length l.
Proof.
  (** Applying the eliminator is a bit more tricky in this case:
      we must the length
 *)
  apply (fast_length_elim (fun A l res => length l = res)
                          (fun A l res l' lenl => res + length l' = lenl));
    intros l H; simpl in *; intuition auto with arith; lia.
Qed.



Equations list_init {A} (n : nat) (a : A) : list A :=
  list_init 0 _ := [];
  list_init (S n) x := x :: list_init n x.

Require Import NArith.

Equations pos_list_init {A} (n : positive) (a : A) : list A :=
  pos_list_init xH x := [x];
  pos_list_init (n~1) x := let l := pos_list_init n x in x :: l ++ l;
  pos_list_init (n~0) x := let l := pos_list_init n x in x :: l ++ l.
(* Time Definition big_interval := Eval vm_compute in pos_list_init 20000 true. *)

(* Extraction length. *)
(* Extraction fast_length. *)

(* Time Definition slow := Eval vm_compute in length big_interval. *)
(* Time Definition fast := Eval vm_compute in fast_length big_interval. *)
