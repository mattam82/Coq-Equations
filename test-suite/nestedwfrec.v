From Equations Require Import Equations.
Require Import Lia.

Equations? f (n : nat) : nat by rec n lt :=
  f 0 := 0;
  f (S k) := g k (le_n (S k))

  where g (n' : nat) (H : n' < S k) : nat by rec n' lt :=
  g 0 _ := 1;
  g (S n') H := f n' + g n' (PeanoNat.Nat.lt_le_incl (S n') (S k) H).

Hint Extern 0 (_ < _) => lia : f.
Proof. lia. Defined.

Goal f 2 = 1.
Proof. reflexivity. Defined.

Definition f_e := f_elim.