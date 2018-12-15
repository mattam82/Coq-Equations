Require Import Equations.Equations.
Require Import Lia.

Set Equations Debug.

Equations f (n : nat) : nat by rec n lt :=
  f 0 := 0;
  f (S k) := g k (le_n (S k))

  where g (n' : nat) (H : n' < S k) : nat by rec n' lt :=
  g 0 _ := 1;
  g (S n') H := f n' + g n' (PeanoNat.Nat.lt_le_incl (S n') (S k) H).

Hint Extern 0 (_ < _) => lia : f.
Next Obligation. lia. Qed.

Goal f 2 = 1.
Proof. reflexivity. Defined.

Check f_elim.