(* begin hide *)
Require Import Equations.
(* end hide *)

Fixpoint Below_nat (P : nat -> Type) (n : nat) : Type :=
  match n with
    | 0 => ()
    | S n' => (P n' * Below_nat P n')
  end%type.