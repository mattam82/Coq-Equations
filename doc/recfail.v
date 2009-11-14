(* begin hide *)
Require Import Program Bvector.
(* end hide *)

Program Fixpoint vlast (A : Type) (n : nat) (v : vector A (S n)) : A :=
  match v with
    | Vnil => !
    | Vcons a n v' => 
      match n return A with
        | O => a
        | S n' => vlast A _ v'
      end
      (* match n return vector A n -> option A with *)
      (*   | O => fun v' => Some a *)
      (*   | S n' => fun v' => vlast A (S n') v' *)
      (* end v' *)
  end.

Fixpoint filter {A : Type} (p : A -> bool) (l : list A) {struct l} :=
  match l with
    | nil => nil
    | cons a l => 
      match p a return list A -> list A with
        | true => fun l => a :: filter p l
        | false => fun l => filter p l
      end l
  end.