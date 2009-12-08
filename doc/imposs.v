Class ImpossibleCall {A : Type} (a : A) : Type :=
  is_impossible_call : False.

(** We have a trivial elimination operator for impossible calls.
   This can be used to eliminate an application [a] appearing anywhere
   directly. *)

Definition elim_impossible_call {A} (a : A)
  {imp : ImpossibleCall a} (P : A -> Type) : P a :=
  match is_impossible_call with end.
