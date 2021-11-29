From Equations Require Import Equations.

Universe u.
(* Same observed behaviour with and without universe polymorphism set *)
Set Universe Polymorphism.

Equations foo@{} (u : unit) : Type@{u} :=
  | tt => unit.
(* The command has indeed failed with message: *)
(* Universe {debug.204} is unbound. *)
