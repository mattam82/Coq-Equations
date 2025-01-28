From Stdlib Require Import Vector.
From Equations.Prop Require Import Equations.
Arguments Vector.nil {A}.
Arguments Vector.cons {A} _ {n}.

Equations silly_replicate {A} (n : nat) (x : A) : Vector.t A n :=
silly_replicate O _ := nil;
silly_replicate (S n') x with (silly_replicate n' x) := {
  | nil => cons x nil;
  | cons h tl => cons x (cons h tl)
}.