From Equations Require Import Equations.
Require Import Program.

Equations foo (f: option (nat -> nat)) (l: list nat) : list nat :=
  foo None _ := [];
  foo (Some f) nil := nil;
  foo (Some f) (cons hd tl) := cons (f hd) (foo (Some f) tl).
