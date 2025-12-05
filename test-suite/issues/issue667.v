From Equations Require Import Equations.
Variant foo := Foo (x : bool).
Equations bar : foo -> bool -> bool :=
  bar (Foo _) x := x .
Check (eq_refl : bar (Foo true) false = false).
