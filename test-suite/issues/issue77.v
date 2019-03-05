From Equations Require Import Equations.
Require Vector.
Notation vector := Vector.t.
Derive Signature for Vector.t.
Fail Equations test {X n} (v : vector X (S n)) : vector X 0 :=
    {
      test Vector.cons := Vector.nil
    }.

Fail  Equations test1 {X n} (v : vector X (S n)) : vector X n :=
    {
      test1 (Vector.cons a) := a
    }.

  Equations test2 {X n} (v : vector X (S n)) : vector X n :=
    {
      test2 (Vector.cons x a) := a
    }.

Fail  Equations test3 {X n} (v : vector X (S n)) : vector X n :=
    {
      test3 (Vector.cons X n a) := a
    }.

Equations test4 {X n} (v : vector X (S n)) : vector X n :=
    {
      test4 (@Vector.cons _ x n a) := a
    }.