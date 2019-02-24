Require Import Program Bvector List.
Require Import Relations.
From Equations Require Import Equations DepElimDec.

Module TestF.

Equations? f (n : nat) : nat :=
f 0 := 42 ;
f (S m) with f m :=
{
f (S m) IH := _
}.
Proof. exact 0. Defined.
Write State bisect.
End TestF.