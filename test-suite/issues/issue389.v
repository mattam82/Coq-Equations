From Equations Require Import HoTT.All.
Set Universe Polymorphism.
Inductive A : Type :=
| foo : A
| bar : A -> A -> A.

Derive NoConfusion for A.
Derive EqDec for A.
