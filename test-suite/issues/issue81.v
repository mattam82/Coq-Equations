From Stdlib Require Import Lists.List.
Import ListNotations.
From Equations.Prop Require Import Equations.

Equations app {A} (l l' : list A) : list A :=
app [] l' := l' ;                                  (* <- here notations work *)
app (a :: l) l' := a :: (app l l').