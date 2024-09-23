Require Import Stdlib.Lists.List.
Import ListNotations.
From Equations Require Import Equations.

Equations app {A} (l l' : list A) : list A :=
app [] l' := l' ;                                  (* <- here notations work *)
app (a :: l) l' := a :: (app l l').