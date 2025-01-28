From Equations.Prop Require Import Equations.


Equations Rtuple'' (domain : list Type) : Type :=
  Rtuple'' nil => unit;
  Rtuple'' (cons d ds) with ds => {
    | nil => d ;
    | _ => prod (Rtuple'' ds) d }.
