Require Import Equations.Equations.

Equations Rtuple'' (domain : list Type) : Type :=
  Rtuple'' nil => unit;
  Rtuple'' (cons d ds) with ds => {
    | nil => d ;
    | _ => prod (Rtuple'' ds) d }.
