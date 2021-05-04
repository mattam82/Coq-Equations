Require Import Equations.Prop.Equations.

Equations Rtuple' (domain : list Type) : Type :=
  Rtuple' nil := unit;
  Rtuple' (cons d nil) := d;
  Rtuple' (cons d (cons d' ds)) := prod (prod (Rtuple' ds) d') d.
