Require Import Equations.Equations.

Equations Rtuple'' (domain : list Type) : Type :=
  Rtuple'' nil := unit;
  Rtuple'' (cons d ds) <= ds => {
    | nil => d ;
    | _ => prod (Rtuple'' ds) d }.

Next Obligation.
  revert domain. fix 1.
  destruct domain. constructor.
  autorewrite with Rtuple''.
  constructor.
  set(refine:=domain) at 2 4; clearbody refine. destruct refine.
  simpl. constructor. simpl. constructor.
  apply Rtuple''_ind_fun_obligation.
Defined.
