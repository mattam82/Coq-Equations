Require Import Equations.Type.DepElim Equations.Type.WellFounded.

Ltac Equations.Init.simpl_equations ::= Equations.Type.DepElim.simpl_equations.

Ltac Equations.Init.depelim H ::= Equations.Type.DepElim.depelim H.
Ltac Equations.Init.depind H ::= Equations.Type.DepElim.depind H.

Ltac Equations.Init.noconf H ::= Equations.Type.DepElim.noconf H.

Ltac Equations.Init.solve_subterm ::= Equations.Type.WellFounded.solve_subterm.
