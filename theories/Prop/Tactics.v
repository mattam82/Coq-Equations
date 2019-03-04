Require Import Equations.Prop.DepElim Equations.Prop.Subterm.

Ltac Equations.Init.simpl_equations ::= Equations.Prop.DepElim.simpl_equations.
Ltac Equations.Init.depelim H ::= Equations.Prop.DepElim.depelim H.
Ltac Equations.Init.depind H ::= Equations.Prop.DepElim.depind H.
Ltac Equations.Init.noconf H ::= Equations.Prop.DepElim.noconf H.

Ltac Equations.Init.solve_subterm ::= Equations.Prop.Subterm.solve_subterm.
