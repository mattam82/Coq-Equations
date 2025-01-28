From Equations.Prop Require Import Equations.

Inductive t (u : unit) :=
| strange : t tt  -> t u.

Derive NoConfusionHom for t.
Fail Derive Subterm for t.

Inductive t' (u : unit) : Set :=
| strange' : t' tt  -> t' u.

Derive NoConfusionHom for t'.
Derive Subterm for t'.
Definition test := well_founded_t'_subterm.
