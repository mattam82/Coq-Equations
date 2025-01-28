From Equations.Prop Require Import Equations.
(* Removing this line makes Derive Subterm go through without troubles *)
Set Universe Polymorphism.

Inductive t : Type -> Type :=
| Build_t : forall A, t A -> t A.

Derive Signature for t.
Derive NoConfusionHom for t.
Derive Subterm for t.

Definition test := well_founded_t_subterm.