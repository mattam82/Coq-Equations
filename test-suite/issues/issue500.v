From Equations.Prop Require Import Equations.

Section box.
  Universe u.
  Context {A : Type@{u}} `(EA : EqDec A).

  Inductive box : Type@{u} :=
  | pack : A -> box.
  Derive NoConfusion for box.

  Derive EqDec for box.
  Inspect 5.
End box.

Definition test := @box_eqdec nat _.

Section LIST.

Variable (A:Type) (eq_dec : EqDec A).

Inductive list : Type :=
| nil
| cons : A -> list -> list.

Derive NoConfusion EqDec for list.

End LIST.

