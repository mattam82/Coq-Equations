From Equations.Prop Require Import Equations.

Require Import List.
Import ListNotations.

Record decl := { na : nat; body : option nat }.

Derive NoConfusion for decl.

Definition ctx := list decl.

Check (_ : NoConfusionPackage ctx).

Inductive P : ctx -> Type :=
| P_nil : P nil
| P_bod n k l : P l -> P ({| na := n; body := Some k |} :: l)
| P_nobod n l : P l -> P ({| na := n; body := None |} :: l).
Derive Signature for P.

Definition vass na := {| na := na; body := None |}.

Goal forall n l, P (vass n :: l) -> P l.
Proof.
  intros n l.
  intros p.
  depelim p. exact p.
Defined.