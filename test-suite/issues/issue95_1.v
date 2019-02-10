Require Import Equations.Equations.
Require Import Omega.

Inductive type: Set :=
  | T_bool: type
  | T_prod: type -> type -> type.

Axiom wf : 0 < 0.

Equations? transport (t: nat) (T: type): Prop
  by wf 0 lt :=

  transport t T_bool := True;

  transport t (T_prod U V) :=
    transport t U /\
    transport t V.
Proof. all: apply wf. Defined.
