Require Import Equations.Equations.
Require Import Omega.

Inductive type: Set :=
  | T_bool: type
  | T_prod: type -> type -> type.

Equations transport (t: nat) (T: type): Prop :=
  transport t T by rec 0 lt :=

  transport t T_bool := True;

  transport t (T_prod U V) :=
    transport t U /\
    transport t V.

Next Obligation. Admitted.
Next Obligation. Admitted.

(* obligation generated for transport_ind_fun *)
Next Obligation.
  generalize t.
  induction T; repeat intuition || simp transport in *.
Defined.

