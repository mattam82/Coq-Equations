From Equations Require Import Equations.
Require Import Examples.Fin.
(* Add LoadPath "examples". *)
Require Import Examples.ordinals.
Add Search Blacklist "_obligation_".
Require Import Equations.Prop.TransparentEquations.

Inductive ho : Set :=
| base : nat -> ho
| lim : forall n : nat, (fin n -> ho) -> ho.
Derive NoConfusion for ho.

Equations lift_fin {n : nat} (f : fin n) : fin (S n) := 
lift_fin fz := fz;
lift_fin (fs f) := fs (lift_fin f).

Equations maxf (n : nat) (f : fin n -> nat) : nat :=
maxf 0 f := 0;
maxf (S n) f := max (f (gof n)) (maxf n (fun y : fin n => f (lift_fin y))).

Equations horec_struct (x : ho) : nat :=
horec_struct (base n) := n;
horec_struct (lim k f) := maxf k (fun x => horec_struct (f x)).

Derive Subterm for ho.

Equations horec (x : ho) : nat by wf x ho_subterm :=
horec (base n) := n;
horec (lim k f) := maxf k (fun x => horec (f x)).
Transparent horec maxf lift_fin horec_struct.

Definition horec_test : horec (lim 7 (fun fs => base (fog fs))) = 6 := eq_refl.
