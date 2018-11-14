From Equations Require Import Equations DepElimDec HSets.
Unset Equations WithK.
Parameter  I     : Set.
Variables i1 i2 : I.

Inductive D : I -> Set :=
| d1 : D i1
| d2 : D i2.
Derive Signature NoConfusion for D.

(* Equations noConfD {i : I} (d1 d2 : D i) : Prop := *)
(* noConfD {i:=?(i₁)} d1 d1 := True; *)
(* noConfD {i:=?(i₂)} d2 d2 := True; *)
(* noConfD _ _ := False. *)

Inductive P : forall {i}, D i -> Set :=
  p1 : P d1
| p2 : P d2.
Derive Signature NoConfusion for P.

Equations noConfP {i} {d : D i} (p q : P d) : Prop :=
  noConfP p1 p1 := True;
  noConfP p2 p2 := True.

Definition noConfP_eq {i} {d : D i} (v v' : P d) : v = v' -> noConfP v v'.
Proof.
  intros ->. destruct v'; constructor.
Defined.

Definition noConfP_eq_inv {i} {d: D i} (v v' : P d) : noConfP v v' -> v = v'.
Proof.
  funelim (noConfP v v'); simplify *; constructor.
Defined.

Lemma noConfP_eq_eq_inv {i} {d : D i} (v v' : P d) (e : v = v') :
  noConfP_eq_inv _ _ (noConfP_eq _ _ e) = e.
Proof.
  destruct e. destruct v; reflexivity.
Defined.

Lemma noConfP_hom_equiv : forall i (d : D i), NoConfusionPackage (P d).
Proof.
  unshelve econstructor.
  refine noConfP.
  apply noConfP_eq.
  apply noConfP_eq_inv.
  apply noConfP_eq_eq_inv.
Defined.
Existing Instances noConfP_hom_equiv.

Equations Foo (p : P d1) : Set :=
  Foo p1 := nat.
