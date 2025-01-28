Set Warnings "-deprecated-library-file-since-8.20".
From Stdlib Require Import Program Bvector List Relations.
From Equations Require Import Equations Signature.
From Stdlib Require Import Utf8.
Unset Equations WithK.

Inductive Vec (A : Set) : nat -> Set :=
  nil  : Vec A O
| cons : forall {n} (x : A) (xs : Vec A n), Vec A (S n).

Derive NoConfusion for Vec.
Derive NoConfusionHom for Vec.

Transparent NoConfusionHom_Vec.
Definition noConfVec_eq {A n} (v v' : Vec A n) : v = v' -> NoConfusionHom_Vec _ _ v v'.
Proof.
  intros ->. destruct v'; constructor.
Defined.

Definition noConfVec_eq_inv {A n} (v v' : Vec A n) : NoConfusionHom_Vec _ _ v v' -> v = v'.
Proof.
  funelim (NoConfusionHom_Vec _ _ v v'); simplify *; constructor.
Defined.

Lemma noConfVec_eq_eq_inv {A n} (v v' : Vec A n) (e : v = v') :
  noConfVec_eq_inv _ _ (noConfVec_eq _ _ e) = e.
Proof.
  destruct e. destruct v; reflexivity.
Defined.

Lemma noConfVec_eq_inv_eq {A n} (v v' : Vec A n) (e : NoConfusionHom_Vec _ _ v v') :
  noConfVec_eq _ _ (noConfVec_eq_inv _ _ e) = e.
Proof.
  destruct v; revert e. depelim v'. simplify *; reflexivity.
  depelim v'. simplify *. simpl. reflexivity.
Defined.
