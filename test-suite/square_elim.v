(** Taken from Agda issue 3034:
    https://github.com/agda/agda/issues/3034 *)

Inductive Square {A : Type} : forall w x y z : A, w = x -> x = y -> y = z -> z = w -> Type :=
  square w : Square w w w w eq_refl eq_refl eq_refl eq_refl.

Equations J2 {A : Type} (x : A) (p : x = x) (s : Square x x x x eq_refl eq_refl p eq_refl) : Set :=
J2 _ _ (square x) := nat.
