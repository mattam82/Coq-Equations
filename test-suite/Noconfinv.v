Require Import Equations.

Equations(nocomp) noConfusion_nat_inv (x y : nat) (P : NoConfusion x y) : x = y :=
noConfusion_nat_inv 0 0 _ := eq_refl;
noConfusion_nat_inv (S n) (S m) p := f_equal S p;
noConfusion_nat_inv _ _ p :=! p.

