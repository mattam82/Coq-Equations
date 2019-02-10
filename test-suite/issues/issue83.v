From Equations Require Import Equations.

Section CookingKillsOpaquenessForReduction.
Equations id {A} (x : A) : A :=
id x := x.
(* id is basically transparent but considered opaque for reduction *)
End CookingKillsOpaquenessForReduction.

Definition foo : @id = fun A x => x.
Proof. Fail unfold id. reflexivity. Qed.
