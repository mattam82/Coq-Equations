From Equations Require Import Equations DepElimDec HSets.
Unset Equations OCaml Splitting.
Set Universe Polymorphism.

Equations Logic Type Id Id_rect Empty unit tt Id_rect_r Id_rect_dep_r.

Set Warnings "-notation-overridden".
Import IdNotations.
Set Warnings "+notation-overridden".

Derive Signature for Id.

Check (_ : HSet nat).

Set Printing Universes.
Equations test_k (x : nat) (r : x = x) : r = r :=
test_k x id_refl := id_refl.

Equations foo (A : Type) (x : A) : A :=
foo A x := x.
