From Equations Require Import Equations DepElimDec HSets.
Unset Equations OCaml Splitting.
Set Universe Polymorphism.

Equations Logic Type Id Id_rect Empty unit tt.

Import IdNotations.

Derive Signature for Id.

Check (_ : HSet nat).

Set Printing Universes.
Equations test_k (x : nat) (r : x = x) : r = r :=
test_k x id_refl := id_refl.
Print Assumptions test_k.

(* Fail *)
(* Equations fail_k (A : Type) (x : A) (r : x = x) : r = r :=  *)
(* fail_k A x id_refl := id_refl. *)
