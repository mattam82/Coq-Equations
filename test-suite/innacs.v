Require Import Equations.
Require Import Vector.
From Equations Require Import Fin.

Fail Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x _ v) ?(fz) := x;
nth (cons _ _ v) (fs f) := nth v f.

(* Intern is correct *)
Fail Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x _ v) ?(fzblxba) := x;
nth (cons _ _ v) (fs f) := nth v f.

(* Typing of innaccessibles is correct *)
Fail Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x _ v) ?(fs x) := x;
nth (cons _ _ v) (fs f) := nth v f.

(* Innaccessibles match only inaccessibles *)
Fail Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x _ v) ?(_) := x;
nth (cons _ _ v) (fs f) := nth v f.

(** Correct inaccessible computation *)
Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x _ v) fz := x;
nth (cons _ ?(n) v) (fs n f) := nth v f.

(** Correct innaccessible computation *)
Fail Equations nth' {A n} (v : vector A n) (f : fin n) : A :=
nth' (cons x _ v) fz := x;
nth' (cons _ n v) (fs n f) := nth' v f.
