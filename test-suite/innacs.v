Require Import Equations.
Require Import Vector.
From Equations Require Import Fin.
Notation vector := Vector.t.

Fail Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x v) ?(fz) := x;
nth (cons _ v) (fs f) := nth v f.

(* Intern is correct *)
Fail Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x v) ?(fzblxba) := x;
nth (cons _ v) (fs f) := nth v f.

(* Typing of innaccessibles is correct *)
Fail Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x v) ?(fs x) := x;
nth (cons _ v) (fs f) := nth v f.

(* Innaccessibles match only inaccessibles *)
Fail Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x v) ?(_) := x;
nth (cons _ v) (fs f) := nth v f.

(** Correct inaccessible computation *)
Equations nth {A n} (v : vector A n) (f : fin n) : A :=
nth (cons x v) fz := x;
nth (cons _ (n:=?(n)) v) (@fs n f) := nth v f.

(** Correct innaccessible computation: variables do
    not need to be innaccessible, they are just determined
    by typing and do not determine the computational
    behavior. They imply no conversion or splitting when
    evaluating nth'.
 *)
Equations nth' {A n} (v : vector A n) (f : fin n) : A :=
nth' (cons x v) fz := x;
nth' (cons _ (n:=n) v) (@fs n f) := nth' v f.
