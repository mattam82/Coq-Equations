From Equations.Prop Require Import Equations.

#[warnings="-warn-library-file-stdlib-vector"]
From Stdlib Require Import Vector.
From Equations.TestSuite Require Import fin.
Notation vector := Vector.t.
Arguments Vector.nil {A}.
Arguments Vector.cons {A} _ {n}.
Notation vnil := Vector.nil.
Notation vcons := Vector.cons.

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
