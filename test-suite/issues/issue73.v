From Coq.Lists Require Import List.
From Equations Require Import Equations.

Equations (struct l1) zip {A} {B} (l1 : list A) (l2 : list B) : list (A*B) :=
zip (cons h1 t1) (cons h2 t2) := (h1,h2) :: zip t1 t2;
zip _ _ := nil.

Equations (struct l2) zip2 {A} {B} (l1 : list A) (l2 : list B) : list (A*B) :=
zip2 (cons h1 t1) (cons h2 t2) := (h1,h2) :: zip2 t1 t2;
zip2 _ _ := nil.

Print zip.
Print zip2.