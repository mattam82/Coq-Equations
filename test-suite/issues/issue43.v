Require Import Program List.
Require Vector. Import Vector.VectorNotations.
Require Import Relations.
From Equations Require Import Equations DepElimDec.

Equations silly {A} (l : list A) : list A :=
silly l by wf ((fix Ffix (x : list A) : nat :=
         match x with
         | []%list => 0
         | (_ :: x1)%list => S (Ffix x1)
         end) l) lt :=
silly nil := nil;
silly (cons a l) := a :: silly l.

Equations silly' {A} (l : list A) : list A :=
silly' l by wf (length l) lt :=
silly' nil := nil;
silly' (cons a l) := a :: silly' l.

Check silly'_elim.
