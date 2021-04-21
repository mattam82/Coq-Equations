From Equations.HoTT Require Import Loader.
From HoTT Require Import Basics.

Equations foo {A} (x y : A) (e : x = y) : e = e :=
foo _ _ idpath := idpath.
