From Equations Require Import Equations Utf8.
Add Rec LoadPath ".." as Top.
From Stdlib Require Import issue7.


Extraction Inline apply_noConfusion.
Extraction Inline simplify_ind_pack.
Extraction Inline simplify_ind_pack_inv.
Extraction Inline eq_simplification_sigma1_dep_dep.

Extraction Inline Equations.EqDec.K_dec.
Extraction myComp.