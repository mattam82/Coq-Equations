Require Import HoTT.Basics.Overture.

Class WellFounded (A : Type) (R : relation A) :=
  wellfounded : well_founded R.