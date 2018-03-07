Require Import HoTT.Basics.Overture.
Require Import Coq.Init.Wf.

(** A class for well foundedness proofs.
   Instances can be derived automatically using [Derive Subterm for ind]. *)

Class WellFounded {A : Type} (R : relation A) :=
  wellfounded : well_founded R.
