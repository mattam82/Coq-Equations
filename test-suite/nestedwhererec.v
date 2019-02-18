From Equations Require Import Equations.

(* Bug with eqns *)
(* Nested with equation not properly generated *)

Module FullWf.
Equations test2 (n : nat) (n' : nat) : unit by wf n lt :=
  test2 0 _ := tt;
  test2 (S n) gs := aux gs
  where aux (n' : nat) : unit by wf n' lt :=
   { aux 0 := tt;
     aux (S g) := with_new_candidate (Some g)
                  where with_new_candidate : option nat -> unit :=
                          { | Some newg => tt;
                            | None => aux g } }.
End FullWf.

Module FullStruct.
  Equations test2 (n : nat) (n' : nat) : unit by struct n :=
  test2 0 _ := tt;
  test2 (S n) gs := aux gs
  where aux (n' : nat) : unit by struct n' :=
   { aux 0 := tt;
     aux (S g) := with_new_candidate (Some g)
                  where with_new_candidate : option nat -> unit :=
                          { | Some newg => tt;
                            | None => aux g } }.
End FullStruct.

Module MixedWfStruct.
  Equations test2 (n : nat) (n' : nat) : unit by wf n lt :=
  test2 0 _ := tt;
  test2 (S n) gs := aux gs
  where aux (n' : nat) : unit by struct n' :=
   { aux 0 := tt;
     aux (S g) := with_new_candidate (Some g)
                  where with_new_candidate : option nat -> unit :=
                          { | Some newg => tt;
                            | None => aux g } }.
End MixedWfStruct.
