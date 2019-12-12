From Coq Require Import Arith Lia.
From Equations Require Import Equations.

Equations? Div (x y : nat) : nat by wf x lt :=
 { Div x 0 := 0 ;
   Div x y with le_lt_dec y x :=
     { | left _  := 1 + Div (x - y) y  ;
       | right _ :=  0 } } .
Proof.
 lia.
Qed.

Equations? Mod (x y : nat) : nat by wf x lt :=
 { Mod x 0 := 0 ;
   Mod x y with le_lt_dec y x :=
     { | left _  := Mod (x - y) y  ;
       | right _ := x } } .
Proof.
 lia.
Qed.

Fact Div_Mod x y :
 x = S y * Div x (S y) + Mod x (S y).
Proof.
 induction x as [x IH] using lt_wf_ind.
 simp Div Mod.
 Opaque mult.
 destruct (le_lt_dec _ _) as [H|H]; cbn.
 - assert (x - S y < x) as IH1%IH by lia.
   lia.
 - lia.
Qed.