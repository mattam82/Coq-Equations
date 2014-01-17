Require Import Equations.
Require Import Relations.

Definition gcd_order (p : nat * nat) : nat := let (x,y) := p in x+y.


Definition measure {A B} (f : A -> B) (R : relation B) : relation A :=
  fun x y => R (f x) (f y).

Definition gcd_rel : relation (nat * nat) :=
  MR lt gcd_order.

Instance gt_bound_wf : WellFounded gcd_rel.
Proof. red. apply measure_wf. apply Wf_nat.lt_wf. Defined.

Require Import Omega.

Hint Extern 5 => 
  unfold gcd_rel, gcd_order, MR; omega : Below.

Equations gcd (p : nat * nat) : nat :=
gcd p by rec p gcd_rel :=
gcd (pair 0 _) := 0 ;
gcd (pair _ 0) := 0 ;
gcd (pair x y) with gt_eq_gt_dec x y := {
  | inleft (left ygtx) := gcd (x, y - x) ;
  | inleft (right refl) := x ;
  | inright xgty := gcd (x - y, y) }.

Require Import Utf8.
Lemma FixF_eq A (R : A -> A -> Prop) P (F : (∀ x : A, (∀ y : A, R y x → P y) → P x)) t step step' : 
  @Fix_F A R P F t (Acc_intro t step) =
  F t (fun y rel => @Fix_F A R P F y (step' y rel)).
Proof. simpl. apply f_equal. extensionality y; extensionality h. 
       apply f_equal. apply proof_irrelevance.
Defined.

Lemma FixWf_eq A (R : A -> A -> Prop) wfr P (F : (∀ x : A, (∀ y : A, R y x → P y) → P x)) t : 
  @FixWf A R wfr P F t =
  F t (fun y rel => @FixWf A R wfr P F y).
Proof. unfold FixWf, Fix. unfold wellfounded.        
       destruct (wfr t). apply FixF_eq.
Defined.
Obligation Tactic := idtac.
Next Obligation. (*MS: Bug *) intros. admit. Defined.

(*   intros. *)
(*   rec_wf_rel p IH gcd_rel. *)
(*   setoid_rewrite FixWf_eq.  *)
(*   change ( gcd_obligation_8 x *)
(*      (λ (y : nat * nat) (_ : gcd_rel y x), gcd y) = gcd_unfold x). *)
(*   Opaque gcd. *)
(*   depelim x. depelim n. reflexivity. *)
(*   depelim n0. reflexivity. *)
(*   simpl. simpl_equations.  *)
(*   simpl. *)
(*   destruct_call gt_eq_gt_dec. destruct s. *)
(*   simpl. simpl. unfold gcd_comp_proj. unfold gcd_obligation_1. *)

(*   autounfold with gcd. specialize (IH (S n, n - n)). *)
(*   symmetry. rewrite IH. Focus 2. do 3 red; unfold gcd_order. omega.  *)
(*   unfold gcd_comp_proj. *)
(*   Transparent gcd gcd_unfold. apply IH. *)
(* Solve Obligations.  *)
Next Obligation. 
  intros. 
  eapply (@gcd_ind_mut P P0); eauto. 
  apply gcd_ind_fun.
Defined.

Lemma gcd_ref x : gcd (x,x) = x.
Proof.
  funelim (gcd (x, x)); now (try (exfalso; omega)). 
Qed.

Module Function.    
Require Import Recdef.
Function gcd (p : nat * nat) {measure gcd_order p} : nat :=
 match p with
   | (0,_) => 0
   | (_,0) => 0
   | (x,y) => match gt_eq_gt_dec x y with
                | inleft (left _) => gcd (x, y-x)
                | inleft (right _) => x
                | inright xgty => gcd (x-y, y)
              end
 end.
- unfold gcd_order ; intros ; omega.
- unfold gcd_order ; intros ; omega.
Defined.

Lemma gcd_ref x : gcd (x,x) = x.
Proof.
  functional induction (gcd (x, x)). Abort.

Lemma gcd_ref x : gcd (x,x) = x.
Proof.
  generalize (@eq_refl _ (x, x)).
  generalize (x, x) at 1 3. intros p; revert x.
  functional induction (gcd p); intros; noconf H.
  red in _x. omega. omega.
Qed.
End Function.