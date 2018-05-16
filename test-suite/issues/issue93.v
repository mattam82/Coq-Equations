From Coq.Lists Require Import List.
From Equations Require Import Equations.

(* This type is from VST: https://github.com/PrincetonUniversity/VST/blob/v2.1/floyd/compact_prod_sum.v#L6 *)
Fixpoint compact_prod (T: list Type): Type :=
  match T with
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t * compact_prod T0)%type
  end.

(* The rest is a nonsensical, just to give a minimalistic reproducible example *)
Inductive foo :=
| Nat : foo -> nat -> foo
| List : list foo -> foo.

Equations foo_type (ft:foo) : Type :=
  foo_type (Nat f _) := foo_type f;
  foo_type (List fs) := compact_prod (List.map foo_type fs).
Transparent foo_type.

(* val was moved into the result type, rather than being an argument, to work around issues #73 and #85 *)
Set Equations Debug.
Equations sum (fx:foo) : forall (val:foo_type fx), nat := {
  sum (Nat f _) := fun val => sum f val;
  sum (List ff) := fun val => sum_list ff val }

where(struct fs) sum_list (fs : list foo) (vval: compact_prod (map foo_type fs)) : nat := {
  sum_list nil vval := 0;
  (* The "with clause" below is there to work around issue #78 *)
  sum_list (cons hd tl) val1 <= fun val => sum_list tl val => {
    sum_list (cons hd nil) val1 _ := sum hd val1;
    sum_list (cons hd _) val1 sumtl := sum hd (fst val1) + sumtl (snd val1)}}.

(* Next Obligation. *)
(*   assert ((forall fx : foo, sum_ind fx (sum fx)) -> (forall fs vval, sum_ind_1 fs vval (sum_list fs vval))). *)
(*   intros H. *)
(*   fix Hsl 1. *)
(*   intros. *)
(*   destruct fs; constructor. *)
(*   intros. *)
(*   apply Hsl. *)
(*   simp sum. *)
(*   destruct fs. *)
(*   econstructor. *)
(*   apply H. *)
(*   econstructor. *)
(*   apply H. *)

(*   assert (forall fx : foo, sum_ind fx (sum fx)). *)
(*   fix IH 1. specialize (H IH). intros fx. destruct fx. *)
(*   simpl. rewrite sum_equation_1. constructor. simpl. intros. apply IH. *)
(*   autorewrite with sum. constructor. *)
(*   simpl. intros. apply H. *)

(*   intuition. *)
(* Defined. *)