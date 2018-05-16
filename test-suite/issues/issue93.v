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
Equations sum (fx:foo) : forall (val:foo_type fx), nat := {
  sum (Nat f _) := sum f;
  sum (List ff) := fun val => sum_list ff val }

where sum_list (fs : list foo) : forall (vval: compact_prod (map foo_type fs)), nat := {
  sum_list nil := fun vval => 0;
  (* The "with clause" below is there to work around issue #78 *)
  sum_list (cons hd tl) <= fun val1 => sum_list tl val1 => {
    sum_list (cons hd nil) _ := fun vval => sum hd vval;
    sum_list (cons hd _) sumtl := fun vval => sum hd (fst vval) + sumtl (snd vval)}}.

Next Obligation.
  assert ((forall fx : foo, sum_ind fx (sum fx)) -> (forall fs : list foo, sum_ind_1 fs (sum_list fs))).
  intros.
  induction fs. constructor.
  constructor.
  destruct fs. constructor. constructor.

  assert (forall fx : foo, sum_ind fx (sum fx)).
  fix IH 1. intros fx. destruct fx.
  simpl. rewrite sum_equation_1. constructor. apply IH.
  autorewrite with sum. constructor.
  intuition.
Defined.