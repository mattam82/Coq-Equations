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
| Nat : foo
| List : list foo -> foo.

Fixpoint foo_type (f:foo) : Type :=
  match f with
  | Nat => nat
  | List fs => compact_prod (map foo_type fs)
  end.

Equations num (f:foo) : forall (val:foo_type f), nat := {
  num Nat := fun val => val;
  num (List nil) := fun val => 0;
  num (List (cons hd tl)) := fun val => sum hd (num hd) tl val }
where sum (f:foo) (numf: (foo_type f -> nat)) (fs : list foo) (val: compact_prod (map foo_type (f::fs))) : nat
  by struct fs := {
  sum f numf nil val := numf val;
  sum f numf (cons hd tl) val := numf (fst val) + sum hd (num hd) tl (snd val)}.