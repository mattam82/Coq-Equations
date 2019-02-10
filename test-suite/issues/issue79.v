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
| List : foo.

Definition foo_type (f:foo) : Type :=
  match f with
  | Nat => nat
  | List => list unit
  end.

Equations num (f:foo) (val:foo_type f) : nat :=
  num Nat val := val;
  num List val := length val.

Equations sum (fs : list foo) (val: compact_prod (map foo_type fs)) : nat by struct fs := {
  sum nil _ := 0;
  sum (cons f tl) val := sum_aux f tl val }

where sum_aux (f:foo) (fs : list foo) (val: compact_prod (map foo_type (f::fs))) : nat by struct fs := {
  sum_aux f nil val := num f val;
  sum_aux f (cons hd tl) val := num f (fst val) + sum_aux hd tl (snd val)}.
