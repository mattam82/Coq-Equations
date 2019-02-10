From Equations Require Import Equations.
Require Import List.
(* This type is from VST: 
 * https://github.com/PrincetonUniversity/VST/blob/v2.1/floyd/compact_prod_sum.v#L13 *)
Fixpoint compact_sum (T: list Type): Type :=
  match T with
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t + compact_sum T0)%type
end.

(* The rest is a nonsensical, just to give a reproducible example *)
Inductive foo :=
| Sum : (foo * list foo) -> foo.

Equations foo_type (t : foo) : Type :=
  foo_type (Sum u) :=
    (foo_type (fst u))
    * (compact_sum (List.map foo_type (snd u))).

Equations do_foo (f : foo) : forall (val : foo_type f), nat by struct f := {
  do_foo (Sum (pair s1 s2)) := fun val =>
    (do_foo s1 (fst val)) + (do_sum s1 (fst val) s2 (snd val)) }

where do_sum (f : foo) (otherval : foo_type f) (fs : list foo) :
        forall val : compact_sum (List.map foo_type fs), nat
        by struct fs := {
    do_sum _ _ nil := fun val => 0;
    do_sum f otherval (cons hd tl) with (fun val => do_sum f otherval tl val) => {
      do_sum _ _ (cons var nil) _ :=
        fun val => do_foo var val;
      do_sum _ _ (cons hd tl) do_foo_tl := fun val =>
        match val with
        | inl vh => do_foo hd vh
        | inr vstl => do_foo_tl vstl
        end }}.