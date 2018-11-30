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

(* The rest is a nonsensical, just to give a minimalistic reproducible example *)
Inductive foo :=
| Sum : (foo * list foo) -> foo.

Equations foo_type (t : foo) : Type :=
  foo_type (Sum u) :=
    (foo_type (fst u))
    * (compact_sum (List.map foo_type (snd u))).

(* Moving val into the return type, rather than having it as an argument
   might be unnecessary if
   https://github.com/mattam82/Coq-Equations/issues/73 was fixed *)
Equations (struct f) do_foo (f : foo) : forall (val : foo_type f), nat := {
  do_foo (Sum s) := fun val =>
    (do_foo (fst s) (fst val)) + (do_sum (snd s) (snd val)) }

  where
    do_sum (fs : list foo) :
      forall val : compact_sum (List.map foo_type fs), nat
      by struct fs := {
    do_sum nil := fun val => 0;
    (* Attempting to work around https://github.com/mattam82/Coq-Equations/issues/78 *)
    do_sum (cons hd tl) with (fun val => do_sum tl val) => {
      do_sum (cons var nil) _ :=
        fun val => do_foo var val;
      do_sum (cons hd tl) do_foo_tl := fun val =>
        match val with
        | inl vh => do_foo hd vh
        | inr vstl => do_foo_tl vstl
        end }}.