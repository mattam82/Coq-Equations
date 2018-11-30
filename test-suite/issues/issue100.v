From Coq.Lists Require Import List.
From Equations Require Import Equations.

(* This type is from VST: 
 * https://github.com/PrincetonUniversity/VST/blob/v2.1/floyd/compact_prod_sum.v#L13 *)
Fixpoint compact_sum (T: list Type): Type :=
  match T with
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t + compact_sum T0)%type
end.

(* The rest is a nonsensical, just to give a minimalistic reproducible example *)
Inductive Foo :=
| Sum : list Foo -> Foo.

Equations foo_type (t : Foo) : Type :=
  foo_type (Sum u) := compact_sum (List.map foo_type u).

(* Moving val into the return type, rather than having it as an argument might be
 * unnecessary if https://github.com/mattam82/Coq-Equations/issues/73 was fixed *)
Fail Equations (struct f) do_foo (f : Foo) : forall (val : foo_type f), nat := {
  do_foo (Sum u) := fun val => do_foo_sum u val }

  where
  do_foo_sum (fs : list Foo) : forall val : compact_sum (List.map foo_type fs), nat
     by struct fs := {
    do_foo_sum nil := fun val => 0;
    (* Attempting to work around https://github.com/mattam82/Coq-Equations/issues/78 *)
    do_foo_sum (cons hd tl) with (fun val => do_foo_sum tl val) => {
      do_foo_sum (cons var nil) :=
        fun val => do_foo var val;
      do_foo_sum (cons hd tl) do_foo_tl := fun val =>
        match val with
        | inl v => do_foo hd v
        | inr vs => do_foo_tl vs
        end }}.