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
Inductive Foo :=
| Foo1 : list Foo -> Foo
| Foo2 : list Foo -> Foo.

Equations foo_type (t : Foo) : Type :=
  foo_type (Foo1 fs) := compact_prod (List.map foo_type fs);
  foo_type (Foo2 fs) := compact_prod (List.map foo_type fs).
Transparent foo_type.

(* Moving val nato the return type, rather than having it as an argument might be unnecessary if
   https://github.com/mattam82/Coq-Equations/issues/73 was fixed *)
(* Set Equations Debug. *)

Equations (struct t) do_foo (t : Foo) : forall (val : foo_type t), nat := {
  do_foo (Foo1 fs) := fun val => do_foo1 fs val;
  do_foo (Foo2 fs) := fun val => do_foo2 fs val }

where do_foo1 (fs:list Foo) : forall (val : compact_prod (map foo_type fs)), nat
 by struct fs := {
    do_foo1 nil := fun val => 0;
    (* do_foo1 (cons hd nil) := fun val => do_foo hd val; *)
    (* do_foo1 (cons hd tl) := fun val => 0 } *)
    (* Attempting to work around https://github.com/mattam82/Coq-Equations/issues/78 *)
    do_foo1 (cons hd tl) with (fun val => do_foo1 tl val) => {
      do_foo1 (cons hd nil) _ := fun val => do_foo hd val;
      do_foo1 (cons hd _) do_foo_tl := fun val =>
        (do_foo hd (fst val)) + (do_foo_tl (snd val))}}

where do_foo2 (fs : list Foo) : forall val : compact_prod (List.map foo_type fs), nat
 by struct fs := {
    do_foo2 nil := fun val => 0;
    do_foo2 (cons var nil) :=
      fun val => do_foo var val;
    do_foo2 _ := fun val => 0 }.
