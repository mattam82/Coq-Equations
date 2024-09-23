From Stdlib.Lists Require Import List.
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
| List : list foo -> foo.

Fixpoint foo_type (f:foo) : Type :=
  match f with
  | List fs => compact_prod (map foo_type fs)
  end.

Equations do_foo (t : foo) : option (foo_type t) := {
  do_foo (List ss) := do_list ss}

  where do_list (ts:list foo) : option (compact_prod (map foo_type ts)) := {
    do_list nil := Some tt;
    (* Attempting to work around https://github.com/mattam82/Coq-Equations/issues/78 and 108*)
    do_list (cons t ts) with (fun val1 =>
        match val1, do_list ts with Some val1, Some vals => Some (val1, vals) | _, _ => None end) => {
      do_list (cons t nil) _ := do_foo t;
      do_list (cons t ts) do_tl :=
        do_tl (do_foo t)}}.