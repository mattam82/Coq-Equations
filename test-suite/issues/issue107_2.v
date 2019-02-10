From Equations Require Import Equations.
Require Import List.

(* The rest is a nonsensical, just to give a minimalistic reproducible example *)
Inductive Foo :=
| Prod : list Foo -> Foo.
Fixpoint compact_prod (T: list Type): Type :=
  match T with
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t * compact_prod T0)%type
  end.

Equations foo_type (t : Foo) : Type :=
  foo_type (Prod fs) := compact_prod (List.map foo_type fs).

(* Moving val into the return type, rather than having it as an argument might be unnecessary if
   https://github.com/mattam82/Coq-Equations/issues/73 was fixed *)

Equations lookup (t:Foo) (val: foo_type t) (what: list nat) : option nat by struct t := {
  lookup (Prod ss) val nil := None;
  lookup (Prod ss) val (cons hd tl) := lookup_prod ss val hd tl }
                                                                            
    (* match what with nil=> None | cons hd tail => lookup_prod ss val hd tail end} *)

  where lookup_prod (ss: list Foo)
                                  (val : compact_prod (map foo_type ss)) 
                                  (what_hd: nat) (what_tl: list nat) : option nat by struct ss := {
  lookup_prod nil _ _ _ := None;
  lookup_prod (cons shd stl) _ _ what_tl with (fun val what_hd => lookup_prod stl val what_hd what_tl) => {
    lookup_prod (cons shd nil) val 0 what_tl _ := lookup shd val what_tl;
    lookup_prod (cons shd nil) _ _ _ _ := None;
    lookup_prod (cons shd _) val 0 what_tl _ := lookup shd (fst val) what_tl;
    lookup_prod (cons _ _) val (S what_hd) _ what_stl_fun := what_stl_fun (snd val) what_hd}}.
