From Coq.Lists Require Import List.
From Equations Require Import Equations.

(* This type is from VST: https://github.com/PrincetonUniversity/VST/blob/v2.1/floyd/compact_prod_sum.v#L6 *)
Fixpoint compact_prod (T: list Type): Type :=
  match T with
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t * compact_prod T0)%type
  end.

Record rec1 {MT : Type} :=
  { field1 : MT }.

Record rec2 {MT : Type} :=
  { field2 : list (@rec1 MT) }.

Inductive MT :=
| Prod : @rec2 MT -> MT.

(* Axiom cheat : forall{A}, A. *)
(* Equations foo_type (t : MT) : Type := *)
(* { foo_type (Prod u) := *)
(*     (compact_prod (List.map (fun t => foo_type (field1 t)) (field2 u))) }. *)
(* Next Obligation. *)
(*   revert t. fix IH 1. destruct t. *)
(*   constructor. apply cheat. Defined. *)
  
  
Equations foo_type (t : MT) : Type :=
{ foo_type (Prod u) :=
    (compact_prod (foo_type_l (field2 u))) }
where foo_type_l (l : list (@rec1 MT)) : list Type := {
  foo_type_l nil := nil;        
  foo_type_l (cons hd tl) := foo_type (field1 hd) :: foo_type_l tl }
  .

Next Obligation.
  revert t. fix IH 1. destruct t.
  constructor.
  intros. apply IH. Defined.