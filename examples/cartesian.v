(* From an example by Olivier Danvy. *)
From Equations Require Import Equations.
From Coq Require Import List.
 
Set Equations Transparent.
Import ListNotations.

Section cart.
   Context {A B : Type}.
   (* No need to have the eliminator generalize over the A, B parameters *)

   Equations cartesian (v1s_given : list A) (v2s_given : list B) : list (A * B) :=
   cartesian v1s_given v2s_given := traverse_1 v1s_given
      where traverse_1 (l : list A) : list (A * B) :=
      { | [] := []
         | (v1 :: v1s') := traverse_2 v2s_given 
            where traverse_2 (l : list B) : list (A * B) by struct l :=
            | [] := traverse_1 v1s'
            | (v2 :: v2s') := (v1, v2) :: traverse_2 v2s' }.
End cart.

Lemma cartesian_spec {A B} (l : list A) (l' : list B) p : 
   In p (cartesian l l') <-> In (fst p) l /\ In (snd p) l'.
Proof.
  revert p. pattern l, l', (cartesian l l').
  (* The bulk of the proof is here: the two invariants needed on the 
     two traversals. *)
  unshelve eapply (cartesian_elim _ 
   (fun _ l' l r => forall p, In p r <-> In (fst p) l /\ In (snd p) l')
   (fun _ v2s_given v1 v1s' v2s' r => forall p, In p r <-> (v1 = fst p /\ In (snd p) v2s') \/
      (In (fst p) v1s' /\ In (snd p) v2s_given))); auto.
  all:cbn; intros; rewrite ?H; intuition auto; cbn.
  - noconf H1. intuition auto.
  - noconf H1. noconf H0. intuition auto.
Qed.

(* Extraction cartesian. *)
(*
(** val cartesian : 'a1 list -> 'a2 list -> ('a1, 'a2) prod list **)

let rec cartesian v1s_given v2s_given =
  match v1s_given with
  | Nil -> Nil
  | Cons (y, l) ->
	let rec traverse_2 = function
    | Nil -> cartesian l v2s_given
    | Cons (y0, l1) -> Cons ((Pair (y, y0)), (traverse_2 l1))
    in traverse_2 v2s_given
*)
Eval compute in cartesian [1; 2] [3; 4].

