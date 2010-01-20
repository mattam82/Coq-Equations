(* begin hide *)
Require Import Equations.
Inductive I : Type := icstr : I.
(** A [NoConfusionPackage] instance on a type [A] defines a [NoConfusion] 
   predicate taking a type and two arguments of type [A] to produce
   a new type. One can make an instance of this predicate using 
   the [noConfusion] method which takes an equality between the two arguments
   as an additional argument. Instances of the [NoConfusionPackage] class 
   can be derived automatically using the [Derive NoConfusion for ind] command.
   For example, the [NoConfusion] predicate for [nat] will be:
   *)
(* end hide *)

Equations NoConfusion_nat (P : Type) (x y : nat) : Type :=
NoConfusion_nat P O O := P -> P ;
NoConfusion_nat P (S n) (S m) := (n = m -> P) -> P ;
NoConfusion_nat P _ _ := P.

(** Suppose we have a goal [P] and a proof of [NoConfusion_nat P x y] for 
   [x] and [y] in constructor form supposing [x = y].
   The proof will always unfold to an implication ending in [P], so we can apply 
   it to our goal. Depending on
   the form of [x] and [y], we will make the goal progress in different ways.
   If [x] and [y] are both [O], then we are left to prove the same goal unchanged,
   the equality is trivial ([P -> P]).
   If [x] and [y] are both of the form [S _] then we are left with a proof of 
   the goal under the additional hypothesis that the arguments are equal 
   [((n = m -> P) -> P)]. Finally, in all other cases, the goal is directly
   discharged, as we have a witness of [P] by contradiction of the equality
   of [n] and [m].

   We define a new type class to register [NoConfusion] proofs for each type.
   Instances can be automatically derived for any computational inductive family.
   We can then build a generic tactic to simplify any equality hypothesis 
   on a registed type using this construction, 
   which subsumes the [discriminate] and [injection] tactics. *)