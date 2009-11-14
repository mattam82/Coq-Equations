(* begin hide *)
Require Import Equations.
(* end hide *)
Class NoConfusionPackage (A : Type) := {
  NoConfusion : Type -> A -> A -> Type;
  noConfusion : forall P a b, a = b -> NoConfusion P a b }.

(** A [NoConfusionPackage] instance on a type [A] defines a [NoConfusion] 
   predicate taking a type and two arguments of type [A] to produce
   a new type. One can make an instance of this predicate using 
   the [noConfusion] method which takes an equality between the two arguments
   as an additional argument. Instances of the [NoConfusionPackage] class 
   can be derived automatically using the [Derive NoConfusion for ind] command.
   For example, the [NoConfusion] predicate for [nat] will be:
   *)

Equations NoConfusion_nat (P : Type) (x y : nat) : Type :=
NoConfusion_nat P O O := P -> P ;
NoConfusion_nat P (S n) (S m) := (n = m -> P) -> P ;
NoConfusion_nat P _ _ := P.

(** Suppose we have a goal [P] and a proof of [NoConfusion_nat P x y] for 
   [x] and [y] in constructor form. This proof will always unfold to an
   implication ending in [P], so we can apply it to our goal. Depending on
   the form of [x] and [y], we will make the goal progress in different ways.
   If [x] and [y] are both [O], then we are left to prove the same goal unchanged,
   the equality is trivial ([P -> P]).
   If [x] and [y] are both of the form [S _] then we are left with a proof of 
   goal under the additional hypothesis that the arguments are equal 
   [((n = m -> P) -> P)]. Finally, in all other cases, the goal is directly
   discharged, as we have a witness of [P].

   We can build a tactic to simplify any hypothesis using this construction,
   which subsumes the [discriminate] and [injection] tactics.
*) 
  
