(** * The Bove-Cappretta method

   This method involves building the graph and/or domain of a recursive
   definition and to define it by recursion + inversion on that graph,
   but not direct pattern matching. We show a difficult example
   involving nested recursive calls. *)

From Equations Require Import Equations.
Require Import Arith Lia Relations Utf8.
Import Sigma_Notations.

(** The graph of the [f91] function. *)

Inductive f91_graph : nat -> nat -> Prop :=
| f91_gt n : n > 100 -> f91_graph n (n - 10)
| f91_le n nest res :
    n <= 100 -> f91_graph (n + 11) nest ->
    f91_graph nest res ->
    f91_graph n res.
Derive Signature for f91_graph.

(** It is easy to derive the spec of [f91] from it, by induction. *)
Lemma f91_spec n m : f91_graph n m -> if le_lt_dec n 100 then m = 91 else m = n - 10.
Proof.
  induction 1; repeat destruct le_lt_dec; try lia; auto.
Qed.

(* Do not [simpl] the (101 - n) call *)
Arguments minus : simpl never.

(** One can construct the graph using a (relatively) complex termination argument.
    Note that it is required to know that the result is in the graph to show
    termination at the second, nested recursive call to [f91_exists]. *)

Equations? f91_exists n : Σ r, f91_graph n r by wf (101 - n) lt :=
f91_exists n with le_lt_dec n 100 := {
  | left H := ((f91_exists (f91_exists (n + 11)).1).1, _) ;
  | right H := (n - 10, _) }.
Proof.
  all:hnf. 2-3:edestruct f91_exists; cbn.
  3:destruct f91_exists. lia.
  apply f91_spec in pr2. destruct le_lt_dec; subst; lia.
  econstructor 2; eauto. constructor. lia.
Defined.

(** Combining these two things allow us to derive the spec of [f91]. *)
Lemma f91 n : (f91_exists n).1 = if le_lt_dec n 100 then 91 else n - 10.
Proof.
  destruct f91_exists. simpl. generalize (f91_spec _ _ pr2).
  destruct le_lt_dec; auto.
Qed.

(** This extracts to [f91]. *)
(* Extraction f91_exists. *)

(** An alternative is to use the domain of [f91] instead,
    which for nested recursive calls requires a quantification
    on the graph relation. *)

Inductive f91_dom : nat -> Prop :=
| f91_dom_gt n : n > 100 -> f91_dom n
| f91_dom_le n :
    n <= 100 -> f91_dom (n + 11) ->
    (forall n', f91_graph (n + 11) n' -> f91_dom n') ->
    f91_dom n.

Lemma le_nle n : n <= 100 -> 100 < n -> False.
Proof. lia. Qed.

(** These two structural inversion lemmas are essential: we rely on the fact
    that they return subterms of their [prf] argument below to define [f91_ongraph]
    by _structural_ recursion. *)

Equations f91_dom_le_inv_l {n} (prf : f91_dom n) (Hle : n <= 100) : f91_dom (n + 11) :=
| f91_dom_gt n H | Hle := ltac:(elimtype False; eauto using le_nle);
| f91_dom_le n H Hd Hg | Hle := Hd.

Equations f91_dom_le_inv_r {n} (prf : f91_dom n) (Hle : n <= 100) : (forall n', f91_graph (n + 11) n' -> f91_dom n') :=
| f91_dom_gt n H | Hle := ltac:(elimtype False; eauto using le_nle);
| f91_dom_le n H Hd Hg | Hle := Hg.

Module WithSigma.

  (** In this case, [f91_ongraph] is recursive on the domain proof, but only does
      inversion of it, not direct pattern-matching which would be forbidden as it
      lives in [Prop]. *)

  Equations? f91_ongraph n (prf : f91_dom n) : Σ r, f91_graph n r by struct prf :=
    f91_ongraph n prf with le_lt_dec n 100 :=
      { | left H => ((f91_ongraph (f91_ongraph (n + 11) _).1 _).1, _);
        | right H => (n - 10, _) }.
  Proof.
    clear f91_ongraph.
    destruct prf. elimtype False; lia.
    apply prf.
    destruct f91_ongraph. clear f91_ongraph. simpl. eapply f91_dom_le_inv_r in prf; eauto.
    destruct f91_ongraph. simpl in *.
    destruct f91_ongraph. clear f91_ongraph. simpl in *.
    econstructor 2; eauto.
    constructor. lia.
  Defined.

  (** The proof witness [f91_dom n] disappears at extraction time.
      But the polymorphic sigma type makes it leave a dummy unit value
      on the side.
   *)
  (* Extraction f91_ongraph. *)
End WithSigma.

Module WithSubset.

  (** Same thing with a subset type for cleaner extraction. We use [Program Mode] to
      avoid explicit projections/injections into subset types. *)

  Set Program Mode.
  Equations? f91_ongraph n (prf : f91_dom n) : { r | f91_graph n r } by struct prf :=
    f91_ongraph n prf with le_lt_dec n 100 :=
      { | left H => f91_ongraph (f91_ongraph (n + 11) _) _;
        | right H => n - 10 }.
  Proof.
    clear f91_ongraph.
    destruct prf. elimtype False; lia.
    apply prf.
    destruct f91_ongraph. clear f91_ongraph. simpl. eapply f91_dom_le_inv_r in prf; eauto.
    destruct f91_ongraph. simpl in *.
    destruct f91_ongraph. clear f91_ongraph. simpl in *.
    econstructor 2; eauto.
    constructor. lia.
  Defined.

  Lemma f91_ongraph_spec n dom : proj1_sig (f91_ongraph n dom) = if le_lt_dec n 100 then 91 else n - 10.
  Proof.
    destruct f91_ongraph. simpl. generalize (f91_spec _ _ f).
    destruct le_lt_dec; auto.
  Qed.

  (** All proof witnesses [f91_dom n] and [f91_graph n r] disappear at extraction time, giving
      the "real" [f91] implementation.
   *)

  (* Extraction f91_ongraph. *)
End WithSubset.
