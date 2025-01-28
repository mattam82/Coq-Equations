Set Warnings "-notation-overridden".
From Equations.Type Require Import All.
#[warning="-notation-incompatible-prefix"]
Require Import Examples.HoTT_light.
Set Universe Polymorphism.
From Stdlib Require Import Relations.

Import Id_Notations.
Import Sigma_Notations.

Derive Signature for Id.

Equations neg (b : bool) : bool :=
  neg true := false; neg false := true.

Definition neg_fib (x : bool) := Σ a : bool, neg_graph a x.
#[local] Hint Resolve neg_graph_correct : core.
Definition neg_graph_rec := neg_graph_rect.

Scheme neg_graph_rect_dep := Induction for neg_graph Sort Type.

Lemma hfiber_graph : (Σ x : bool, hfiber neg x) <~> Σ x : bool, neg_fib x.
Proof.
  unshelve refine {| equiv_fun := fun h => (h.1, _) |}.
  red. destruct h as [res [arg Heq]].
  exists arg. simpl. destruct Heq. auto.
  simpl.
  unshelve refine {| equiv_inv h := (h.1, _) |}.
  red. destruct h as [res [arg Heq]].
  exists arg. simpl. induction Heq; reflexivity.
  red.

  - intros [x [res Hind]]. simpl.
    induction Hind using neg_graph_rect_dep; simpl; reflexivity.

  - intros [res [arg Heq]]. simpl.
    destruct Heq; simpl.
    apply path_sigma_uncurried. simpl. exists id_refl. simpl.
    apply path_sigma_uncurried. simpl. exists id_refl.
    simpl. destruct arg. simpl. reflexivity.
    simpl. reflexivity.

  - simpl.
    intros [res [arg Heq]]. destruct Heq. 
    destruct arg. simpl. reflexivity. simpl. reflexivity.
Qed.
