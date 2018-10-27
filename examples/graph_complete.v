Require Import Equations.
Require Import HoTT_light.
Set Universe Polymorphism.
Require Import Relations.
Require Import ConstantsType.

Import Id_Notations.
Import Sigma_Notations.

Derive Signature for Id.

Equations neg (b : bool) : bool :=
  neg true := false; neg false := true.

Scheme neg_ind_rec := Minimality for neg_ind Sort Set.
Scheme neg_ind_rect_dep := Induction for neg_ind Sort Type.

Definition neg_fib (x : bool) := &{ a : bool & neg_ind a x }.

Lemma hfiber_graph : &{ x : bool & hfiber neg x } <~> &{ x : bool & neg_fib x }.
Proof.
  unshelve refine {| equiv_fun := fun h => &(h.1 & _) |}.
  red. destruct h as [res [arg Heq]].
  exists arg. simpl. rewrite <- Heq. apply neg_ind_fun.
  simpl.
  unshelve refine {| equiv_inv h := &(h.1 & _) |}.
  red. destruct h as [res [arg Heq]].
  exists arg. simpl. induction Heq. reflexivity. reflexivity.
  red.

  - intros [x [res Hind]]. simpl.
    induction Hind using neg_ind_rect_dep; simpl; reflexivity.

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
