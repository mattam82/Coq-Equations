From Equations Require Import Equations EqDec DepElimK.
Import Sigma_Notations.

(** This noConfusion instance corresponds to the rule for simplifying injectivity with UIP. *)

Section NoConfusionUIP.
  Context {A} (B : A -> Type) `(E : UIP A).

  Definition NoConfusion_UIP:  forall x, B x -> B x -> Prop := fun x y z => (x, y) = (x, z).

  Definition UIP_NoConfusionPackage : forall x, NoConfusionPackage (B x).
  Proof.
    intros.
    unshelve refine ({| NoConfusion := NoConfusion_UIP x |}).
    intros a b. simplify ?. constructor.
    intros a b H. red in H. apply (pr2_uip H).
    simpl. intros a b. simplify ?. simpl solution_right.
    apply pr2_uip_refl.
  Defined.
End NoConfusionUIP.
