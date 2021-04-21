From Equations Require Import Equations.
Import Sigma_Notations.

(** This noConfusion instance corresponds to the rule for simplifying injectivity with UIP. *)

Set Equations With UIP.

Section NoConfusionUIP.
  Context {A} (B : A -> Type) `(E : UIP A).

  Definition NoConfusion_UIP:  forall x, B x -> B x -> Prop := fun x y z => (x, y) = (x, z).

  Definition UIP_NoConfusionPackage : forall x, NoConfusionPackage (B x).
  Proof.
    intros.
    unshelve refine ({| NoConfusion := NoConfusion_UIP x |}).
    intros a b. simplify ?. simpl. trivial.
    intros a b. simplify *. constructor.
    intros a b. simpl. unfold NoConfusion_UIP. simplify *. simpl.
    rewrite DepElim.simplification_K_uip_refl. reflexivity.
    intros. simpl. destruct e. simpl. 
    now rewrite DepElim.simplification_K_uip_refl.
  Defined.
End NoConfusionUIP.
