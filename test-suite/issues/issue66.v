Require Equations.Equations.

Definition f (l l': list nat) (H: 0 = 0): Prop. Admitted.
Axiom cheat : forall {A}, A.
Equations? id (l: list nat) (H: f l l _): { r: list nat | f l r _ } :=
  id l H := exist _ nil _.
Proof. apply cheat. Defined.

Definition check := id_elim.