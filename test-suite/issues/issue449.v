Module Import tactics.
  Tactic Notation "simplify_eq" := idtac.
End tactics.

Goal True. Proof. simplify_eq. auto. Qed.

From Equations Require Import Equations.

Goal True. Proof. simplify_eq. auto. Qed.
