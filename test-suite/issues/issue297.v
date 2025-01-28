From Equations.Prop Require Import Equations.


Goal forall P y, P y -> let n := y in n = 12 -> P n.
  intros P y py n. simplify ?. apply py.
Qed.
