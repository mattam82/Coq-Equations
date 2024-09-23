From Stdlib Require Import Program.
From Equations Require Import Equations.
Definition tyty := Type -> Type.
Inductive X : tyty := | K : X nat.

Derive NoConfusion for X.
Derive Signature for X.

Derive NoConfusionHom for X.

Next Obligation.
now dependent induction a; dependent induction b.
Defined.

Next Obligation.
dependent induction a; dependent induction b; simpl.
now compute; rewrite JMeq_eq_refl; destruct e.
Defined.

Next Obligation.
dependent induction b; simpl.
now compute; rewrite JMeq_eq_refl.
Defined.

Derive Subterm for X.

Derive EqDec for X.

Next Obligation.
now destruct x; dependent induction y; left.
Defined.

Check (NoConfusionPackage_X : NoConfusionPackage (sigma (fun x => X x))).
