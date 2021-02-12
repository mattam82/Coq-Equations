From Equations Require Import Equations.
Definition tyty := Type -> Type.
Inductive X : tyty := | K : X nat.
Derive NoConfusion for X.
Derive Signature for X.
Derive NoConfusionHom for X.
Derive Subterm for X.
Derive EqDec for X.

Check (NoConfusionPackage_X : NoConfusionPackage (sigma (fun x => X x))).
