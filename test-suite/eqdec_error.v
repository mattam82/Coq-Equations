Require Import Stdlib.Numbers.BinNums.

From Equations Require Import Equations.

Fail Derive EqDec for positive.
Derive NoConfusion EqDec for positive.

#[export]
Instance positive_eqdec' : EqDec positive.
Proof.
  apply _.
Defined.
