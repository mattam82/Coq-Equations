From Equations Require Import Equations.
Equations foo (n : nat) : nat :=
  {
    foo 0
      with true, true, true :=
      {
      | true | true | true := 1;
      | _ | _ | _ := 0
      };

    foo _ := 0

  }.

Equations foo' (n : nat) : nat :=
  {
    foo' 0
      with true, true, true, true :=
      {
      | true | true | true | true := 1;
      | _ | _ | _ | _ := 0
      };

    foo' _ := 0

  }.
