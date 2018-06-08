Require Equations.Equations.

Axiom unsupported: False. 
Axiom ignore_termination: nat.  

Ltac t := intros; match goal with
  | |- (?T < ?T)%nat => 
    unify T ignore_termination; apply False_ind; exact unsupported
  end.

Obligation Tactic := t.

Equations content (n: nat): nat := 
content n by rec ignore_termination lt :=
content n := content n.

Definition check := content_elim.
