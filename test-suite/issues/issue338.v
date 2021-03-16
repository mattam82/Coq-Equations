(* success *)
From Coq Require Import ssreflect.
From Equations Require Import Equations.

Import EquationsNotations.
Open Scope equations_scope.

Goal (forall n, n + 0 = n). intros.
 now rewrite -!plus_n_O.
Qed.



(* rewrite fails with:
Error:
Syntax error: '*' or [tactic:ssrrwargs] or [oriented_rewriter] expected after 'rewrite' (in [tactic:simple_tactic]).
*)
