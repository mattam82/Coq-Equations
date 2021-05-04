From Coq Require Import Lia NArith.NArith Program.Basics ssr.ssreflect.
From Equations Require Export Equations.

Obligation Tactic := idtac.

Section Context.

Import N.

Local Open Scope N_scope.

Context (f : N -> N) (mono : forall (a b : N) (l : a < b), f a < f b).

Equations f_bogus (n : N) : positive :=
  f_bogus n :=
    let m := f (succ n) - f n in
    match m with
    | N0 => _
    | Npos p => p
    end.
Next Obligation. intros n m. apply xH. Qed.

Equations f_inspect (n : N) : positive :=
  f_inspect n :=
    let m := f (succ n) - f n in
    match exist _ m (eq_refl m) with
    | exist _ N0 e => @const _ (m = N0) _ e
    | exist _ (Npos p) e => @const _ (m = Npos p) p e
    end.
Next Obligation. intros n m _ _ e. pose proof mono n (succ n) as l. lia. Qed.

Lemma eq_f (n : N) : f_bogus n = f_inspect n.
Proof.
  Fail funelim f_bogus.
Abort.
End Context.
