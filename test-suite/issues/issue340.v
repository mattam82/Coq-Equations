(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "." "Top" "-top" "test_equations") -*- *)
(* File reduced by coq-bug-finder from original input, then from 206 lines to 87 lines, then from 105 lines to 87 lines *)
(* coqc version 8.12.0 (August 2020) compiled on Aug 3 2020 10:47:28 with OCaml 4.09.1
   coqtop version 8.12.0 (August 2020) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

From Coq Require Export Bool Lia List.
Notation "! b" := (negb b) (at level 39).
Import ListNotations.
Notation "x 'el' A" := (In x A) (at level 50).

From Equations Require Export Equations.
Set Equations Transparent.
Unset Equations With Funext.

Definition dec P := {P} + {~P}.

Definition var := nat.
Inductive form: Type :=
  Var (x: nat) | Fal | Imp (s t : form).
Notation "s ~> t" := (Imp s t) (at level 41, right associativity).
Implicit Types s t : form.

Inductive sform : Type := Pos (s: form) | Neg (s: form).
Notation "+ s" := (Pos s) (at level 43).
Notation "- s" := (Neg s).

Definition clause := list sform.
Implicit Types S T : sform.
Implicit Types C D E : clause.
Implicit Types L : list clause.

Fact clause_in_dec S C : dec (S el C).
admit.
Defined.

Implicit Types alpha beta : var -> bool.

Equations eva alpha s : bool :=
eva alpha (Var x)  := alpha x ;
eva alpha Fal      := false ;
eva alpha (s ~> t) := !eva alpha s || eva alpha t.
Equations evas alpha S : bool :=
evas alpha (+s) := eva alpha s ;
evas alpha (-s) := !eva alpha s.
Equations evac alpha C : bool :=
evac alpha []     := true ;
evac alpha (T::C) := evas alpha T && evac alpha C.
Equations evad alpha L : bool :=
evad alpha []     := false ;
evad alpha (C::L) := evac alpha C || evad alpha L.

Equations sizeF s : nat :=
sizeF (s1 ~> s2) := 1 + sizeF s1 + sizeF s2 ;
sizeF _          := 1.
Equations size C : nat :=
size nil := 0 ;
size (+s::C) := sizeF s + size C ;
size (-s::C) := sizeF s + size C.

Axiom ho : (clause -> list clause) -> list clause.

Equations? dnf C D : list clause by wf (size D) lt :=
dnf C [] := ho (fun x => dnf C x) ;
dnf C (+Fal :: _) := [] ;
dnf C (-Fal :: D) := dnf C D ;
dnf C (+Imp s t :: D) := dnf C (-s::D) ++ dnf C (+t::D) ;
dnf C (-Imp s t :: D) := dnf C (+s::-t::D) ;
dnf C (+Var x :: D) with clause_in_dec (-Var x) C :=
      { | left _ => [] ;
        | right _ => dnf (+Var x :: C) D } ;
dnf C (-Var x :: D) with clause_in_dec (+Var x) C :=
      { | left _ => [] ;
        | right _ => dnf (-Var x :: C) D } .
Proof.
  admit.
  all: lia.
Qed.

Lemma dnf_eq' alpha C D :
  evad alpha (dnf C D) = evac alpha D && evac alpha C.
Proof.
  funelim (dnf C D); auto.

