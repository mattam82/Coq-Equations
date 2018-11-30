Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.
Require Import Lia.
Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.
Set Equations WithKDec.
Generalizable All Variables.

Definition obj_idx : Type := positive.
Definition arr_idx (n : nat) : Type := Fin.t n.

Import VectorNotations.

Definition obj_pair := (obj_idx * obj_idx)%type.

Inductive Term {a} (tys : Vector.t (obj_idx * obj_idx) a)
          : obj_idx -> obj_idx -> Type :=
  | Ident : forall dom, Term tys dom dom
  | Morph (f : arr_idx a) : Term tys (fst (tys[@f])) (snd (tys[@f]))
  | Comp (dom mid cod : obj_idx)
         (f : Term tys mid cod) (g : Term tys dom mid) :
      Term tys dom cod.

Arguments Ident {a tys dom}.
Arguments Morph {a tys} f.
Arguments Comp {a tys dom mid cod} f g.

Derive NoConfusion for positive.
Derive EqDec for positive.
Derive Signature NoConfusion Subterm for Term.
Axiom cheat : forall {A}, A.

Next Obligation.
Proof.
  apply cheat. (* FIXME *)
  (* Subterm.solve_subterm. revert H. simplify *. noconf H. *)
Qed.

Fixpoint term_size
         {a : nat} {tys : Vector.t obj_pair a}
         {dom cod} (t : @Term a tys dom cod) : nat :=
  match t with
  | Ident    => 1%nat
  | Morph _  => 1%nat
  | Comp f g => 1%nat + term_size f + term_size g
  end.
Set Program Mode.
Equations comp_assoc_simpl_rec {a : nat} {tys dom cod}
          (t : @Term a tys dom cod) : {t' : @Term a tys dom cod | term_size t' <= term_size t}
  by rec (term_size t) lt :=
  comp_assoc_simpl_rec (Comp f g) with comp_assoc_simpl_rec f => {
    | exist _ (Comp i j) Hle => Comp i (comp_assoc_simpl_rec (Comp j g));
    | x => Comp x (comp_assoc_simpl_rec g)
  };
  comp_assoc_simpl_rec x := x.

Solve Obligations with program_simpl; try destruct_call comp_assoc_simpl_rec; simpl in *; lia.
Solve Obligations.
