Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

Require Import Equations.Equations.
Require Import Equations.EqDec.
Unset Equations WithK.

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

Derive Subterm for Term.

Fixpoint term_size
         {a : nat} {tys : Vector.t obj_pair a}
         {dom cod} (t : @Term a tys dom cod) : nat :=
  match t with
  | Ident    => 1%nat
  | Morph _  => 1%nat
  | Comp f g => 1%nat + term_size f + term_size g
  end.

Fail Equations comp_assoc_simpl_rec {a : nat} {tys dom cod}
          (t : @Term a tys dom cod) : @Term a tys dom cod :=
  comp_assoc_simpl_rec t by rec t (MR lt (@term_size a tys dom cod)) :=
  comp_assoc_simpl_rec (Comp f g) <= comp_assoc_simpl_rec f => {
    | Comp i j => Comp i (comp_assoc_simpl_rec (Comp j g));
    | x => Comp x (comp_assoc_simpl_rec g)
  };
  comp_assoc_simpl_rec x := x.