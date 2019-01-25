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
Import Sigma_Notations.
Require Import Wellfounded Relations.

Derive NoConfusion for positive.
Derive EqDec for positive.
Derive Signature NoConfusion Subterm for Term.

Fixpoint term_size
         {a : nat} {tys : Vector.t obj_pair a}
         {dom cod} (t : @Term a tys dom cod) : nat :=
  match t with
  | Ident    => 1%nat
  | Morph _  => 1%nat
  | Comp f g => 1%nat + term_size f + term_size g
  end.
Set Program Mode.

Equations? comp_assoc_simpl_rec {a : nat} {tys dom cod}
          (t : @Term a tys dom cod) : {t' : @Term a tys dom cod | term_size t' <= term_size t}
  by wf (term_size t) lt :=
  comp_assoc_simpl_rec (Comp f g) with comp_assoc_simpl_rec f => {
    | exist _ (Comp i j) Hle => Comp i (comp_assoc_simpl_rec (Comp j g));
    | x => Comp x (comp_assoc_simpl_rec g)
  };
  comp_assoc_simpl_rec x := x.
Proof.
  1-2,4:lia.
  all:(simpl; try destruct_call comp_assoc_simpl_rec; simpl in *; lia).
Time Defined.

Definition comp_assoc_simpl {a}
           {tys : Vector.t obj_pair a} {dom cod} (t : Term tys dom cod) : Term tys dom cod :=
  comp_assoc_simpl_rec t.

Lemma comp_assoc_simpl_ident {a} {tys : Vector.t obj_pair a} {dom cod} (g : Term tys dom cod) :
  comp_assoc_simpl (Comp Ident g) = Comp Ident (comp_assoc_simpl g).
Proof.
  unfold comp_assoc_simpl.
  Opaque comp_assoc_simpl_rec.
  autorewrite with comp_assoc_simpl_rec. simpl. reflexivity.
Qed.

Unset Program Mode.
Open Scope program_scope.

Lemma comp_assoc_simpl_comp {a} {tys : Vector.t obj_pair a} {dom mid cod}
      (f : Term tys mid cod) (g : Term tys dom mid) :
  comp_assoc_simpl (Comp f g) =
  match comp_assoc_simpl f in Term _ mid cod return Term tys dom mid -> Term tys dom cod with
  | Comp f f' => fun g => Comp f (comp_assoc_simpl (Comp f' g))
  | x => fun g => Comp x (comp_assoc_simpl g) end g.
Proof.
  unfold comp_assoc_simpl.
  simp comp_assoc_simpl_rec.
  revert dom g. reverse.
  let felim := constr:(fun_elim (f := @comp_assoc_simpl_rec)) in
  unshelve refine_ho (felim _ _ _ _ _ _); simpl; intros; try reflexivity.
Qed.
