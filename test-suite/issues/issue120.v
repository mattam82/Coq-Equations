Require Export Lia.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.
From Equations Require Import Equations.

Inductive id : Type := Id : nat -> id.
Inductive var : Type :=
| varF : id -> var
| varB : id -> var.

Inductive ty : Set :=
| TTop : ty
| TAll : ty -> ty -> ty
| TSel : var -> ty -> ty.

Inductive tm : Set :=
| tvar : id -> tm.

Fixpoint tsize_flat(T: ty) :=
  match T with
    | TTop => 1
    | TAll T1 T2 => S (tsize_flat T1 + tsize_flat T2)
    | TSel _ U => 1 + tsize_flat U
  end.

Definition val_type_termRel :=
  Program.Wf.MR (lexprod lt (fun _ => lt)) (fun p => let '(T, n) := p in (existT (fun _ => nat) n (tsize_flat T))).

Ltac smaller_n := autounfold; apply left_lex; lia.

Instance WF_val_type_termRel: WellFounded val_type_termRel.
  apply Wf.measure_wf; apply wf_lexprod; intro; apply Wf_nat.lt_wf.
Qed.

Equations? val_type (Tn: ty * nat) : Prop by wf Tn val_type_termRel :=
    val_type (pair T (S n)) := val_type (pair T n);
    val_type (pair T O) := True.
Proof. smaller_n. Defined.

Fail Next Obligation.
