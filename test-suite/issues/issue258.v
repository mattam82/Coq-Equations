From Stdlib Require Import Psatz.
From Equations.Prop Require Import Equations.

Inductive Pre := Pi : Pre -> Pre.

Fixpoint pre_size (p : Pre) : nat :=
  match p with
  | Pi τ => 1 + pre_size τ
  end.

Inductive InterpInput :=
| inp_ctx (Γp : nat)
| inp_ty (Γp : nat) (Γ : nat) (σp : Pre).

Definition measure_input (ii : InterpInput) : nat :=
  match ii with
  | inp_ctx Γp => Γp
  | inp_ty Γp Γ σp => Γp + pre_size σp
  end.

Equations? interp (ii : InterpInput) : nat by wf (measure_input ii) lt :=
  interp (inp_ty Γp Γ (Pi τp)) :=
    let piΓ := interp (inp_ctx Γp) in
    let τ := interp (inp_ty Γp piΓ τp) in
    0;
  interp _ := 0.
Proof. all: abstract lia. Defined.

Definition test := interp_elim.
