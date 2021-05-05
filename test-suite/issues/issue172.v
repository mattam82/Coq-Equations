Set Implicit Arguments.

From Equations Require Export Equations.
Require Export Equations.Prop.Subterm.

(* Module KAxiom. *)

(** By default we disallow the K axiom, but it can be set. *)

Set Equations With UIP.

(** In this case the following definition uses the [K] axiom just imported. *)
Axiom uip : forall A, UIP A.
#[export] 
Existing Instance uip.

Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl)
          (H : x = x) : P H :=
  K P p eq_refl := p.
