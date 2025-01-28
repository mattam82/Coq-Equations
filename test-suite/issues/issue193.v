From Stdlib Require Import Program.
From Equations.Prop Require Import Equations.
#[local]
Obligation Tactic := program_simpl.
Equations h_type (P : Type) (H : P) : P := h_type P H => let H1 := H in _.

(* h_type_obligations has type-checked, generating 1 obligation *)
(* Solving obligations automatically... *)
(* h_type_obligations_obligation_1 is defined *)
(* No more obligations remaining *)
(* h_type_obligations is defined *)
(* h_type is defined *)
(* h_type is defined *)
(* The command has indeed failed with message: *)
(* h_type_obligations_obligation_1 cannot be used as a hint. *)

Equations h_prop (P : Prop) (H : P) : P := h_prop P H => _.
(* h_prop_obligations has type-checked, generating 1 obligation *)
(* Solving obligations automatically... *)
(* h_prop_obligations_obligation_1 is defined *)
(* No more obligations remaining *)
(* h_prop_obligations is defined *)
(* h_prop is defined *)
(* h_prop is defined *)
(* The command has indeed failed with message: *)
(* h_prop_obligations_obligation_1 cannot be used as a hint. *)

Example test0 := h_prop.
Example test1 := h_prop_obligations_obligation_1.