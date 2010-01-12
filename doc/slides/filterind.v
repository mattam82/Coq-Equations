Require Import Equations List.

Equations filter {A} (l : list A) (p : A -> bool) : list A :=
filter A nil p := nil ;
filter A (cons a l) p with p a := {
  | true := a :: filter l p ;
  | false := filter l p }.
Print filter_ind.
Check app.
Equations app' {A} (l l' : list A) : (list A) :=
app' A nil l := l ;
app' A (cons a v) l := cons a (app' v l).
Goal Π A (l : list A), app' l [] = l.
Proof. intros. funelim (app' l []); auto. now rewrite H. Defined.

About filter_ind_mut.
Check(filter_ind_mut :
  forall (P : forall (A : Type) (l : list A) (p : A -> bool), filter_comp l p -> Prop)
  (P0 : forall (A : Type) (a : A) (l : list A) (p : A -> bool),
    bool -> filter_comp (a :: l) p -> Prop),

  (forall A p, P A [] p []) ->

  (forall A a l p,
    filter_ind_1 A a l p (p a) (filter_obligation_2 (@filter) A a l p (p a)) ->
    P0 A a l p (p a) (filter_obligation_2 (@filter) A a l p (p a)) ->
    P A (a :: l) p (filter_obligation_2 (@filter) A a l p (p a))) ->

  (forall A a l p, filter_ind A l p (filter l p) ->
    P A l p (filter l p) -> P0 A a l p true (a :: filter l p)) ->
  (forall A a l p, filter_ind A l p (filter l p) ->
    P A l p (filter l p) -> P0 A a l p false (filter l p)) ->

  forall A l p (f3 : filter_comp l p),
    filter_ind A l p f3 -> P A l p f3).

Check (filter_elim :
  forall P : forall (A : Type) (l : list A) (p : A -> bool), filter_comp l p -> Prop,
  let P0 :=
    fun (A : Type) (a : A) (l : list A) (p : A -> bool) 
      (refine : bool) (H : filter_comp (a :: l) p) =>
      p a = refine -> P A (a :: l) p H 
  in
  (forall (A : Type) (p : A -> bool), P A [] p []) ->
  (forall (A : Type) (a : A) (l : list A) (p : A -> bool),
    P A l p (filter l p) -> P0 A a l p true (a :: filter l p)) ->
  (forall (A : Type) (a : A) (l : list A) (p : A -> bool),
    P A l p (filter l p) -> P0 A a l p false (filter l p)) ->
  forall (A : Type) (l : list A) (p : A -> bool), P A l p (filter l p)).

(*
Inductive filter_ind : forall (A : Type) (l : list A) (p : A -> bool),
  filter_comp l p -> Prop :=
| filter_ind_equation_1 : forall (A : Type) (p : A -> bool),
    filter_ind A [] p []
| filter_ind_refinement_2 : forall (A : Type) (a : A) 
  (l : list A) (p : A -> bool),
  filter_ind_1 A a l p (p a) (filter_obligation_2 (@filter) A a l p (p a)) ->
  filter_ind A (a :: l) p (filter_obligation_2 (@filter) A a l p (p a))

with filter_ind_1 : forall (A : Type) (a : A) (l : list A) (p : A -> bool),
  bool -> filter_comp (a :: l) p -> Prop :=
| filter_ind_1_equation_1 : forall (A : Type) (a : A) (l : list A) (p : A -> bool),
  filter_ind A l p (filter l p) ->
  filter_ind_1 A a l p true (a :: filter l p)
| filter_ind_1_equation_2 : forall (A : Type) (a : A) (l : list A) (p : A -> bool),
  filter_ind A l p (filter l p) ->
  filter_ind_1 A a l p false (filter l p).
*)