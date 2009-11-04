Require Import Equations.
Require Import List.
(* begin hide *)
Ltac funind c Hcall ::= 
  match c with
    appcontext C [ ?f ] => 
      let x := constr:(fun_ind_prf (f:=f)) in
        (let prf := eval simpl in x in
         let p := context C [ prf ] in
         let prf := fresh in
         let call := fresh in
           assert(prf:=p) ;
           (* Abstract the call *)
           set(call:=c) in *; generalize (refl_equal : call = c); clearbody call ; intro Hcall ;
           (* Now do dependent elimination and simplifications *)
           dependent induction prf ; simplify_IH_hyps)
           (* Use the simplifiers for the constant to get a nicer goal. *)
           (* try on_last_hyp ltac:(fun id => simpc f in id ; noconf id)) *)
        || fail 1 "Internal error in funind"
  end || fail "Maybe you didn't declare the functional induction principle for" c.
(* end hide *)
(** ** Inductive types

   In its simplest form, Equations permits to define functions on inductive datatypes.
   Take for example the booleans defined as an inductive type with two constructors [true] and [false]:
   [[
   Inductive bool : Set := true : bool | false : bool
   ]] 
   
   We can define the boolean negation as follows: *)

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.

(* begin hide *)
Check neg_ind. Check neg_comp.
Check neg_ind_equation_1.
Check neg_ind_equation_2.

(* Lemma neg_inv : forall b, neg (neg b) = b. *)
(* Proof. intros b. funind (neg b) nb.  Qed. *)

(* end hide *)

(** [Equations] declarations are formed by a signature definition and a set of _clauses_ 
   that must form a _covering_ of this signature. The compiler is then expected to
   automatically find a corresponding case-splitting tree that implements the function.
   In simple cases like this, it simply needs to split on the single variable [b] to
   produce two new _programming problems_ [neg true] and [neg false] that are directly 
   handled by the user clauses. We will see in more complex examples that this search
   for a splitting tree may be non-trivial.
 *)

(** ** Reasoning principles

   In the setting of a proof assistant like Coq, we need not only the ability 
   to define complex functions but also get good reasoning support for them.
   Practically, this translates to the ability to simplify applications of functions 
   appearing in the goal and to give strong enough proof principles for recursive 
   definitions.

   [Equations] provides this through an automatic generation of proofs related to
   the function. Namely, each defining equation gives rise to a lemma stating the 
   equality between the left and right hand sides. These equations can be used as 
   rewrite rules for simplification during proofs, without having to rely on the
   fragile simplifications implemented by raw reduction. We can also generate the
   inductive graph of any [Equations] definition, giving the strongest induction 
   principle on the function. 

   I.e., for [neg] the inductive graph is defined as:
   [[
   Inductive neg_ind : forall b : bool, neg_comp b -> Prop :=
   | neg_ind_equation_1 : neg_ind true false
   | neg_ind_equation_2 : neg_ind false true
   ]]

   Along with a proof that [Π b, neg_ind b (neg b)], we can eliminate any call
   to [neg] specializing its argument and result in a single command. 
   Suppose we want to show that [neg] is involutive for example, our goal will 
   look like:
   
   [[
  b : bool
  ============================
   neg (neg b) = b
   ]]
   

   An application of the [funind] tactic will produce two goals corresponding to 
   the splitting done in [neg]: [neg false = true] and [neg true = false].
   These correspond exactly to the rewriting lemmas generated for [neg].

   In the following sections we will show how these ideas generalize to more complex 
   types and definitions involving dependencies, overlapping clauses and recursion.
   
   ** Building up

   *** Polymorphism
   
   Coq's inductive types can be parameterized by types, giving polymorphic datatypes.
   For example the list datatype is defined as:
   *)

Inductive list {A} : Type := nil : list | cons : A -> list -> list.
Implicit Arguments list []. Notation " x :: l " := (cons x l).

(** No special support for polymorphism is needed, as type arguments are treated 
   like regular arguments in dependent type theories. Note however that one cannot
   match on type arguments, there is no intensional type analysis. We will present 
   later how to programm with universes to achive the same kind of genericity. 
   We can write the standard [tail] function as follows:
*)

Equations tail {A} (l : list A) : list A :=
tail A nil := nil ;
tail A (cons a v) := v.

(** *** Recursive inductive types 
   
   Of course with inductive types comes recursion. Coq accepts a subset of the 
   structurally recursive definitions by default (it is incomplete due to its 
   syntactic nature). We will use this as a first step towards a more robust 
   treatment of recursion via well-founded relations in section %\ref{sec:wfrec}%.
   A classical example is list concatenation: *)

Equations app {A} (l l' : list A) : list A :=
app A nil l := l ;
app A (cons a v) l := cons a (app v l).
Print app_ind_ind.
(** Recursive definitions like [app] can be unfolded easily so proving the 
   equations as rewrite rules is direct. The induction principle associated 
   to this definition is more interesting however, as we will get an 
   induction hypothesis for the recursive call:
   [[
Inductive app_ind : forall (A : Type) (l l' : list A), app_comp l l' -> Prop :=
  | app_ind_equation_1 : forall (A : Type) (l' : list A), app_ind A nil l' l'
  | app_ind_equation_2 : forall (A : Type) (a : A) (l l' : list A),
     app_ind A l l' (app l l') -> app_ind A (cons a l) l' (cons a (app l l'))
]]

  Here 

 *) 


(* begin hide *)
Check app_ind. Check @app_comp. Check @app_ind_equation_1. Check @app_ind_equation_2.
(* end hide *)

Equations filter {A} (l : list A) (p : A -> bool) : list A :=
filter A nil p := nil ;
filter A (cons a l) p <= p a => {
  filter A (cons a l) p true := a :: filter l p ;
  filter A (cons a l) p false := filter l p }.


(** ** Dependent types *)

Equations(nocomp) equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := in_left ;
equal (S n) (S m) <= equal n m => {
  equal (S n) (S n) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := in_right } ;
equal x y := in_right.


(** The [tail] function is made total by returning the dummy element [nil] in the 
   first equation, but we might like to express that such partial functions are
   in fact total, given a precondition on their input. *)
(* Equations head A (l : list A | l <> nil) : A := *)
(* head A (exist nil pf) :=! pf; *)
(* head A (exist (cons a v) _) := a. *)

Equations head A (l : list A) (pf : l <> nil) : A :=
head A nil pf :=! pf;
head A (cons a v) _ := a.

Next Obligation. depelim l. impossible_call head. constructor. Defined.

(** ** Inductive families *)

Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
K A x P p eq_refl := p.

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans A ?(x) ?(x) ?(x) eq_refl eq_refl := eq_refl.
