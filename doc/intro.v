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

Ltac funelim c :=
  match c with
    appcontext C [ ?f ] => 
      let x := constr:(fun_elim (f:=f)) in
        (let prf := eval simpl in x in
          dependent_pattern c ; apply prf)
  end.

Derive DependentElimination for nat bool option sum prod list.
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

Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b. funelim (neg b); simp neg. Defined.

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
   later how to program with universes to achive the same kind of genericity. 
   We can write the polymorphic [tail] function as follows:
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
app A nil l' := l' ;
app A (cons a l) l' := cons a (app l l').

(** Recursive definitions like [app] can be unfolded easily so proving the 
   equations as rewrite rules is direct. The induction principle associated 
   to this definition is more interesting however. We can derive from it the 
   following _elimination_ principle for calls to [app]:
   [[
app_elim :
forall P : forall (A : Type) (l l' : list A), app_comp l l' -> Prop,
(forall (A : Type) (l' : list A), P A nil l' l') ->
(forall (A : Type) (a : A) (l l' : list A),
 P A l l' (app l l') -> P A (a :: l) l' (a :: app l l')) ->
forall (A : Type) (l l' : list A), P A l l' (app l l')
]]

  Using this eliminator, we can write proofs exactly following the 
  structure of the function definition, instead of redoing the splitting 
  by hand. This idea is already present in the [Function] package 
  %\cite{Barthe:2006gp}% that derives induction principles from
  function definitions, we will discuss the main differences with [Equations]
  in section %\ref{sec:related}%.
 *)

(* begin hide *)
Check app_ind. Check @app_comp. Check @app_ind_equation_1. Check @app_ind_equation_2.
(* end hide *)

(** *** Moving to the left

   The structure of real programs is richer than a simple case tree on the 
   original arguments in general. In the course of a computation, we might 
   want to scrutinize intermediate results (e.g. comming from function calls)
   to produce an answer. This literally means adding a new pattern to the left of
   our equations made available for further refinement. This concept is know as with
   clauses in the Agda %\cite{norell:thesis}% community and was first presented 
   and implemented in the Epigram language %\cite{DBLP:journals/jfp/McBrideM04}%. 

   The compilation of with clauses and its treatment for generating equations and the
   induction principle are quite involved and will be discussed in section %\ref{sec:with}%.
   Suffice is to say that each with node generates an auxiliary definition from the clauses
   in the curly brackets, taking the additional object as argument. The equation for the
   with node will simply be an indirection to the auxiliary definition and simplification 
   will continue as usual with the auxiliary definition's rewrite rules.
   *)

Equations filter {A} (l : list A) (p : A -> bool) : list A :=
filter A nil p := nil ;
filter A (cons a l) p <= p a => {
  filter A (cons a l) p true := a :: filter l p ;
  filter A (cons a l) p false := filter l p }.

(** A common use of with clauses is to scrutinize recursive results like the following: *)

Equations unzip {A B} (l : list (A * B)) : list A * list B :=
unzip A B nil := (nil, nil) ;
unzip A B (cons p l) <= unzip l => {
  unzip A B (cons (pair a b) l) (pair la lb) := (a :: la, b :: lb) }.

(** The real power of with however comes when it is used with dependent types. *)

(** ** Dependent types
   
   Coq supports writing dependent functions, in other words, it gives the ability to
   make the results _type_ depend on actual _values_, like the arguments of the function.
   A simple example is given below of a function which decides the equality of two 
   natural numbers, returning a sum type carrying proofs of the equality or disequality 
   of the arguments. The sum type [{ A } + { B }] is a constructive variant of disjunction 
   that can be used in programs to give at the same time a boolean algorithmic information 
   (are we in branch [A] or [B]) and a _logical_ information (a proof witness of [A] or [B]).
   Hence its constructors [left] and [right] take proofs as arguments. The [eq_refl] proof 
   term is the single proof of [x = x] (the [x] is generaly infered automatically).
*)

Equations equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := left eq_refl ;
equal (S n) (S m) <= equal n m => {
  equal (S n) (S ?(n)) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := right _ } ;
equal x y := right _.

(** Of particular interest here is the inner program refining the recursive result.
   As [equal n m] is of type [{ n = m } + { n <> m }] we have two cases to consider:

   - Either we are in the [left p] case, and we know that [p] is a proof that [n = m],
     in which case we can do a nested match on [p]. The result of matching this equality
     proof is to unify [n] and [m], hence the left hand side patterns become [S n] and
     [S ?(n)] and the return type of this branch is refined to [{ n = n } + { n <> n }].
     We can easily provide a proof for the left case. 
     
   - In the right case, we mark the proof unfilled with an underscore. This will
     generate an obligation for this hole, that can be filled automatically by a 
     predefined tactic or interactively by the user in proof mode (this uses the
     same obligation mechanism as the Program extension
     %\cite{sozeau.Coq/FingerTrees/article}%).
*)

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
