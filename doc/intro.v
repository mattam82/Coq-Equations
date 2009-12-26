(** * A gentle introduction to [Equations] 

   [Equations] is a plugin for Coq%\footnote{Currently available for the trunk version only}
   \cite{Coq}% that comes with a few support modules defining classes and tactics for 
   running it. We will introduce its main features through a handful of examples, requiring 
   no prior knowledge of the tool. We start our Coq primer session by importing the [Equations]
   module.
   *)

Require Import Equations.

(* begin hide *)
Check @eq.
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
          dependent pattern c ; apply prf)
  end.
Require Import Bvector.

(* Derive DependentElimination for nat bool option sum prod list vector. *)
(* end hide *)

(** ** Inductive types

   In its simplest form, [Equations] allows to define functions on inductive datatypes.
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
   In this case, it simply needs to split on the single variable [b] to
   produce two new _programming problems_ [neg true] and [neg false] that are directly 
   handled by the user clauses. We will see in more complex examples that this search
   for a splitting tree may be non-trivial. *)

(** ** Reasoning principles

   In the setting of a proof assistant like Coq, we need not only the ability 
   to define complex functions but also get good reasoning support for them.
   Practically, this translates to the ability to simplify applications of functions 
   appearing in the goal and to give strong enough proof principles for (recursive)
   definitions.

   [Equations] provides this through an automatic generation of proofs related to
   the function. Namely, each defining equation gives rise to a lemma stating the 
   equality between the left and right hand sides. These equations can be used as 
   rewrite rules for simplification during proofs, without having to rely on the
   fragile simplifications implemented by raw reduction. We can also generate the
   inductive graph of any [Equations] definition, giving the strongest elimination
   principle on the function. 

   I.e., for [neg] the inductive graph is defined as: [[
Inductive neg_ind : forall b : bool, bool -> Prop :=
| neg_ind_equation_1 : neg_ind true false
| neg_ind_equation_2 : neg_ind false true ]]

   Along with a proof of [Π b, neg_ind b (neg b)], we can eliminate any call
   to [neg] specializing its argument and result in a single command. 
   Suppose we want to show that [neg] is involutive for example, our goal will 
   look like: [[
  b : bool
  ============================
   neg (neg b) = b ]]
   An application of the tactic [funelim (neg b)] will produce two goals corresponding to 
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
Implicit Arguments list []. Notation "x :: l" := (cons x l).

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
   following _elimination_ principle for calls to [app]: [[
   app_elim :
   forall P : forall (A : Type) (l l' : list A), app_comp l l' -> Prop,
   (forall (A : Type) (l' : list A), P A nil l' l') ->
   (forall (A : Type) (a : A) (l l' : list A),
   P A l l' (app l l') -> P A (a :: l) l' (a :: app l l')) ->
   forall (A : Type) (l l' : list A), P A l l' (app l l') ]]
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
   want to scrutinize intermediate results (e.g. coming from function calls)
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
  equal (S n) (S n) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := right _ } ;
equal x y := right _.

(** Of particular interest here is the inner program refining the recursive result.
   As [equal n m] is of type [{ n = m } + { n <> m }] we have two cases to consider:
   
   - Either we are in the [left p] case, and we know that [p] is a proof of [n = m],
     in which case we can do a nested match on [p]. The result of matching this equality
     proof is to unify [n] and [m], hence the left hand side patterns become [S n] and
     [S ?(n)] and the return type of this branch is refined to [{ n = n } + { n <> n }].
     We can easily provide a proof for the left case. 
     
   - In the right case, we mark the proof unfilled with an underscore. This will
     generate an obligation for the hole, that can be filled automatically by a 
     predefined tactic or interactively by the user in proof mode (this uses the
     same obligation mechanism as the Program extension
     %\cite{sozeau.Coq/FingerTrees/article}%). In this case the automatic tactic 
     is able to derive by itself that [n <> m -> S n <> S m].

   Dependent types are also useful to turn partial functions into total functions by
   restricting their domain. Typically, we can force the list passed to [head] 
   to be non-empty using the specification:
*)

Equations head A (l : list A) (pf : l <> nil) : A :=
head A nil pf :=! pf;
head A (cons a v) _ := a.

(** We decompose the list and are faced with two cases:

   - In the first case, the list is empty, hence the proof [pf] of type 
     [nil <> nil] allows us to derive a contradiction. We make use of
     another category of right-hand sides, which we call _empty_ nodes
     to inform the compiler that a contradiction is derivable in this case.
     In general we cannot expect the compiler to find by himself that 
     the context contains a contradiction, as it is undecidable 
     %(\cite{DBLP:conf/plpv/Oury07,DBLP:conf/birthday/GoguenMM06})%.
   - In the second case, we simply return the head of the list, disregarding
     the proof.
 *)

(** *** Inductive families

   The next step is to make constraints such as non-emptiness part of the 
   datatype itself. This capability is provided through inductive families in
   Coq %\cite{paulin93tlca}%, which are a similar concept to the generalization 
   of algebraic datatypes to GADTs in functional languages like Haskell 
   %\cite{ghani-popl07,GADTcomplete}%. Families provide a way to associate to each constructor 
   a different type, making it possible to give specific information about a value 
   in its type. 

   **** Equality 
   The alma mater of inductive families is the propositional equality 
   [eq] defined as: [[
Inductive eq (A : Type) (x : A) : A -> Prop := 
 eq_refl : eq A x x. ]]
   
   It is a central tool in the compilation process so we present it in detail here.
   It is also a contentious subject in the type theory community, we'll discuss 
   it in section %\ref{sec:equality}%.

   Equality is a polymorphic relation on [A]. (The [Prop] sort (or kind) categorizes
   propositions, while the [Set] sort, equivalent to $\star$ in Haskell categorizes 
   computational types.) Equality is _parameterized_ by a value [x] of type [A] and 
   _indexed_ by another value of type [A]. Its single constructor states that 
   equality is reflexive, so the only way to build an object of [eq x y] is if 
   [x ~= y], that is if [x] is definitionaly equal to [y]. 
   
   Now what is the elimination principle associated to this inductive family?
   It is the good old Leibniz substitution principle: [[
forall (A : Type) (x : A) (P : A -> Type), P x -> forall y : A, x = y -> P y ]]

   Provided a proof that [x = y], we can create on object of type [P y] from an 
   existing object of type [P x]. This substitution principle is enough to show
   that equality is symmetric and transitive. For example we can use 
   pattern-matching on equality proofs to show:
 *)

Equations eqt {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eqt A ?(x) ?(x) ?(x) eq_refl eq_refl := eq_refl.

(** Let us explain the meaning of the non-linear patterns here that we 
   slipped through in the [equal] example. By pattern-matching on the 
   equalities, we have unified [x], [y] and [z], hence we determined the 
   _values_ of the patterns for the variables to be [x]. The [?(x)] 
   notation is essentially denoting that the pattern is not a candidate 
   for refinement, as it is determined by another pattern. 

   **** Indexed datatypes
   
   Functions on [vector]s provide more stricking examples of this situation.
   The [vector] family is indexed by a natural number representing the size of 
   the vector: [[
Inductive vector (A : Type) : nat -> Type :=
| Vnil : vector A O
| Vcons : A -> forall n : nat, vector A n -> vector A (S n) ]]

   The empty vector [Vnil] has size [O] while the cons operation increments 
   the size by one. Now let us define the usual map on vectors:
 *)

Equations vmap {A B} (f : A -> B) {n} (v : vector A n) :
  vector B n :=
vmap A B f ?(0) Vnil := Vnil ;
vmap A B f ?(S n) (Vcons a n v) := Vcons (f a) (vmap f v).

(** Here the value of the index representing the size of the vector 
   is directly determined by the constructor, hence in the case tree
   we have no need to eliminate [n]. This means in particular that 
   the function [vmap] does not do any computation with [n], and 
   the argument could be eliminated in the extracted code.
   In other words, it provides only _logical_ information about 
   the shape of [v] but no computational information.

   The [vmap] function works on every member of the [vector] family,
   but some functions may work only for some subfamilies, for example
   [vtail]:
 *)

Equations(nocomp) vtail {A n} (v : vector A (S n)) : vector A n :=
vtail A n (Vcons a n v') := v'.

(** The type of [v] ensures that [vtail] can only be applied to 
   non-empty vectors, moreover the patterns only need to consider 
   constructors that can produce objects in the subfamily [vector A (S n)],
   excluding [Vnil]. The pattern-matching compiler uses unification 
   with the theory of constructors to discover which cases need to 
   be considered and which are impossible. In this case the failed 
   unification of [0] and [S n] shows that the [Vnil] case is impossible.
   This powerful unification engine running under the hood permits to write
   concise code where all uninteresting cases are handled automatically.
   
   Of course the equations and the induction principle are simplified in a 
   similar way. If we encounter a call to [vtail] in a proof, we can 
   use the following elimination principle to simplify both the call and the
   argument which will be automatically substituted by an object of the form
   [Vcons _ _ _]:[[
forall P : forall (A : Type) (n : nat), vector A (S n) -> vector A n -> Prop,
(forall (A : Type) (n : nat) (a : A) (v : vector A n), 
  P A n (Vcons a v) v) ->
forall (A : Type) (n : nat) (v : vector A (S n)), P A n v (vtail v) ]] 

   As a witness of the power of the unification, consider the following function 
   which computes the diagonal of a square matrix of size [n * n].
*) 

Equations(nocomp noind) diag {A n} 
  (v : vector (vector A n) n) : vector A n :=
diag A O Vnil := Vnil ;
diag A (S n) (Vcons (Vcons a n v) n v') := 
  Vcons a (diag (vmap vtail v')).

(** Here in the second equation, we know that the elements of the vector 
   are necessarily of size [S n] too, hence we can do a nested refinement
   on the first one to find the first element of the diagonal. 
   The [nocomp] and [noind] flags of [Equations] used here allow the 
   guardness checker of Coq to validate the definition and the equations
   proofs in reasonable time, but it takes too long to check that the
   induction principle proof is well-formed%\footnote{Or guarded in Coq jargon}%.

   This closes our presentation of the basic features of [Equations]. 
   Our contribution is a realistic implementation of dependent pattern-matching
   which can be used to write programs on inductive families, also 
   providing tools to reason on them. We will now delve into the details of 
   the implementation and come back to the user side later, introducing 
   the more novel features of our system, including a more robust
   handling of recursion. *)