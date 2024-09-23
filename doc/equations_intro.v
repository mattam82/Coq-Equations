(** printing funelim %\coqdoctac{funelim}% *)
(** printing Derive %\coqdockw{Derive}% *)
(** printing Signature %\coqdocind{Signature}% *)
(** printing NoConfusion %\coqdocind{NoConfusion}% *)
(** printing simp %\coqdoctac{simp}% *)
(** printing <= %$\Leftarrow$% *)
(** printing <=? %$\le?$% *)

(** [Equations] is a plugin for %\cite{Coq}% that comes with a few support modules defining
   classes and tactics for running it. We will introduce its main
   features through a handful of examples. We start our Coq primer
   session by importing the [Equations] module.  *)

From Stdlib Require Import Arith Lia Program.
From Equations Require Import Equations.

(* begin hide *)
Check @eq.
Require Import Bvector.

(* Derive DependentElimination for nat bool option sum Datatypes.prod list *)
(* end hide *)

(** * Inductive types

   In its simplest form, [Equations] allows to define functions on inductive datatypes.
   Take for example the booleans defined as an inductive type with two constructors [true] and [false]:
   [[
   Inductive bool : Set := true : bool | false : bool 
   ]]
   
   We can define the boolean negation as follows: *)

Equations neg (b : bool) : bool :=
neg true := false;
neg false := true.

(* begin hide *)
Check neg_graph.
Check neg_graph_equation_1.
Check neg_graph_equation_2.

Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b. funelim (neg b); now simp neg. Defined.
(* end hide *)
(** [Equations] declarations are formed by a signature definition and a set of _clauses_ 
   that must form a _covering_ of this signature. The compiler is then expected to
   automatically find a corresponding case-splitting tree that implements the function.
   In this case, it simply needs to split on the single variable [b] to
   produce two new _programming problems_ [neg true] and [neg false] that are directly 
   handled by the user clauses. We will see in more complex examples that this search
   for a splitting tree may be non-trivial. *)

(** * Reasoning principles

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
Inductive neg_ind : bool -> bool -> Prop :=
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
   
   * Building up

   ** Polymorphism
   
   Coq's inductive types can be parameterized by types, giving polymorphic datatypes.
   For example the list datatype is defined as:
   *)

Inductive list {A} : Type := nil : list | cons : A -> list -> list.

Arguments list : clear implicits.
Notation "x :: l" := (cons x l). 
Notation "[]" := nil.

(** No special support for polymorphism is needed, as type arguments are treated 
   like regular arguments in dependent type theories. Note however that one cannot
   match on type arguments, there is no intensional type analysis.
   We can write the polymorphic [tail] function as follows:
*)

Equations tail {A} (l : list A) : list A :=
tail nil := nil ;
tail (cons a v) := v.

(** Note that the argument [{A}] is declared implicit and must hence be
 omitted in the defining clauses. In each of the branches it is named
 [A]. To specify it explicitely one can use the syntax [(A:=B)],
 renaming that implicit argument to [B] in this particular case *)

(** ** Recursive inductive types
   
   Of course with inductive types comes recursion. Coq accepts a subset
   of the structurally recursive definitions by default (it is
   incomplete due to its syntactic nature). We will use this as a first
   step towards a more robust treatment of recursion via well-founded
   relations. A classical example is list concatenation: *)

Equations app {A} (l l' : list A) : list A :=
app nil l' := l' ;
app (cons a l) l' := cons a (app l l').

(** Recursive definitions like [app] can be unfolded easily so proving the 
   equations as rewrite rules is direct. The induction principle associated 
   to this definition is more interesting however. We can derive from it the 
   following _elimination_ principle for calls to [app]: [[
   app_elim :
   forall P : forall (A : Type) (l l' : list A), list A -> Prop,
   (forall (A : Type) (l' : list A), P A nil l' l') ->
   (forall (A : Type) (a : A) (l l' : list A),
   P A l l' (app l l') -> P A (a :: l) l' (a :: app l l')) ->
   forall (A : Type) (l l' : list A), P A l l' (app l l') ]]
  Using this eliminator, we can write proofs exactly following the 
  structure of the function definition, instead of redoing the splitting 
  by hand. This idea is already present in the [Function] package 
  %\cite{Barthe:2006gp}% that derives induction principles from
  function definitions.
 *)

(* begin hide *)
Check app_graph. Check @app_graph_equation_1. Check @app_graph_equation_2.
(* end hide *)

(** ** Moving to the left

   The structure of real programs is richer than a simple case tree on
   the original arguments in general. In the course of a computation, we
   might want to scrutinize intermediate results (e.g. coming from
   function calls) to produce an answer. This literally means adding a
   new pattern to the left of our equations made available for further
   refinement. This concept is know as with clauses in the Agda
   %\cite{norell:thesis}% community and was first presented and
   implemented in the Epigram language
   %\cite{DBLP:journals/jfp/McBrideM04}%.

   The compilation of with clauses and its treatment for generating
   equations and the induction principle are quite involved in the
   presence of dependencies, but the basic idea is to add a new case
   analysis to the program. To compute the type of the new subprogram,
   we actually abstract the discriminee term from the expected type of
   the clause, so that the type can get refined in the subprogram. In
   the non-dependent case this does not change anything though.

   Each [with] node generates an auxiliary definition from the clauses
   in the curly brackets, taking the additional object as argument. The
   equation for the with node will simply be an indirection to the
   auxiliary definition and simplification will continue as usual with
   the auxiliary definition's rewrite rules.  *)

Equations filter {A} (l : list A) (p : A -> bool) : list A :=
filter nil p := nil ;
filter (cons a l) p with p a => {
  filter (cons a l) p true := a :: filter l p ;
  filter (cons a l) p false := filter l p }.

(** By default, equations makes definitions opaque after definition,
    to avoid spurious unfoldings, but this can be reverted on a case by case
    basis, or using the global [Set Equations Transparent] option. *)
Global Transparent filter.

(** A more compact syntax can be used to avoid repeating the same patterns in multiple clauses and 
  focus on the patterns that matter. When a clause starts with `|`, a list of patterns separated by "," or "|" 
  can be provided in open syntax, without parentheses. They should match the explicit arguments of the 
  current problem. Under a `with` node, they should match the variable(s) introduced by the `with` construct.
  When using "|", the ";" at the end of a clause becomes optional. *)

Equations filter' {A} (l : list A) (p : A -> bool) : list A :=
 | [], p => []
 | a :: l, p with p a => {
  | true  => a :: filter' l p
  | false => filter' l p }.

(** A common use of with clauses is to scrutinize recursive results like the following: *)

Equations unzip {A B} (l : list (A * B)) : list A * list B :=
unzip nil := (nil, nil) ;
unzip (cons p l) with unzip l => {
  unzip (cons (pair a b) l) (pair la lb) := (a :: la, b :: lb) }.

(** The real power of with however comes when it is used with dependent types. *)

(** * Dependent types
   
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
equal (S n) (S m) with equal n m := {
  equal (S n) (S ?(n)) (left eq_refl) := left eq_refl ;
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

Equations head {A} (l : list A) (pf : l <> nil) : A :=
head nil pf with pf eq_refl := { | ! };
head (cons a v) _ := a.

(** We decompose the list and are faced with two cases:

   - In the first case, the list is empty, hence the proof [pf] of type
     [nil <> nil] allows us to derive a contradiction by applying it to
     reflexivity.  We make use of another category of left-hand sides,
     which we call _empty_ patterns, denoted with [!] to inform the compiler 
     that the type of the variable is empty in this case.  In general we cannot
     expect the compiler to find by himself that the context contains a
     contradiction, as it is undecidable
     %(\cite{DBLP:conf/plpv/Oury07,DBLP:conf/birthday/GoguenMM06})%.

     However, in this case, one could also write an empty set of clauses
     for the [with] subprogram, as Equations applies a heuristic in case
     of an empty set of clause: it tries to split each of the variables
     in the context to find an empty type.

   - In the second case, we simply return the head of the list,
     disregarding the proof.  *)

(** ** Inductive families

   The next step is to make constraints such as non-emptiness part of the 
   datatype itself. This capability is provided through inductive families in
   Coq %\cite{paulin93tlca}%, which are a similar concept to the generalization 
   of algebraic datatypes to GADTs in functional languages like Haskell 
   %\cite{GADTcomplete}%. Families provide a way to associate to each constructor 
   a different type, making it possible to give specific information about a value 
   in its type. 

   *** Equality 
   The alma mater of inductive families is the propositional equality 
   [eq] defined as: [[
Inductive eq (A : Type) (x : A) : A -> Prop := 
 eq_refl : eq A x x. ]]
   
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
eqt x ?(x) ?(x) eq_refl eq_refl := eq_refl.

(** Let us explain the meaning of the non-linear patterns here that we
   slipped through in the [equal] example. By pattern-matching on the
   equalities, we have unified [x], [y] and [z], hence we determined the
   _values_ of the patterns for the variables to be [x]. The [?(x)]
   notation is essentially denoting that the pattern is not a candidate
   for refinement, as it is determined by another pattern. This
   particular patterns are called "inaccessible". When they are variables
   the inaccessibility annotation is optional.

   *** Indexed datatypes
   
   Functions on [vector]s provide more stricking examples of this
   situation.  The [vector] family is indexed by a natural number
   representing the size of the vector: [[ Inductive vector (A : Type) :
   nat -> Type := | Vnil : vector A O | Vcons : A -> forall n : nat,
   vector A n -> vector A (S n) ]]

   The empty vector [Vnil] has size [O] while the cons operation
   increments the size by one. Now let us define the usual map on
   vectors: *)
Arguments Vector.nil {A}.
Arguments Vector.cons {A} a {n} v : rename.

Notation vector := Vector.t.
Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.

Equations vmap {A B} (f : A -> B) {n} (v : vector A n) :
  vector B n :=
vmap f (n:=?(0)) Vnil := Vnil ;
vmap f (Vcons a v) := Vcons (f a) (vmap f v).

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

Equations vtail {A n} (v : vector A (S n)) : vector A n :=
vtail (Vcons a v') := v'.

(** The type of [v] ensures that [vtail] can only be applied to 
   non-empty vectors, moreover the patterns only need to consider 
   constructors that can produce objects in the subfamily [vector A (S n)],
   excluding [Vnil]. The pattern-matching compiler uses unification 
   with the theory of constructors to discover which cases need to 
   be considered and which are impossible. In this case the failed 
   unification of [0] and [S n] shows that the [Vnil] case is impossible.
   This powerful unification engine running under the hood permits to write
   concise code where all uninteresting cases are handled automatically. *)

(** ** Derived notions, No-Confusion

    For this to work smoothlty, the package requires some derived definitions
    on each (indexed) family, which can be generated automatically using
    the generic [Derive] command. Here we ask to generate the signature,
    heterogeneous no-confusion and homogeneous no-confusion principles for vectors: *)

Derive NoConfusion for nat.
Derive Signature NoConfusion NoConfusionHom for vector.

(** The precise specification of these derived definitions can be found in the manual
    section %(\S \ref{manual})%. Signature is used to "pack" a value in an inductive family
    with its index, e.g. the "total space" of every index and value of the family. This
    can be used to derive the heterogeneous no-confusion principle for the family, which
    allows to discriminate between objects in potentially different instances/fibers of the family,
    or deduce injectivity of each constructor. The [NoConfusionHom] variant derives
    the homogeneous no-confusion principle between two objects in the _same_ instance
    of the family, e.g. to simplify equations of the form [Vnil = Vnil :> vector A 0].
    This last principle can only be defined when pattern-matching on the inductive family
    does not require the [K] axiom and will otherwise fail.

   ** Unification and indexed datatypes

   Back to our example, of course the equations and the induction principle are simplified in a
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


Equations diag {A n} (v : vector (vector A n) n) : vector A n :=
diag (n:=O) Vnil := Vnil ;
diag (n:=S _) (Vcons (Vcons a v) v') :=
  Vcons a (diag (vmap vtail v')).

(** Here in the second equation, we know that the elements of the vector
   are necessarily of size [S n] too, hence we can do a nested refinement
   on the first one to find the first element of the diagonal.
  *)

(** ** Recursion

  Notice how in the [diag] example above we explicitely pattern-matched
  on the index [n], even though the [Vnil] and [Vcons] pattern matching
  would have been enough to determine these indices. This is because the
  following definition also fails: *)

Fail Equations diag' {A n} (v : vector (vector A n) n) : vector A n :=
diag' Vnil := Vnil ;
diag' (Vcons (Vcons a v) v') :=
  Vcons a (diag' (vmap vtail v')).

(** Indeed, Coq cannot guess the decreasing argument of this fixpoint
    using its limited syntactic guard criterion: [vmap vtail v'] cannot
    be seen to be a (large) subterm of [v'] using this criterion, even
    if it is clearly "smaller". In general, it can also be the case that
    the compilation algorithm introduces decorations to the proof term
    that prevent the syntactic guard check from seeing that the
    definition is structurally recursive.

    To aleviate this problem, [Equations] provides support for
    _well-founded_ recursive definitions which do not rely on syntactic
    checks.

    The simplest example of this is using the [lt] order on natural numbers
    to define a recursive definition of identity: *)

Equations id (n : nat) : nat by wf n lt :=
  id 0 := 0;
  id (S n') := S (id n').

(** Here [id] is defined by well-founded recursion on [lt] on the (only)
    argument [n] using the [by wf] annotation.  At recursive calls of
    [id], obligations are generated to show that the arguments
    effectively decrease according to this relation.  Here the proof
    that [n' < S n'] is discharged automatically.

  Wellfounded recursion on arbitrary dependent families is not as easy
  to use, as in general the relations on families are _heterogeneous_,
  as they must relate inhabitants of potentially different instances of
  the family.  [Equations] provides a [Derive] command to generate the
  subterm relation on any such inductive family and derive the
  well-foundedness of its transitive closure. This provides
  course-of-values or so-called "mathematical" induction on these
  objects, reflecting the structural recursion criterion in the logic. *)

Derive Subterm for vector.

(** For vectors for example, the relation is defined as: [[
Inductive t_direct_subterm (A : Type) :
  forall n n0 : nat, vector A n -> vector A n0 -> Prop :=
    t_direct_subterm_1_1 : forall (h : A) (n : nat) (H : vector A n),
      t_direct_subterm A n (S n) H (Vcons h H) ]]

  That is, there is only one recursive subterm, for the subvector
  in the [Vcons] constructor. We also get a proof of:
 *)

Check well_founded_t_subterm : forall A, WellFounded (t_subterm A).

(** The relation is actually called [t_subterm] as [vector] is just
    a notation for [Vector.t].
    [t_subterm] itself is the transitive closure of the relation seen as
    an homogeneous one by packing the indices of the family with the
    object itself. Once this is derived, we can use it to define
    recursive definitions on vectors that the guard condition couldn't
    handle. The signature provides a [signature_pack] function to pack a
    vector with its index. The well-founded relation is defined on the
    packed vector type. *)

Module UnzipVect.
  Context {A B : Type}.

  (** We can use the packed relation to do well-founded recursion on the vector.
      Note that we do a recursive call on a substerm of type [vector A n] which
      must be shown smaller than a [vector A (S n)]. They are actually compared
      at the packed type [{ n : nat & vector A n}]. The default obligation
      tactic defined in [Equations.Init] includes a proof-search
      for [subterm] proofs which can resolve the recursive call obligation
      automatically in this case. *)

  Equations unzip {n} (v : vector (A * B) n) : vector A n * vector B n
    by wf (signature_pack v) (@t_subterm (A * B)) :=
  unzip Vnil := (Vnil, Vnil) ;
  unzip (Vector.cons (pair x y) v) with unzip v := {
  | pair xs ys := (Vector.cons x xs, Vector.cons y ys) }.

End UnzipVect.

(** For the diagonal, it is easier to give [n] as the decreasing argument
    of the function, even if the pattern-matching itself is on vectors: *)

Equations diag' {A n} (v : vector (vector A n) n) : vector A n by wf n :=
diag' Vnil := Vnil ;
diag' (Vcons (Vcons a v) v') :=
  Vcons a (diag' (vmap vtail v')).

(** One can check using [Extraction diag'] that the computational behavior of [diag']
    is indeed not dependent on the index [n]. *)

(** *** Pattern-matching and axiom K *)

(** To use the K axiom or UIP with [Equations], one _must_ first set an option
    allowing its use during dependenet pattern-matching compilation. *)

Module KAxiom.

  (** By default we disallow the user of UIP, but it can be set. *)

  Set Equations With UIP.

  Module WithAx.

    (** The user must declare this axiom itself, as an instance of the [UIP] class. *)

    Axiom uipa : forall A, UIP A.
    Local Existing Instance uipa.

    (** In this case the following definition uses the [UIP] axiom just declared. *)

    Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl)
              (H : x = x) : P H :=
      K x P p eq_refl := p.

  End WithAx.

  (** Note that the definition loses its computational content: it will
      get stuck on an axiom. We hence do not recommend its use.

      Equations allows however to use constructive proofs of UIP for types
      enjoying decidable equality. The following example relies on an
      instance of the [EqDec] typeclass for natural numbers, from which
      we can automatically derive a [UIP nat] instance.  Note that
      the computational behavior of this definition on open terms is not
      to reduce to [p] but pattern-matches on the decidable equality
      proof.  However the defining equation still holds as a
      _propositional_ equality, and the definition of K' is axiom-free. *)

  Equations K' (x : nat) (P : x = x -> Type) (p : P eq_refl)
            (H : x = x) : P H :=
    K' x P p eq_refl := p.

  Print Assumptions K'.
  (* Closed under the global context *)

End KAxiom.

(** *** Options

  [Equations] supports the following attributes:
  
  - [universes(polymorphic | monomorphic)] for universe polymorphic or
    monomorphic definitions (also depending on the global `Universe Polymorphism` flag).

  - [tactic=tac] for setting the default tactic to try solve obligations/holes.
    By default this reuses the `Obligation Tactic` of Program.

  - [derive(eliminator=yes|no, equations=yes|no)] to control the derivation of 
    the graph and elimination principle for the function, and the propositional 
    equalities of the definition. Note that `eliminator=yes` forces `equations=yes`.

*)