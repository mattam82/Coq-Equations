(** printing now %\coqdoctac{now}% *)
(** printing elimination %\coqdoctac{elimination}% *)
(** printing Hint %\coqdockw{Hint}% *)
(** printing Rewrite %\coqdockw{Rewrite}% *)
(** printing Program %\name{Program}% *)
(** printing <= %\rightarrow% #⇐# *)
(** printing funelim %\coqdoctac{funelim}% *)
(** printing Derive %\coqdockw{Derive}% *)
(** printing Signature %\coqdocind{Signature}% *)
(** printing NoConfusion %\coqdocind{NoConfusion}% *)
(** printing simp %\coqdoctac{simp}% *)
(** printing <= %$\Leftarrow$% *)
(** printing <=? %$\le?$% *)
(* begin hide *)

Set Warnings "-notation-overridden".
Require Import Utf8 Arith Compare_dec List Lia.
Require Import Relation_Operators Program.

Close Scope program_scope.
Close Scope list_scope.
Arguments map {A B}.

(* end hide *)

(** [Equations] is a plugin for %\cite{Coq}% that comes with a few support modules defining
   classes and tactics for running it. We will introduce its main
   features through a handful of examples. We start our Coq primer
   session by importing the [Equations] module.  *)

From Equations.Prop Require Import Equations.

(* begin hide *)
Close Scope list_scope.
Set Equations Transparent.
Import EquationsNotations.
Local Open Scope equations_scope.
Extraction Inline Logic.transport.
(* end hide *)

(** * Inductive types

  In its simplest form, [Equations] allows to define functions on inductive datatypes.
  Take for example the booleans defined as an inductive type with two constructors 
  [true] and [false]:
  [[
  Inductive bool : Set := true : bool | false : bool 
  ]]
  
  We can define the boolean negation as follows: *)

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.

(** [Equations] declarations are formed by a signature definition and a set of _clauses_ 
  that must form a _covering_ of this signature. The compiler is then expected to
  automatically find a corresponding case-splitting tree (i.e. [match .. with])  
  that implements the function.
  In this case, it simply needs to split on the single variable [b] to
  produce two new _programming problems_ [neg true] and [neg false] that are directly 
  handled by the user clauses. We will see in more complex examples that this search
  for a splitting tree may be non-trivial. *)

Print neg.


(** * Reasoning principles

  In the setting of a proof assistant like Coq, we need not only the ability 
  to define complex functions but also get good reasoning support for them.
  Practically, this translates to the ability to simplify applications of functions 
  appearing in the goal and to give strong enough proof principles for (recursive)
  definitions.

  ** Rewrite rules

  [Equations] provides this through an automatic generation of proofs related to
  the function. Namely, each defining equation gives rise to a lemma stating the 
  equality between the left and right hand sides. These equations can be used as 
  rewrite rules for simplification during proofs, without having to rely on the
  fragile simplifications implemented by raw reduction. *)
  
Lemma negb_invol : 
  forall b, neg (neg b) = b.
Proof.
  destruct b. rewrite neg_equation_1.
  all:simp neg. all:easy.
Qed.

(** The [simp foo] tactic is an alias to [autorewrite with foo], using the rewrite 
  rules associated to constant foo. *)

(** ** Elimination principle

  We can also generate the inductive graph of any [Equations] definition, 
  giving the strongest elimination principle on the function. 

  I.e., for [neg] the inductive graph is defined as: [[
Inductive neg_graph : bool -> bool -> Set :=
| neg_graph_equation_1 : neg_graph true false
| neg_graph_equation_2 : neg_graph false true ]]

  Along with a proof of [neg_graph_correct : ∀ b, neg_graph b (neg b)], we can 
  eliminate any call to [neg] specializing its argument and result in a single command.

  Suppose we want to show that [neg] is involutive for example, our goal will 
  look like: [[
  b : bool
  ============================
  neg (neg b) = b ]]
  
  An application of the tactic [funelim (neg b)] will produce two goals corresponding to 
  the splitting done in [neg]: [neg false = true] and [neg true = false].
  These correspond exactly to the rewriting lemmas generated for [neg].

  In the following sections we will show how these ideas generalize to more complex 
  types and definitions involving dependencies, overlapping clauses and recursion. *)

Print neg_graph.
Check neg_graph_correct.

Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b. funelim (neg b). all:now reflexivity. Defined.

Module BuildingUp.

(** Equations naturally supports notations: the left-hand 
  sides of clauses only have to be elaborated to well-typed patterns for the given argument types. *)

Notation "[]" := nil : mylist_scope.
Notation "[ x ]" := (cons x nil) : mylist_scope.
Notation "x :: l" := (cons x l) : mylist_scope.
Open Scope mylist_scope.

(** ** Recursive inductive types
  
  Of course with inductive types comes recursion. Coq accepts a subset
  of the structurally recursive definitions by default (it is
  incomplete due to its syntactic nature). We will use this as a first
  step towards a more robust treatment of recursion via well-founded
  relations. A classical example is list concatenation: *)

  (** *** Recursive notations

  One can also define notations for recursive definitions, by
  first _reserving_ them:
*)

Reserved Notation "x +++ y" (at level 60, right associativity).

(** Here we declare [x ++ y] as an infix operation with right associativity,
  so [x ++ y ++ z] will mean [x ++ (y ++ z)]. *)

Equations app {A} (l l' : list A) : list A := {
  nil      +++ l' := l' ;
  (a :: l) +++ l' := a :: (l +++ l') }
where "x +++ y" := (app x y).

(** We can directly bind and use this notation to write the left-hand side
  and right-hand sides of the program.

  Remark: We enclose the clauses around curly braces, to scope the notation around the
  whole program. Otherwise the notation [where] clause would only apply to the body
  of the second branch. *)

(** *** Functional elimination and recursion 

  Recursive definitions like [app] can be unfolded easily so proving the 
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
  and recursion. This idea is already present in the [Function] package 
  %\cite{Barthe:2006gp}% that derives induction principles from
  function definitions.

  In the example below we can see that we get an instantiated induction
  hypothesis corresponding to the recursive call to [app] in the [_ :: _] branch.
*)

About app_elim.

Lemma app_assoc {A} (x y z : list A) :
  x +++ y +++ z = (x +++ y) +++ z.
Proof.
  funelim (x +++ y); simpl; auto.
  now rewrite H. 
Qed.

Lemma app_nil_r {A} (l : list A) : 
 l +++ [] = l.
Proof. funelim (l +++ []); auto. now rewrite H. Qed.

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

Equations filter {A} (l : list A) 
  (p : A -> bool) : 
  list A :=
filter [] p := [] ;
filter (a :: l) p with (p a) => {
  | true := a :: filter l p ;
  | false := filter l p }.

(** *** Elimination principle 

  Introduction of these intermediate computations are also reflected
  in the elimination principle: the motive for elimination of each 
  subprogram is augmented with an equality proof between the new 
  argument variable and the effective argument it is called with (here
  [p a]). We have three subgoals corresponding to the leaves (right-hand sides) 
  of the program. *)

Lemma filter_true {A} (l : list A) :
  filter l (fun x => true) = l.
Proof.
  funelim (filter l (fun _ => true)).
  - (* [l = []] *) reflexivity.
  - (* [l = (a :: l)] and [(fun x => true) a = true] *)
    simpl. now rewrite H.
  - (* [l = (a :: l)] and [(fun x => true) a = false] *) 
    discriminate.
Qed.
   
(** ** Auxiliary local functions

  A common idiom of functional programming is the worker/wrapper
  pattern. It usually involves a recursive function that computes the
  result, wrapped in a toplevel function calling it with specific
  parameters. The paradigmatic example is probably list reversal,
  whose tail-recursive version can be written using a recursive local
  where clause: *)

Equations rev_acc {A} (l : list A) : list A :=
  rev_acc l := go l []
   where go : 
     list A -> list A -> list A :=
         go [] acc := acc;
         go (hd :: tl) acc := go tl (hd :: acc).

(** The [where] clause acts like [where] in Haskell or Agda,
  or [let] in OCaml:
  it defines an auxilliary function or value, which might use more pattern-matching 
  and be recursive itself. The auxilliary function's scope is the body of the program
  which comes _before_ the [where], here [go l []]. *)

(** A typical issue with such accumulating functions is 
  that one has to write lemmas in two versions to prove properties about them, once about the internal [go] function and then on its wrapper. Using the functional elimination principle associated to [rev_acc], we can show both properties simultaneously.

  First, lets define the usual list reversal function,
  which is not tail recursive and might hence incur stack overflows on large lists: *)

Equations rev {A} (l : list A) : list A :=
rev [] := [];
rev (a :: l) := rev l +++ [a].

Lemma rev_acc_eq : forall {A} (l : list A), 
  rev_acc l = rev l.
Proof. 
  (** We apply functional elimination on the [rev_acc l]  call. The eliminator expects two predicates:
  one for the wrapper and another for the worker.
  For the wrapper, we give the expected final goal but for the worker we have to invent a kind of loop invariant: here that the result of the whole [go acc l] call is equal to [rev l ++ acc]. *)

  apply (rev_acc_elim 
    (fun A l revaccl => revaccl = rev l)
    (fun A _ l acc go_res => 
      go_res = rev l +++ acc)).
  all:intros A l; simpl; trivial.

  (** Functional elimination provides us with the worker
    property for the initial [go [] l] call, i.e. that it is equal to [rev l ++ []], which trivially gives us the result. *)

  + intros IH. now rewrite app_nil_r in IH.
  + (* For the worker proof itself, the result follows from associativity of 
      list concatenation and the induction hypothesis. *)
    intros a l1 l' IH.
    rewrite <- app_assoc. simpl. assumption.
Qed.

(** *** The Worker/Wrapper and Well-Founded Recursion

  Sometimes the natural expression of an algorithm in the worker/wrapper
  pattern requires well-founded recursion: here we take an example
  algorithm translated from Haskell whose termination is justified by a measure.
  Note that the [worker] subprogram's termination measure and
  implementation depends on the enclosing [k] argument which is captured
  in the where clause. Termination is justified by a simple arithmetic argument. *)
  
  Local Obligation Tactic := idtac.
  
  Equations? isPrime (n : nat) : bool :=
  isPrime 0 := false; 
  isPrime 1 := false;
  isPrime 2 := true;
  isPrime k := worker 2
    where worker (n' : nat) : bool by wf (k - n') lt :=
    worker n' with ge_dec n' k :=
      { | left H := true;
        | right H := 
        if Nat.eqb (Nat.modulo k n') 0 then false 
        else worker (S n') }.
Proof. lia. (* Linear arithmetic reasoning *) Qed.

Import ListNotations.

Eval vm_compute in map isPrime [13; 14; 28; 29].

End BuildingUp.

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

(** ** Inductive families

  The next step is to make constraints such as non-emptiness part of the 
  datatype itself. This ability is provided through inductive families in
  Coq %\cite{paulin93tlca}%, which are a similar concept to the generalization 
  of algebraic datatypes to GADTs in functional languages like Haskell 
  %\cite{GADTcomplete}%. Families provide a way to associate to each constructor 
  a different type, making it possible to give specific information about a value 
  in its type. 

  *** Indexed datatypes
  
  Functions on [vec]s provide more stricking examples of this
  situation.  The [vec] family is indexed by a natural number
  representing the size of the vector: *)

Module Vector.

Inductive vec (A : Type) : nat -> Type :=
| nil : vec A 0
| cons n : A -> vec A n -> vec A (S n).

Derive Signature for vec.

(** 
  The empty vector [nil] has size [O] while the cons operation
  increments the size by one. We declare notations similar to lists
  on vectors, as the size information will generally be left _implicit_. *)

Arguments nil {A}.
Arguments cons {A n}.

Notation "x :: v" := (cons x v) : vector_scope.
Notation "[ ]" := nil : vector_scope.
Notation "[ x ]" := (cons x nil) : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) .. )) : vector_scope.

End Vector.
Import Vector.
Local Open Scope vector_scope.

(** Now let us define the usual map on vectors. *)
Equations map {A B} (f : A -> B) {n} (v : vec A n) : 
  vec B n :=
map f (n:=?(0)) [] := [] ;
map f (a :: v) := f a :: map f v.

Print map.

(** Here the value of the index representing the size of the vector 
  is directly determined by the constructor, hence in the case tree
  we have no need to eliminate [n]. This means in particular that 
  the function [map] does not do any computation with [n], and 
  the argument could be eliminated in the extracted code.
  In other words, it provides only _logical_ information about 
  the shape of [v] but no computational information.

  The [map] function works on every member of the [vec] family,
  but some functions may work only for some subfamilies, for example
  [tail]:
*)

Equations tail {A n} (v : vec A (S n)) : vec A n :=
tail (a :: v') := v'.

(** The type of [v] ensures that [tail] can only be applied to 
  non-empty vectors, moreover the patterns only need to consider 
  constructors that can produce objects in the subfamily [vec A (S n)],
  excluding [nil]. The pattern-matching compiler uses unification 
  with the theory of constructors to discover which cases need to 
  be considered and which are impossible. In this case the failed 
  unification of [0] and [S n] shows that the [nil] case is impossible.
  This powerful unification engine running under the hood permits to write
  concise code where all uninteresting cases are handled automatically. *)

Equations head {A n} (v : vec A (S n)) : A :=
head (a :: v') := a.
  
(** ** Derived notions, No-Confusion

    For this to work smoothlty, the package requires some derived definitions
    on each (indexed) family, which can be generated automatically using
    the generic [Derive] command. Here we ask to generate the homogeneous no-confusion principles for vectors: *)

Derive NoConfusionHom for vec.

Equations noconf {A n} (v v' : vec A n) : Prop :=
noconf [] [] := True;
noconf (a :: v) (a' :: v') := (a = a' /\ v = v').

(* + proof that [v = v' <~> noconf v v'] *)

(** The precise specification of these derived definitions can be found in the manual
    section %(\S \ref{manual})%. Signature is used to "pack" a value in an inductive family
    with its index, e.g. the "total space" of every index and value of the family. This
    can be used to derive the heterogeneous no-confusion principle for the family, which
    allows to discriminate between objects in potentially different instances/fibers of the family,
    or deduce injectivity of each constructor. 
    
    The [NoConfusionHom] variant derives
    the homogeneous no-confusion principle between two objects in the _same_ instance
    of the family, e.g. to simplify equations of the form [nil = nil :> vec A 0].
    This last principle can only be defined when pattern-matching on the inductive family
    does not require the [K] axiom and will otherwise fail.

  ** Unification and indexed datatypes

  Back to our example, of course the equations and the induction principle are simplified in a
  similar way. If we encounter a call to [tail] in a proof, we can 
  use the following elimination principle to simplify both the call and the
  argument which will be automatically substituted by an object of the form
  [cons _ _ _]:[[
forall P : forall (A : Type) (n : nat), vec A (S n) -> vec A n -> Prop,
(forall (A : Type) (n : nat) (a : A) (v : vec A n), 
  P A n (a :: v) v) ->
forall (A : Type) (n : nat) (v : vec A (S n)), P A n v (tail v) ]] 

  As a witness of the power of the unification, consider the following function 
  which computes the diagonal of a square matrix of size [n * n].
*) 

Equations diag {A n} (v : vec (vec A n) n) : vec A n :=
diag (n:=O) [] := [] ;
diag (n:=S _) ((a :: v) :: v') :=
   a :: diag (map tail v').

(** Here in the second equation, we know that the elements
  of the vector are necessarily of size [S n] too, hence 
  we can do a nested refinement on the first one to find
  the first element of the diagonal.
  *)

(** ** Recursion on indexed families

  Notice how in the [diag] example above we explicitely pattern-matched
  on the index [n], even though the [nil] and [cons] pattern matching
  would have been enough to determine these indices. This is because the
  following definition also fails: *)

Fail Equations diag' {A n} (v : vec (vec A n) n) : vec A n :=
diag' [] := [] ;
diag' ((a :: v) :: v') := a :: diag' (map tail v').

(** Indeed, Coq cannot guess the decreasing argument of this fixpoint
    using its limited syntactic guard criterion: [map tail v'] cannot
    be seen to be a (large) subterm of [v'] using this criterion, even
    if it is clearly "smaller". In general, it can also be the case that
    the compilation algorithm introduces decorations to the proof term
    that prevent the syntactic guard check from seeing that the
    definition is structurally recursive.

    To aleviate this problem, [Equations] provides support for
    _well-founded_ recursive definitions which do not rely on syntactic
    checks.

    ** Wellfounded recursion 

  For the diagonal, it is easier to give [n] as the decreasing argument
  of the function, even if the pattern-matching itself is on vectors: *)

Equations diag' {A n} (v : vec (vec A n) n) : 
  vec A n by wf n :=
diag' [] := [] ;
diag' ((a :: v) :: v') := a :: diag' (map tail v').

(* Unfolding lemma *)
Check diag'_unfold_eq.
Check diag'_elim.

(** One can check using [Extraction diag'] that the
  computational behavior of [diag'] is indeed not
  dependent on the index [n]. *)

Extraction diag'.

(** To go further and implement a safe lookup function on vectors,
  we introduce an inductive definition of bounded natural numers [fin n].
  [fin n] represents the interval [ (0..n] ]. 
*)

Inductive fin : nat -> Set :=
  | f0 : forall n, fin (S n)
  | fS : forall n, fin n -> fin (S n).

Derive Signature NoConfusionHom for fin.

Arguments f0 {n}.
Arguments fS {n}.

(** For example, [fin 3] has the following inhabitants: *)

Check f0 : fin 3.
Check fS f0 : fin 3.
Check fS (fS f0) : fin 3.

(** But [fS (fS (fS f0))] is not an inhabitant of [fin 3]: *)

Fail Check fS (fS (fS f0)) : fin 3.

(** We can hence prove that [fin 0] is not inhabited: *)
Equations fin0 : fin 0 -> False := 
  fin0 !.

(** Our safe lookup can now be concisely written: it takes
  an index that must be within the bounds of the vector. *)

Equations nth {A} {n} (v : vec A n) (f : fin n) : A := 
nth (a :: v) f0 := a;
nth (_ :: v) (fS f) := nth v f.

Equations fin_eq {n} (f g : fin n) : 
   { f = g } + { f <> g } :=
fin_eq f0 f0 := left eq_refl;
fin_eq (n:=?(S n')) (fS f) (fS (n:=n') f') 
  with fin_eq f f' := 
  { fin_eq (fS f) (fS ?(f)) (left eq_refl) => left eq_refl;
    fin_eq (fS f) (fS f') (right p) => right _ };
fin_eq x y := right _.

Extraction fin_eq.

(** ** Dependent elimination tactics 
   
  Alternatively to writing dependent pattern-matching programs, 
  we can also use dependent elimination whenever needed 
  in proof mode using the [depelim] and [dependent elimination] tactics
  provided by Equations. *)

Goal fin 0 -> False.
Proof.
  intros f.
  depelim f.
Qed.

Lemma vec_eq_dec {A n} `{EqDec A} (v w : vec A n) : { v = w } + { v <> w }.
Proof.
  induction v.




























  - dependent elimination w.
    left; auto.
  - dependent elimination w as [@cons n a' v']. 
    destruct (eq_dec a a') as [->|na].
    destruct (IHv v') as [->|nv].
    left; auto.
    right; intros eq.
    inversion eq. Undo.
    noconf eq. contradiction.
    right; intro eq. congruence.
Qed.

Print Assumptions vec_eq_dec.


(*** Equality 
The alma mater of inductive families is the propositional equality 
[eq] defined as: [[
Inductive eq (A : Type) (x : A) : A -> Prop := 
eq_refl : eq A x x. ]] 
*)

Print eq.

(** 
Equality is a polymorphic relation on [A]. The [Prop] sort (or kind) categorizes
propositions, while the [Set] sort, equivalent to $\star$ in Haskell, categorizes 
computational types. 

Equality is _parameterized_ by a value [x] of type [A] and 
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

Equations eqt {A} (x y z : A) (p : x = y) (q : y = z) : 
  x = z :=
eqt x ?(x) ?(x) eq_refl eq_refl := eq_refl.

(** Let us explain the meaning of the non-linear patterns here that we
slipped through in the [equal] example. By pattern-matching on the
equalities, we have unified [x], [y] and [z], hence we determined the 
_values_ of the patterns for the variables to be [x]. The [?(x)]
notation is essentially denoting that the pattern is not a candidate
for refinement, as it is determined by another pattern. This
particular patterns are called _inaccessible_. When they are variables
the inaccessibility annotation is optional. *)

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
    Print Assumptions K.

  End WithAx.

  (** Note that the definition loses its computational
  content: it will get stuck on an axiom. We hence do not 
  recommend its use.

  Equations allows however to use constructive proofs of 
  UIP for types enjoying decidable equality. The following 
  example relies on an instance of the [EqDec] typeclass for natural numbers, from which
      we can automatically derive a [UIP nat] instance.  Note that
      the computational behavior of this definition on open terms is not
      to reduce to [p] but pattern-matches on the decidable equality
      proof.  However t/he defining equation still holds as a
      _propositional_ equality, and the definition of K' is axiom-free. *)

  Equations K' (x : nat) (P : x = x -> Type) (p : P eq_refl)
            (H : x = x) : P H :=
    K' x P p eq_refl := p.

  Print Assumptions K'.
  (* Closed under the global context *)

End KAxiom.

Section ex.
  Variable (X : Type) (g : X -> option X).

  Inductive dns : X -> Prop :=
    dns_I x : dnso (g x) -> dns x
  with dnso : option X -> Prop :=
   | dnso_none: dnso None
   | dnso_some x : dns x -> dnso (Some x).

   Equations pidns (x : X) (d : dns x) : dnso (g x) :=
   pidns x (dns_I x d) := d.

   Equations pidnso (x : X) (d : dnso (Some x)) : dns x :=
     pidnso x (dnso_some x d) := d.

  Fixpoint mutrec (x : X) (d : dns x) : nat :=
    mut' (g x) (pidns x d)
  with mut' (x : option X) (d : dnso x) : nat :=
    match x return dnso x -> nat with
    | None => fun d => 0
    | Some x' => fun d => S (mutrec x' (pidnso x' d))
    end d.

  (*
  Equations mutrec (x : X) (d : dns x) : nat :=
    mutrec x d := mut' (g x) (pidns x d)
  with mut' (x : option X) (d : dnso x) : nat :=
    mut' None d := 0;
    mut' (Some x') d := S (mutrec x' (pidnso x' d)). 

    Next Obligation.
     depelim d. now cbn.
    Defined.
    Next Obligation.
     depelim d. now cbn.
    Defined.
    About mutrec_elim. *)

    
    
End ex.

Extraction mutrec.