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

Require Import Arith Omega.
From Equations Require Import Equations.

(* begin hide *)
Check @eq.
Require Import Bvector.

(* Derive DependentElimination for nat bool option sum prod list vector. *)
(* end hide *)

(** * Inductive types

   In its simplest form, [Equations] allows to define functions on inductive datatypes.
   Take for example the booleans defined as an inductive type with two constructors [true] and [false]:
   [[
   Inductive bool : Set := true : bool | false : bool 
   ]]
   
   We can define the boolean negation as follows: *)

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.
Print All.
(* begin hide *)
Check neg_ind.
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
 [A]. To specify it explicitely one can use the syntax [{A:=B}],
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
Check app_ind. Check @app_ind_equation_1. Check @app_ind_equation_2.
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
filter (cons a l) p <= p a => {
  filter (cons a l) p true := a :: filter l p ;
  filter (cons a l) p false := filter l p }.

(** By default, equations makes definitions opaque after definition,
    to avoid spurious unfoldings, but this can be reverted on a case by case
    basis, or using the global [Set Equations Transparent] option. *)
Global Transparent filter.

(** A common use of with clauses is to scrutinize recursive results like the following: *)

Equations unzip {A B} (l : list (A * B)) : list A * list B :=
unzip nil := (nil, nil) ;
unzip (cons p l) <= unzip l => {
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
head nil pf :=! pf;
head (cons a v) _ := a.

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
   particular patterns are called "inaccessible".

   *** Indexed datatypes
   
   Functions on [vector]s provide more stricking examples of this
   situation.  The [vector] family is indexed by a natural number
   representing the size of the vector: [[ Inductive vector (A : Type) :
   nat -> Type := | Vnil : vector A O | Vcons : A -> forall n : nat,
   vector A n -> vector A (S n) ]]

   The empty vector [Vnil] has size [O] while the cons operation
   increments the size by one. Now let us define the usual map on
   vectors: *)
Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.

Equations vmap {A B} (f : A -> B) {n} (v : vector A n) :
  vector B n :=
vmap f {n:=?(0)} Vnil := Vnil ;
vmap f {n:=?(S n)} (Vcons a n v) := Vcons (f a) (vmap f v).

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
vtail (Vcons a n v') := v'.

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

Equations diag {A n} (v : vector (vector A n) n) : vector A n :=
diag {n:=O} Vnil := Vnil ;
diag {n:=(S ?(n))} (Vcons (Vcons a n v) ?(n) v') :=
  Vcons a (diag (vmap vtail v')).

(** Here in the second equation, we know that the elements of the vector 
   are necessarily of size [S n] too, hence we can do a nested refinement
   on the first one to find the first element of the diagonal. *)

(** ** Recursion

  Notice how in the [diag] example above we explicitely pattern-matched
  on the index [n], even though the [Vnil] and [Vcons] pattern matching
  would have been enough to determine these indices. This is because the
  following definitions fails: *)

Fail Equations diag' {A n} (v : vector (vector A n) n) : vector A n :=
diag' Vnil := Vnil ;
diag' (Vcons (Vcons a n v) n v') :=
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

Require Import Equations.Subterm.

Equations id (n : nat) : nat :=
  id n by rec n lt :=
  id 0 := 0;
  id (S n') := S (id n').

(** Here [id] is defined by well-founded recursion on [lt] on the (only)
    argument [n] using the [by rec] node.  At recursive calls of [id],
    obligations are generated to show that the arguments effectively
    decrease according to this relation.  Here the proof that [n' < S
    n'] is discharged automatically.

  Wellfounded recursion on arbitrary dependent families is not as easy
  to use, as in general the relations on families are _heterogeneous_,
  as the must related inhabitants of potentially different instances of
  the family.  [Equations] provides a [Derive] command to generate the
  subterm relation on any such inductive family and derive the
  well-foundedness of its transitive closure, which is often what's
  required. This provides course-of-values or so-called "mathematical"
  induction on these objects, mimicking the structural recursion
  criterion in the logic. *)

Derive Signature Subterm for vector.

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
      at the packed type [{ n : nat & vector A n}]. *)

  Equations unzip {n} (v : vector (A * B) n) : vector A n * vector B n :=
  unzip v by rec (signature_pack v) (@t_subterm (A * B)) :=
  unzip Vnil := (Vnil, Vnil) ;
  unzip (Vector.cons (pair x y) n v) with unzip v := {
    | pair xs ys := (Vector.cons x xs, Vector.cons y ys) }.
End UnzipVect.

(* begin hide *)
Require Import Relation_Operators.
Import Sigma_Notations.
Local Open Scope equations_scope.
Require Import Relations.
Lemma clos_trans_stepr_refl A (R : relation A) (x y z : A) :
  R y z -> clos_refl _ (clos_trans A R) x y -> clos_trans A R x z.
Proof.
  intros Hyz Hxy.
  destruct Hxy. eapply clos_trans_stepr; eauto.
  now constructor.
Qed.
(* end hide *)

(** While this was just mimicking simple structural recursion, we can of
    course use this for more elaborate termination arguments. We put
    ourselves in a section to parameterize a [skip] function by a predicate: *)

Section Skip.
  Context {A : Type} (p : A -> bool).
  Equations skip_first {n} (v : vector A n) : &{ n : nat & vector A n } :=
  skip_first Vnil := &(0 & Vnil);
  skip_first (Vcons a n v') <= p a => {
                     | true => skip_first v';
                     | false => &(_ & Vcons a v') }.

  (** It is relatively straitforward to show that [skip] returns a (large) subvector of its argument *)

  Lemma skip_first_subterm {n} (v : vector A n) : clos_refl _ (t_subterm _) (skip_first v) &(_ & v).
  Proof.
    funelim (skip_first v).
    constructor 2.
    depelim H.
    constructor 1.
    eapply clos_trans_stepr. simpl.
    apply (t_direct_subterm_1_1 _ _ _ (&(_ & t).2)). apply H.
    rewrite H. constructor. eauto with subterm_relation.
    constructor 2.
  Qed.
  
End Skip.

(** This function takes an unsorted vector and returns a sorted vector corresponding to it
    starting from its head [a], removing all elements smaller than [a] and recursing.  *)

Equations sort {n} (v : vector nat n) : &{n' : _ & vector nat n'} :=
sort v by rec (signature_pack v) (t_subterm nat) :=
sort Vnil := &( _ & Vnil );
sort (Vcons a n v) := let sk := skip_first (fun x => Nat.leb x a) v in &(_ & Vcons a (sort sk.2).2).

(** Here we prove that the recursive call is correct as skip preserves the size of its argument *)

Next Obligation.
  red. simpl.
  eapply clos_trans_stepr_refl.
  simpl. apply (t_direct_subterm_1_1 _ _ _ (&(_ & v).2)).
  refine (skip_first_subterm _ _).
Qed.

(** To prove it we need a few supporting lemmas, we first write a predicate on vectors
    equivalent to [List.forall]. *)

Equations forall_vect {A} (p : A -> bool) {n} (v : vector A n) : bool :=
forall_vect _ Vnil := true;
forall_vect p (Vcons x n v) := p x && forall_vect p v.

Require Import Bool.

(** By functional elimination it is easy to prove that this respects the implication
    order on predicates *)

Lemma forall_vect_impl {A} p p' {n} (v : vector A n)
      (fp : forall x, p x = true -> p' x = true) :
  forall_vect p v = true -> forall_vect p' v = true.
Proof.
  funelim (forall_vect p v). auto.
  simp forall_vect. rewrite !andb_true_iff; intuition auto.
Qed.

(** We now define a simple-minded sorting predicate *)

Inductive sorted : forall {n}, vector nat n -> Prop :=
| sorted_nil : sorted Vnil
| sorted_cons x n (v : vector nat n) :
    forall_vect (fun y => Nat.leb x y) v = true ->
    sorted v -> sorted (Vcons x v).

(** Again, we show this by repeat functional eliminations. *)

Lemma fn_sorted n (v : vector nat n) : sorted (sort v).2.
Proof.
  funelim (sort v). (** The first elimination just gives the two [sort] cases. *)
  - constructor.
  - constructor; auto.
    (** Here we have a nested call to skip_first, for which the induction hypothesis holds: [[
  H : sorted (sort (skip_first (fun x : nat => x <=? h) t).2).2
  ============================
  forall_vect (fun y : nat => h <=? y) (sort (skip_first (fun x : nat => x <=? h) t).2).2 = true
]]

   We can apply functional elimination likewise, even if the predicate argument is instantiated
   here. *)

  funelim (skip_first (fun x : nat => Nat.leb x h) t); simp sort forall_vect in *; simpl in *.

  (** After further simplifications, we get: [[
  Heq : (h0 <=? h) = false
  H : sorted (Vcons h0 (sort (skip_first (fun x : nat => x <=? h0) t).2).2)
  ============================
  (h <=? h0) && forall_vect (fun y : nat => h <=? y) (sort (skip_first (fun x : nat => x <=? h0) t).2).2 = true
]]

    This requires inversion on the sorted predicate to find out that, by induction,
    [h0] is smaller than all of [fn (skip_first ...)], and hence [h] is as well.
    This is just regular reasoning. Just note how we got to this point in just
    two invocations of [funelim]. *)

    depelim H.
    rewrite andb_true_iff.
    enough (h <=? h0 = true). split; auto.
    eapply forall_vect_impl in H.
    apply H.
    intros x h0x. simpl. rewrite Nat.leb_le in *. omega.
    rewrite Nat.leb_le, Nat.leb_nle in *. omega.
Qed.

(** *** Pattern-matching and axiom K *)

Module KAxiom.

  (** By default we allow the K axiom, but it can be unset. *)

  Unset Equations WithK.

  (** In this case the following definition fails as [K] is not derivable on type [A]. *)

  Fail Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
    K x P p eq_refl := p.

  (** However, types enjoying a provable instance of the [K] axiom are fine.
      This relies on an instance of the [EqDec] typeclass for natural numbers.
      Note that the computational behavior of this definition on open terms
      is not to reduce to [p] but pattern-matches on the decidable equality proof.
      However the defining equation still holds as a _propositional_ equality. *)

  Equations K (x : nat) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
    K x P p eq_refl := p.

  Print Assumptions K. (* Closed under the global context *)

End KAxiom.
