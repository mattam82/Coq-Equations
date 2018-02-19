Require Import Equations Utf8.
Set Universe Polymorphism.
Open Scope equations_scope.
Import Sigma_Notations.
Polymorphic
Definition pr1_seq {A} {P : A -> Type} {p q : sigma A P} (e : p = q) : p.1 = q.1.
Proof. destruct e. apply eq_refl. Defined.

Require Vector.
Derive NoConfusion for Vector.t.

Notation " 'rew' H 'in' c " := (@eq_rect _ _ _ c _ H) (at level 20).

Definition J {A} {x : A} (P : forall y : A, x = y -> Type)
           (p : P x eq_refl) (y : A) (e : x = y) : P y e.
  destruct e. exact p.
Defined.

Lemma J_on_refl {A} (x y : A) (e : x = y) : J (λ (y : A) _, x = y) eq_refl y e = e.
Proof. destruct e. constructor. Defined.

Definition subst {A : Type} {x : A} {P : A -> Type} {y : A} (e : x = y) (f : P x) : P y :=
  J (fun x _ => P x) f y e.

Definition subst2 {A : Type} {x : A} {P : A -> Type} (f : P x) (y : A) (e : x = y) : P y :=
  J (fun x _ => P x) f y e.

Definition cong {A B : Type} (f : A -> B) {x y : A} (e : x = y) : f x = f y :=
  J (fun y _ => f x = f y) (@eq_refl _ (f x)) y e.
(* aka ap *)

Lemma cong_iter {A B C} (f : A -> B) (g : B -> C) (x y : A) (e : x = y) :
  cong g (cong f e) = cong (fun x => g (f x)) e.
Proof. revert y e. refine (J _ _). reflexivity. Qed.

Lemma cong_subst2 {A B C} (f : C -> B) (x y : A) (e : x = y) (z w : A -> C) (p : z x = w x) :
  cong f (subst2 (P:=fun x : A => z x = w x) p y e) =
  subst2 (P := fun x : A => f (z x) = f (w x)) (cong f p) y e.
Proof. revert y e. refine (J _ _). simpl. reflexivity. Defined.
  
Definition congd {A} {B : A -> Type} (f : forall x : A, B x) {x y : A} (p : x = y) :
  subst p (f x) = f y :=
  J (fun y p => subst p (f x) = f y) (@eq_refl _ (f x)) y p.
(* aka apd *)

Notation " 'rew' H 'in' c " := (@subst _ _ _ _ H c) (at level 20).

Notation "p =_{ P ; e } q" := (subst (P:=P) e p = q) (at level 90, format "p  =_{ P ; e }  q").

Definition subst_expl {A : Type} {x : A} {P : A -> Type} {y : A} (e : x = y) (f : P x) : P y :=
  subst e f.
Notation " 'rewP' H 'at' P 'in' c " := (@subst_expl _ _ P _ H c) (at level 20).

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

(** A typeclass that includes the data making [f] into an adjoin equivalence*)

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = cong f (eissect x)
}.
Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.

Record Equiv (A B : Type) := { equiv :> A -> B ; is_equiv :> IsEquiv equiv }.
Arguments equiv {A B} e.

Instance Equiv_IsEquiv {A B} (e : Equiv A B) : IsEquiv (equiv e).
Proof. apply is_equiv. Defined.

Definition inv_equiv {A B} (E: Equiv A B) : B -> A :=
  equiv_inv (IsEquiv:=is_equiv _ _ E).

Definition equiv_inv_equiv {A B} {E: Equiv A B} (x : A) : inv_equiv _ (equiv E x) = x := eissect _ x.
Definition inv_equiv_equiv {A B} {E: Equiv A B} (x : B) : equiv E (inv_equiv _ x) = x := eisretr _ x.
Definition equiv_adj {A B} {E: Equiv A B} (x : A)
  : inv_equiv_equiv (equiv E x) = cong (equiv E) (equiv_inv_equiv x)
  := eisadj _ x.

Notation " X <~> Y " := (Equiv X Y) (at level 90, no associativity, Y at next level).

Definition equiv_id A : A <~> A.
Proof.
  intros.
  refine {| equiv a := a |}.
  unshelve refine {| equiv_inv e := e |}.
  - red. reflexivity.
  - red; intros. reflexivity.
  - intros. simpl. reflexivity.
Defined.

Axiom axiom_triangle : forall {A}, A.

Definition equiv_sym {A B} : A <~> B -> B <~> A.
Proof.
  intros.
  refine {| equiv a := inv_equiv X a |}.
  unshelve refine {| equiv_inv e := equiv X e |}.
  - red; intros. apply eissect.
  - red; intros. apply eisretr.
  - intros x. simpl. destruct X. simpl. unfold inv_equiv. simpl.
    apply axiom_triangle.
Defined.

Require Import DepElimDec.

Set Equations Transparent.

Set Refolding Reduction.

Ltac rewrite_change c :=
  match type of c with
    ?foo = ?bar => change foo with bar in *
  end.

Equations path_sigma_uncurried {A : Type} {P : A -> Type} (u v : sigma A P)
  (pq : sigma _ (fun p => subst p u.2 = v.2))
  : u = v :=
path_sigma_uncurried (sigmaI u1 u2) (sigmaI _ _) (sigmaI eq_refl eq_refl) :=
  eq_refl.

Definition pr1_path {A} `{P : A -> Type} {u v : sigma A P} (p : u = v)
: u.1 = v.1
  := cong (@pr1 _ _) p.

Notation "p ..1" := (pr1_path p) (at level 3).

Definition pr2_path {A} `{P : A -> Type} {u v : sigma A P} (p : u = v)
: rew (p..1) in u.2 = v.2.
  destruct p. apply eq_refl.
Defined.

Notation "p ..2" := (pr2_path p) (at level 3).

Definition eta_path_sigma_uncurried {A} `{P : A -> Type} {u v : sigma A P}
           (p : u = v) : path_sigma_uncurried _ _ &(p..1 & p..2) = p.
  destruct p. apply eq_refl.
Defined.

Equations path_sigma {A : Type} {P : A -> Type} {u v : sigma A P}
  (p : u.1 = v.1) (q : rew p in u.2 = v.2)
: u = v :=
path_sigma {u:=(sigmaI _ _)} {v:=(sigmaI _ _)} eq_refl eq_refl := eq_refl.

Definition eta_path_sigma A `{P : A -> Type} {u v : sigma A P} (p : u = v)
: path_sigma (p..1) (p..2) = p
  := eta_path_sigma_uncurried p.

Instance path_sigma_equiv {A : Type} (P : A -> Type) (u v : sigma A P):
  IsEquiv (path_sigma_uncurried u v).
  unshelve refine (BuildIsEquiv _ _ _ _ _ _ _).
  - exact (fun r => &(r..1 & r..2)).
  - intro. apply eta_path_sigma_uncurried.
  - destruct u, v; intros [p q]; simpl in *.
    destruct p. simpl in *. destruct q.
    reflexivity.
  - destruct u, v; intros [p q]; simpl in *;
    destruct p. simpl in *. destruct q; simpl in *.
    apply eq_refl.
Defined.

Definition path_sigma_equivalence {A : Type} (P : A -> Type) (u v : sigma A P):
  &{ p : u.1 = v.1 & u.2 =_{P;p} v.2 } <~> u = v.
Proof.
  exists (path_sigma_uncurried u v).
  apply path_sigma_equiv.
Defined.

Module Telescopes.

  Inductive t : Type :=
  | inj : Type -> t
  | ext A : (A -> t) -> t.
  Notation Tel := t.
  
  Delimit Scope telescope with telescope.
  Notation "[]" := (inj unit) : telescope.
  Bind Scope telescope with t.

  Example onetel :=
    ext Type (fun A => ext nat (fun n => inj (vector A n))).
  Set Printing Universes.
  Equations telescope (T : Tel) : Type :=
    telescope (inj A) := A;
    telescope (ext A f) := sigma A (fun x => telescope (f x)).
  Coercion telescope : Tel >-> Sortclass.

  (** Accessors *)
  Equations nth_type (Δ : t) (t : Δ) (n : nat) : Type :=
  nth_type (inj A) _ _ := A;
  nth_type (ext A f) _ 0 := A;
  nth_type (ext A f) (sigmaI t ts) (S n) := nth_type (f t) ts n.

  Equations nth_value (Δ : t) (t : Δ) (n : nat) : nth_type Δ t n :=
  nth_value (inj A) a _ := a;
  nth_value (ext A f) (sigmaI t _) 0 := t;
  nth_value (ext A f) (sigmaI t ts) (S n) := nth_value (f t) ts n.

  (** Telescopic equality: an iterated sigma of dependent equalities *)
  Equations eq (Δ : Tel) (t s : Δ) : Tel := 
    eq (inj A) a b := inj (a = b);
    eq (ext A f) (sigmaI t ts) (sigmaI s ss) :=
      ext (t = s) (fun e : t = s => eq (f s) (rew e in ts) ss).
  Reserved Notation "x == y" (at level 70, y at next level, no associativity).
  Reserved Notation "x =={ Δ } y" (at level 70, y at next level, no associativity,
                                   format "x  =={ Δ } '/ '  y").
  Infix "==" := (eq _) : telescope.

  Definition eq_expl := eq.
  Infix "=={ Δ }" := (eq_expl Δ) : telescope.

  Equations refl {Δ : Tel} (t : telescope Δ) : eq Δ t t :=
    refl {Δ:=(inj A)} a := eq_refl;
    refl {Δ:=(ext A f)} (sigmaI t ts) := &(eq_refl & refl ts).

  Local Open Scope telescope.
  
  Equations J {Δ : Tel} (r : Δ) (P : forall s : Δ, eq Δ r s -> Type) 
            (p : P r (refl r)) (s : Δ) (e : eq _ r s) : P s e :=
    J {Δ:=(inj A)} a P p b e := telescopes.J P p b e;
    J {Δ:=(ext A f)} (sigmaI r rs) P p (sigmaI s ss) (sigmaI e es) := 
     telescopes.J (x:=r)
       (fun (s' : A) (e' : r = s') =>
        forall (ss' : f s') (es' : eq (f s') (rewP e' at f in rs) ss'),
          P &(s' & ss') &(e' & es'))
       (fun ss' es' =>
          J _ (fun ss'' (es'' : eq (f r) rs ss'') => P &(r & ss'') &(eq_refl & es''))
              p ss' es')
       s e ss es.

  Lemma J_refl {Δ : Tel} (r : Δ) (P : forall s : Δ, eq Δ r s -> Type) 
          (p : P r (refl r)) : J r P p r (refl r) = p.
  Proof.
    induction Δ. simpl. reflexivity.
    simpl. destruct r. refine (H pr1 pr2 _ _).
  Defined.

  Lemma J_on_refl {Δ : Tel} (x y : Δ) (e : x == y) :
    J _ (λ (y : Δ) _, x == y) (refl _) y e = e.
  Proof. revert y e. refine (J _ _ _). refine (J_refl _ _ _). Defined.

  Equations subst {Δ : Tel} (P : Δ -> Type) {u v : Δ} (e : u =={Δ} v) (p : P u) : P v :=
    subst P e p := J u (fun v _ => P v) p v e.

  Equations cong {Δ : Tel} {T} (f : Δ -> T) (u v : Δ) (e : u =={Δ} v) : f u = f v :=
    cong f u v e := J u (fun v _ => f u = f v) (@eq_refl T (f u)) v e.

  Notation "p ==_{ P ; e } q" := (subst P e p = q) (at level 70, q at next level, no associativity) : telescope.

  Reserved Notation "x =={ T ; e } y" (at level 70, y at next level, no associativity, only parsing,
                                   format "x  =={ T ; e } '/ '  y").
  Notation "x =={ P ; e } y" := (subst P e x == y) (only parsing) : telescope.

  Lemma eq_over_refl {Δ : Tel} {T} (f : forall x : Δ, T x) (u : Δ) :
    f u ==_{T;refl u} f u.
  Proof.
    unfold subst. refine (J_refl _ _ _).
  Defined.

  Equations dcong {Δ : Tel} {T} (f : forall x : Δ, T x) (u v : Δ) (e : u =={Δ} v) :
    f u ==_{T;e} f v :=
    dcong f u v e := J u (fun v e => f u ==_{T;e} f v) (eq_over_refl f u) v e.

  Equations cong_tel {Δ : Tel} {Γ : Tel}
            (f : Δ -> Γ) {u v : Δ} (e : u =={Δ} v) : f u =={Γ} f v :=
    cong_tel f e := J u (fun v _ => f u =={Γ} f v) (refl _) v e.

  Equations dcong_tel {Δ : Tel} {T : Δ -> Tel}
            (f : forall x : Δ, T x) {u v : Δ} (e : u =={Δ} v) :
    f u =={T;e} f v :=
    dcong_tel f e := J u (fun v e => f u =={T;e} f v) _ v e.
  Next Obligation.
    clear. unfold subst. rewrite J_refl. apply refl.
  Defined.
    
  Notation "'tele' x .. y 'in' z " := (@ext _ (fun x => .. (@ext _ (fun y => inj z)) ..))
  (at level 0, x binder, right associativity, z at level 60,
   format "'[' 'tele'  '/  ' x  ..  y '/ '  'in' '/ '  z ']'")
  : type_scope.

  Local Open Scope telescope.

  Notation "'telei' x .. y 'in' z " := (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
                                     (at level 0, right associativity, y at next level, 
                                      format "'[' 'telei'  '/  ' x  ..  y  'in'  z ']'", only parsing)
                                   : telescope.
  
  Lemma solution {A} (t : A) : tele ( x : A ) in (x = t) <~> [].
  Proof.
    refine {| equiv a := tt |}.
    unshelve refine {| equiv_inv e := telei t in eq_refl |}.
    - red; intros. destruct x. reflexivity.
    - red; intros. destruct x. now destruct pr2.
    - intros [x eq]. revert t eq. refine (telescopes.J _ _). constructor.
  Defined.
  
  Equations eq_eq_equiv (Δ : Tel) (u v : Δ) (e : u = v) : u == v :=
    eq_eq_equiv (inj A) a b e := e;
    eq_eq_equiv (ext A f) u v e :=
      let p := equiv_inv (IsEquiv:=path_sigma_equiv _ u v) e in
      &(p.1 & eq_eq_equiv _ _ _ p.2).

  Equations extend_tele (Δ : t) (Γ : telescope Δ -> t) : t :=
  extend_tele (inj A) Γ := ext A Γ;
  extend_tele (ext A f) Γ := ext A (fun a => extend_tele (f a) (fun fa => Γ &(a & fa))).
  
  Equations inj_extend_tel (Δ : t) (Γ : telescope Δ -> t) (s : Δ) (t : Γ s) :
    extend_tele Δ Γ :=
  inj_extend_tel (inj A) Γ s t := &(s & t) ;
  inj_extend_tel (ext A f) Γ (sigmaI t ts) e := 
    &(t & inj_extend_tel (f t) (fun fa => Γ &(t & fa)) ts e).
  
  Lemma reorder_tele (Δ : t) (Γ : telescope Δ -> t) :
    telescope (extend_tele Δ Γ) <~> tele (x : telescope Δ) in Γ x.
  Proof.
    unshelve econstructor. 
    - induction Δ; simpl extend_tele in *; simpl; intros. trivial.
      simpl in Γ. specialize (X X0.1 _ X0.2).
      refine &(&(X0.1 & X.1)&X.2).
    - unshelve econstructor.
      + induction Δ; simpl extend_tele in *; intros; simpl in *; trivial.
        specialize (X X0.1.1). exists X0.1.1.
        apply X. exact &(X0.1.2 & X0.2).
    + red. intro. induction Δ; simpl. destruct x. constructor.
      destruct x. simpl. rewrite H. reflexivity.
    + red. intro. induction Δ; simpl. destruct x. constructor.
      destruct x. simpl. rewrite H. reflexivity.
    + apply axiom_triangle.
  Defined.    
    
  Lemma eq_eq_equiv_refl {Δ : Tel} (u : Δ) : eq_eq_equiv Δ u u eq_refl = refl u.
  Proof.
    induction Δ; simp eq_eq_equiv.
    simpl. now rewrite H.
  Defined.

  Equations eq_eq_equiv_inv (Δ : Tel) (u v : Δ) (e : u == v) : u = v :=
    eq_eq_equiv_inv (inj A) a b e := e;
    eq_eq_equiv_inv (ext A f) u v e :=
      let e' := eq_eq_equiv_inv _ _ _ e.2 in
      equiv (path_sigma_equivalence _ u v) &(e.1 & e').

  Lemma eq_eq_equiv_inv_refl (Δ : Tel) (u : Δ) :
    eq_eq_equiv_inv Δ u u (refl u) = eq_refl.
  Proof.
    induction Δ; simp eq_eq_equiv_inv.
    simpl. now rewrite H.
  Defined.
    
  Lemma sect : forall (Δ : Tel) (u v : Δ), Sect (eq_eq_equiv_inv Δ u v) (eq_eq_equiv Δ u v).
  Proof.
    induction Δ. simpl. intros. intro. constructor.
    intros u v. intros He. simpl in * |-.
    Opaque path_sigma_uncurried path_sigma path_sigma_equivalence path_sigma_equiv.
    pose proof (eissect (path_sigma_uncurried u v)). simpl. red in H0.
    Transparent path_sigma_uncurried path_sigma path_sigma_equivalence path_sigma_equiv.
    match goal with
      |- context[equiv _ ?x] => set (foo:=x)
    end.
    specialize (H0 foo).
    set (bar := (equiv_inv (equiv _ foo))) in *.
    change (bar = foo) in H0. symmetry in H0.
    unfold foo in H0. subst foo. clearbody bar. revert bar H0.
    refine (@telescopes.subst2 _ _ _ _). simpl.
    simpl. red in H. specialize (H _ _ _ He.2). destruct He. simpl. apply telescopes.cong. apply H.
  Defined.

  Require Import EqDecInstances.

  Typeclasses Transparent telescope.
  Transparent path_sigma_equiv path_sigma_uncurried.
  Lemma retr : forall (Δ : Tel) (u v : Δ), Sect (eq_eq_equiv Δ u v) (eq_eq_equiv_inv Δ u v).
  Proof.
    induction Δ.
    + simpl. intros. intro. constructor.
    + intros u v e.
      simpl.
      specialize (H v.1 (rew (equiv_inv (IsEquiv := path_sigma_equiv _ _ _) e).1 in u.2) v.2
                    (equiv_inv (IsEquiv := path_sigma_equiv _ _ _) e).2).
      set (foo := eq_eq_equiv_inv _ _ _ _) in *.
      symmetry in H. clearbody foo. revert foo H.
      refine (telescopes.subst2 _).
      refine (eisretr (path_sigma_uncurried u v) _).
  Defined.

  Lemma eq_sym_dep {A} (x y : A) (P : x = y -> Type)
        (G : forall e : y = x, P (eq_sym e)) :
    forall e : x = y, P e.
  Proof.
    intros. destruct e. apply (G eq_refl).
  Defined.

  Global Instance eq_points_isequiv (Δ : Tel) (u v : Δ) : IsEquiv (eq_eq_equiv Δ u v) :=
    {| equiv_inv := eq_eq_equiv_inv Δ u v |}.
  Proof.
    - apply sect.
    - apply retr. 
    - revert v.
      induction Δ as [ | A t IH].
      + refine (telescopes.J _ _). constructor.
      + simpl in u; refine (telescopes.J _ _). simpl.
        rewrite IH.
        set (r:=retr (t u.1) u.2 u.2 eq_refl) in *.
        set(lhs:=eq_eq_equiv_inv _ _ _ _) in *.
        clearbody r. clearbody lhs.
        revert r. refine (eq_sym_dep _ _ _ _).
        revert lhs. now refine (telescopes.J _ _).
  Defined.
  
  (** Telescopic equality is equivalent to equality of the sigmas. *)
  Definition eq_points_equiv (Δ : Tel) (u v : Δ) : u = v <~> u == v :=
    {| equiv := eq_eq_equiv Δ u v |}.

  (** Necessary as the telescope structure is not easy for Coq to infer *)
  Global Hint Extern 0 (Equiv (?x = ?y) (telescope (eq ?Δ ?x' ?y'))) =>
    exact (eq_points_equiv Δ x' y') : typeclass_instances.

  Definition NoConf :=
    fun (A : Type) (x : &{ index : nat & vector A index}) =>
      match x.2 with
      | Vector.nil =>
        fun y : &{ index : nat & vector A index} =>
          match y.2 with
          | Vector.nil => True
          | Vector.cons _ _ => False
          end
      | @Vector.cons _ h n x0 =>
        fun y : &{ index : nat & vector A index} =>
          match y.2 with
          | Vector.nil => False
          | @Vector.cons _ h0 n0 x1 => telei (h) (n) in (x0) = telei (h0) (n0) in (x1) :> tele (_ : A) (n : nat) in vector A n
          end
      end.
  
  Lemma noconf :
    forall (A : Type) (a b : &{ index : nat & vector A index}), a = b -> NoConf A a b.
  Proof.
    intros. destruct H. destruct a. simpl. destruct pr2. simpl. exact I.
    simpl. reflexivity.
  Defined.

  Lemma noconf_inv :
    forall (A : Type) (a b : &{ index : nat & vector A index}), NoConf A a b -> a = b.
  Proof.
    intros. destruct a, b. destruct pr2, pr3; try constructor || contradiction.
    simpl in H.
    NoConfusion.destruct_tele_eq H. reflexivity.
  Defined.
  
  Import NoConfusion.

  Global Instance noconf_isequiv A a b : IsEquiv (noconf A a b).
  Proof.
    unshelve refine {| equiv_inv := noconf_inv A a b |}.
    intro.
    - destruct_sigma a; destruct_sigma b; 
      destruct a ; destruct b; simpl in * |-;
      on_last_hyp ltac:(fun id => destruct_tele_eq id || destruct id);
      solve [constructor].
    - intro. solve_noconf_inv_equiv.
    - intros. destruct x. destruct a. destruct pr2; simpl; constructor.
  Defined.

  Definition noconf_equiv A a b : Equiv (a = b) (NoConf A a b) :=
    {| equiv := noconf A a b |}.
  
  Global Hint Extern 0 (@IsEquiv (?x = ?y) (telescope (eq ?Δ ?x' ?y')) _) =>
    exact (@eq_points_isequiv Δ x' y') : typeclass_instances.

  Global Hint Extern 0 (@IsEquiv (?x = ?y) _ _) =>
    exact (@noconf_isequiv _ x y) : typeclass_instances.

  Global Hint Extern 0 (@Equiv (?x = ?y) _) =>
    exact (@noconf_equiv _ x y) : typeclass_instances.

  Arguments noconf_equiv : simpl never.
  Arguments noconf_isequiv : simpl never.
  Arguments equiv : simpl never.
  Arguments equiv_inv : simpl never.

  Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3).
  Infix "@" := eq_trans (at level 80).

  (** The composition of equivalences is an equivalence. *)
  Instance isequiv_compose A B f C g {E : @IsEquiv A B f} {E' : @IsEquiv B C g}
    : IsEquiv (compose g f) | 1000
    := BuildIsEquiv A C (compose g f)
                    (compose f^-1 g^-1) _ _ _ .
  Proof.
    exact
      (fun c => telescopes.cong g (eisretr f (g^-1 c)) @ eisretr g c).
    exact
      (fun a => telescopes.cong (f^-1) (eissect g (f a)) @ eissect f a).
    intro.
    simpl.
    apply axiom_triangle.
  Defined.
  
  Definition equiv_compose {A B C} (E : Equiv A B) (E' : Equiv B C) : Equiv A C :=
    Build_Equiv A C (compose (@equiv _ _ E') (@equiv _ _ E)) _.
  
  Definition injectivity_cons {A} (u v : tele (x : A) (n : nat) in vector A n)
    : (&(S u.2.1 & @Vector.cons A u.1 u.2.1 u.2.2) =
       &(S v.2.1 & @Vector.cons A v.1 v.2.1 v.2.2)) <~> u == v :=
    equiv_compose (noconf_equiv A &(S u.2.1 & @Vector.cons A u.1 u.2.1 u.2.2)
                   &(S v.2.1 & @Vector.cons A v.1 v.2.1 v.2.2))
                  (eq_points_equiv (tele (x : A) (n : nat) in vector A n) _ _).

End Telescopes.

Module Example_cons.

Notation " 'rewP' H 'at' B 'in' c " := (@telescopes.subst _ _ B _ H c) (at level 20, only parsing).

Import Telescopes.

Lemma inj_dep {A} (P : A -> Type)
      (G : forall e : inj A, P e) :
  forall e : A, P e.
Proof. apply G. Defined.

Polymorphic
Definition pr1_seq {A} {P : A -> Type} {p q : sigma A P} (e : p = q) : p.1 = q.1.
Proof. destruct e. apply eq_refl. Defined.

Notation " 'rew' H 'in' c " := (@eq_rect _ _ _ c _ H) (at level 20).

Polymorphic
Definition pr2_seq {A} {P : A -> Type} {p q : sigma A P} (e : p = q) :
  rew (pr1_seq e) in p.2 = q.2.
Proof. destruct e. apply eq_refl. Defined.

Polymorphic Definition rewh {A : Type} {B : A -> Type} {x : A} {p q : B x}
    (e : &(x & p) = &(x & q)) (e' : pr1_seq e = eq_refl) : p = q :=
  (@eq_rect _ (pr1_seq e) (fun f : x = x => rew f in p = q)
            (pr2_seq e) eq_refl e').

Polymorphic
Lemma solution_inv {A : Type}
      (B : A -> Type) (x : A) (p q : B x) (G : p = q -> Type) :
  (forall (e : &(x & p) = &(x & q)) (e' : pr1_seq e = eq_refl),
      G (rewh e e')) ->
  (forall e : p = q, G e).
Proof.
  intros H. intros e. destruct e. specialize (H eq_refl eq_refl). simpl in H. apply H.
Defined.

  Definition uncurry {A} {B : A -> Type} {C : forall x : A, B x -> Type}
  (f : forall s : &{ x : A & B x }, C s.1 s.2) :
  forall (x : A) (b : B x), C x b :=
  fun x b => f &(x & b).


  Lemma rewrite_in {A} {x y z : A} (e : x = y) (e' : x = z) : y = z.
  Proof. destruct e. apply e'. Defined.
  Lemma rewrite_inr {A} {x y z : A} (e : x = y) (e' : y = z) : x = z.
  Proof. destruct e. apply e'. Defined.
  Open Scope telescope.

  Lemma cong_equiv_inv (Δ : Tel) (T : Type) (f : Δ -> T) (u v : Δ) :
    IsEquiv f -> f u = f v ->  u =={Δ} v.
  Proof. 
    intros.
    apply eq_points_equiv.
    apply (telescopes.cong equiv_inv) in H.
    transitivity (f ^-1 (f u)). symmetry. apply (eissect f u).
    transitivity (f ^-1 (f v)). apply H. apply (eissect f v).
  Defined.
  
  Instance cong_is_equiv (Δ : Tel) (T : Type) (f : Δ -> T) (u v : Δ) (I : IsEquiv f) :
    IsEquiv (cong f u v) :=
    { equiv_inv := _ }.
  Proof.
    intros.
    - eapply cong_equiv_inv; eauto.
    - red.
      intros x. unfold cong_equiv_inv.
      apply axiom_triangle.
    - apply axiom_triangle.
    - apply axiom_triangle.
  Defined.
    
  Definition cong_equiv (Δ : Tel) (u v : Δ) (T : Type) (f : Δ -> T) (E : IsEquiv f) :
    u =={Δ} v <~> f u = f v :=
   {| equiv := cong f u v |}.

  Notation "'telei' x .. y 'in' z " := (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
                                     (at level 0, right associativity, y at next level, 
                                      format "'[' 'telei'  '/  ' x  ..  y  'in'  z ']'", only parsing)
                                   : telescope.

  Notation " a '={' P ; e } b " := (telescopes.subst (P:=P) e a = b) (at level 90).

  Notation " a '==={' P ; e } b " := (subst P _ _ e a = b) (at level 90, only parsing) : telescope.

  Lemma equiv_cong_subst {A B} (P : B -> Type) (f : A -> B)
        (s t : A) (e : s = t) (u : P (f s))
        (v : P (f t)) : u =_{(fun x => P (f x)); e} v <~> (u =_{P; telescopes.cong f e} v).
  Proof.
    unfold telescopes.subst.
    destruct e. simpl. apply equiv_id.
  Defined.

  Lemma equiv_cong_subst_dep {A} {B : A -> Type}
        (P : forall x : A, B x -> Type) (f : forall x : A, B x)
        (s t : A) (e : s = t) (u : P s (f s))
        (v : P t (f t)) : u =_{(fun x => P x (f x)); e} v <~>
                              (telescopes.J (fun y e => P y (rew e in (f s)))
                                     u _ e =_{(fun x => P _ x); telescopes.congd f e} v).
  Proof.
    unfold telescopes.subst.
    destruct e. simpl. apply equiv_id.
  Defined.
  
  Lemma equiv_cong_subst_tel {Δ Γ : Tel} (P : Γ -> Tel) (f : Δ -> Γ)
        (s t : Δ) (e : s =={Δ} t) (u : P (f s)) :
    subst P (cong_tel f e) u = subst (fun x => P (f x)) e u.
  Proof.
    unfold subst. revert t e. refine (J _ _ _). intros.
    rewrite J_refl. unfold cong_tel. simpl. rewrite !J_refl. reflexivity.
  Defined.

  Lemma equiv_tele_l {A} {A'} {B : A' -> Type} (e : Equiv A A') :
    tele (x : A) in B (equiv e x) <~> tele (x : A') in B x.
  Proof.
    simpl.
    unshelve refine {| equiv a := &(e a.1 & _) |}. exact a.2.
    unshelve refine {| equiv_inv a := &(e ^-1 a.1 & _) |}. destruct a. simpl.
    rewrite eisretr. exact pr2.
    
    red; intros. simpl. destruct x. simpl.
    pose (eisretr e pr1).
    apply path_sigma_uncurried. simpl.
    exists e0. simpl. unfold eq_rect_r. clearbody e0. 

    apply axiom_triangle.
    apply axiom_triangle.
    apply axiom_triangle.
  Defined.

  Lemma equiv_tele_r {A} {B B' : A -> Type} (e : forall x : A, Equiv (B x) (B' x)) :
    tele (x : A) in B x <~> tele (x : A) in (B' x).
  Proof.
    simpl.
    unshelve refine {| equiv a := &(a.1 & e a.1 a.2) |}.
    unshelve refine {| equiv_inv a := &(a.1 & inv_equiv (e a.1) a.2) |}.
    red; intros. simpl. destruct x. simpl. apply telescopes.cong.
    apply eisretr.
    red; intros. simpl. destruct x. simpl. apply telescopes.cong.
    apply eissect.

    intros [x bx].
    simpl. rewrite eisadj. simpl.
    destruct (eissect (e x) bx). simpl. reflexivity.
  Defined.

  Lemma eq_sym_equiv {A} {x y : A} : x = y <~> y = x.
  Proof.
    unshelve refine {| equiv a := eq_sym a |}.
    unshelve refine {| equiv_inv a := eq_sym a |}.
    intro e; destruct e. apply eq_refl.
    intro e; destruct e. apply eq_refl.
    intro e; destruct e. apply eq_refl.
  Defined.

  Lemma eq_tele_sym_equiv {Δ : Tel} {x y : Δ} : x == y <~> y == x.
  Proof.
    refine (equiv_compose _ _).
    refine (equiv_sym _).
    refine (eq_points_equiv _ _ _).
    refine (equiv_compose _ _).
    refine eq_sym_equiv.
    refine (eq_points_equiv _ _ _).
  Defined.

  Lemma subst_subst (Δ : Tel) (a b : Δ) (r s : a =={Δ} b) :
    subst (λ y : Δ, b == y) s (subst (λ x : Δ, x == a) r (refl a)) == refl b
    <~> r =={a =={Δ} b} s.
  Proof.
    induction Δ.
    + simpl in *. destruct r.
      unfold subst. simpl.
      rewrite telescopes.J_on_refl.
      apply eq_sym_equiv.
    + unfold subst.
      revert b r s. refine (J _ _ _).
      intros s. rewrite J_refl.
      rewrite (J_on_refl).
      refine (eq_tele_sym_equiv).
  Defined.

  (** This is the square we get (almost) by applying congruence: 
      it is dependent over e. *)
  Definition dep_square {Γ : Tel} (Δ : Γ -> Tel) u v (e : u =={Γ} v)
             (a b : forall ρ, Δ ρ)
             (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ)
             (r : eqΔ u) (s : eqΔ v) :=
      (subst (fun y => telescope (b u =={Δ;e} y)) s
             (subst (fun y => telescope (y =={Δ;e} a v)) r (dcong_tel a e))
       =={b u =={Δ;e} b v} (dcong_tel b e)).

  Definition square_tel {Δ : Tel} {w x y z : Δ} (t : w =={Δ} x)
             (b : y == z) (l : w == y) (r : x == z) : Tel :=
    subst (fun x : Δ => x == y) t l =={fun y => x == y;b} r.

  (** This is the square we want: we already simplified the dependency on 
      of the endpoints types. *)
  Lemma inj_extend_tel_equiv (Γ : Tel) (u v : Γ) (Δ : Tel) (a b : Γ → Δ)
        (eqΔ:=λ ρ : Γ, a ρ =={Δ} b ρ) (r : eqΔ u) (s : eqΔ v) :
    inj_extend_tel Γ eqΔ u r =={extend_tele Γ eqΔ} inj_extend_tel Γ eqΔ v s <~>
          extend_tele (u =={Γ} v)
          (λ x : u =={Γ} v,
                 square_tel r s (cong_tel a x) (cong_tel b x)).
    induction Γ.
    Transparent telescope eq.

    - simpl extend_tele.
      simpl inj_extend_tel.
      refine (equiv_tele_r _). intros x.
      unfold square_tel. 
      revert v x s. refine (telescopes.J _ _). intros s.
      simpl. unfold square_tel. unfold cong_tel. simpl.
      subst eqΔ. simpl in *.
      refine (equiv_sym _). apply subst_subst.

    - simpl. refine (equiv_tele_r _). intros.
      destruct v. simpl in *. subst eqΔ. simpl in *.
      revert pr1 x pr2 s. 
      refine (telescopes.J _ _).
      simpl. intros. specialize (X u.1 u.2 pr2).
      specialize (X (fun ρ => a &(u.1 & ρ))).
      simpl in X. specialize (X (fun ρ => b &(u.1 & ρ))).
      simpl in X. destruct u. simpl in *.
      specialize (X r s).
      apply X.
  Defined.
    
  Definition lifted_solution (Γ : Tel) (u v : Γ) (Γ' : Tel)
        (Δ : Tel) 
        (a b : Γ -> Δ)
        (eqΔ := λ ρ, a ρ =={Δ} b ρ)
        (r : eqΔ u) (s : eqΔ v)
        (f : extend_tele Γ eqΔ <~> Γ') :
    tele (e : u =={Γ} v) in square_tel r s (cong_tel a e) (cong_tel b e)
    <~>
    f (inj_extend_tel Γ eqΔ u r) =={Γ'} f (inj_extend_tel Γ eqΔ v s).
  Proof.
    refine (equiv_compose _ _).
    Focus 2.
    refine (equiv_compose _ _). 
    refine (cong_equiv (extend_tele Γ eqΔ)
                       (inj_extend_tel Γ eqΔ u r) (inj_extend_tel Γ eqΔ v s) _ f _).
    refine (eq_points_equiv _ _ _).
    unfold square_tel.
    refine (equiv_compose _ _).
    refine (equiv_sym _).
    refine (reorder_tele (u =={Γ} v) (fun x => _)).
    refine (equiv_sym _).
    apply inj_extend_tel_equiv.
  Defined.

  Lemma lower_solution :
    forall A n, tele (x' : A) (n' : nat) (v : vector A n') in (S n' = S n) <~>
                tele (x : A) in vector A n.
  Proof.
    intros A n.
    unshelve refine {| equiv a := _ |}.
    refine &(a.1 & _).
    destruct a. destruct pr2. destruct pr2.
    simpl in pr3. noconf pr3. exact pr2.
    
    unshelve refine {| equiv_inv a := _ |}.
    refine &(a.1, n & _).
    refine &(a.2 & eq_refl).

    intro.
    simpl. unfold solution_left. simpl. reflexivity.
    intro.
    simpl. unfold solution_left.
    unfold NoConfusion.noConfusion_nat_obligation_1. simpl.
    destruct x. destruct pr2. destruct pr2. simpl.
    red in pr3.
    refine (telescopes.cong _ _).
    revert pr3. simplify_one_dep_elim.
    simplify_one_dep_elim. intros.
    reflexivity.

    intros.
    simpl. destruct x as (x&n'&v&e).
    unfold solution_left_dep, apply_noConfusion. simpl.
    unfold telescopes.cong.
    revert e. simpl.
    simplify_one_dep_elim.
    simplify_one_dep_elim.
    intros. reflexivity.
  Defined.

  Definition telu A := tele (x' : A) (n' : nat) in vector A n'.
  Definition telv A n := tele (x : A) in vector A n.
  Lemma apply_equiv_dom {A B} (P : B -> Type) (e : Equiv A B) :
    (forall x : A, P (equiv e x)) -> forall x : B, P x.
  Proof.
    intros.
    specialize (X (e ^-1 x)).
    rewrite inv_equiv_equiv in X. exact X.
  Defined.

  Polymorphic
    Lemma equiv_switch_indep {A : Type} {B : Type} :
    (tele (_ : A) in B <~> tele (_ : B) in A).
  Proof.
    unshelve refine {| equiv a := _ |}. simpl. exact &(a.2 & a.1).
    unshelve refine {| equiv_inv a := _ |}. simpl. exact &(a.2 & a.1).

    - intro a. simpl. reflexivity.
    - intro a. simpl. reflexivity.
    - intro a. simpl. reflexivity.
  Defined.

  Polymorphic
    Lemma equiv_elim_unit {A : Type} : (tele (_ : []) in A) <~> inj A.
  Proof.
    unshelve refine {| equiv a := _ |}. simpl. exact a.2.
    unshelve refine {| equiv_inv a := _ |}. simpl. exact &(tt & a).

    - intro a. simpl. reflexivity.
    - intros [[ ] t]. simpl. reflexivity.
    - intros [[ ] t]. simpl. reflexivity.
  Defined.

  Arguments telescope : simpl never.
  Polymorphic
    Lemma solution_inv_tele {A : Type} (B : A -> Type) (x : A) (p q : B x) :
    (p = q <~> tele (e : x = x) (e' : p =_{B;e} q) in (e = eq_refl)).
  Proof.
    refine (equiv_compose (B:=tele (e : x = x) (e' : e = eq_refl) in (p =_{B;e} q)) _ _).
    all:cycle 1.
    refine (equiv_tele_r _); intro e.
    refine (equiv_switch_indep).
    refine (equiv_sym _).
    refine (equiv_compose _ _).
    refine (reorder_tele (tele (e : x = x) in (e = eq_refl)) (fun ρ => inj (p ={B;ρ.1} q))).
    simpl.
    refine (equiv_compose _ _).
    refine (equiv_sym (equiv_tele_l _)).
    refine (equiv_sym _).
    refine (@solution (x = x) eq_refl).
    simpl.
    refine equiv_elim_unit.
  Defined.

  Definition NoConf :=
    fun (A : Type) (x : &{ index : nat & vector A index}) =>
      match x.2 with
      | Vector.nil =>
        fun y : &{ index : nat & vector A index} =>
          match y.2 with
          | Vector.nil => inj unit
          | Vector.cons _ _ => inj False
          end
      | @Vector.cons _ h n x0 =>
        fun y : &{ index : nat & vector A index} =>
          match y.2 with
          | Vector.nil => inj False
          | @Vector.cons _ h0 n0 x1 =>
            telei (h) (n) in (x0) =={tele (x : A) (n : nat) in vector A n}
                                      telei (h0) (n0) in (x1)
          end
      end.
  
  Lemma noconf :
    forall (A : Type) (a b : &{ index : nat & vector A index}),
      a =={ext nat (fun n => inj (vector A n))} b -> NoConf A a b.
  Proof.
    intros. destruct X. destruct a, b, pr1, pr2. simpl.
    destruct pr3. simpl. simpl. exact tt.
    simpl. exists eq_refl. exists eq_refl. simpl. constructor.
  Defined.

  Lemma noconf_inv :
    forall (A : Type) (a b : &{ index : nat & vector A index}),
      NoConf A a b -> a =={ext nat (fun n => inj (vector A n))} b.
  Proof.
    intros. destruct a, b. destruct pr2, pr3; try constructor || contradiction.
    simpl in X. exists eq_refl. constructor. unfold NoConf in X.
    cbv beta iota delta -[telescope eq_expl] in X.
    apply (@cong_tel (tele (x : A) (n : nat) in (vector A n))
                    (tele (n1 : nat) in vector A n1)
                    (fun x => &(S x.2.1 & Vector.cons x.1 x.2.2))
                    _ _ X).
  Defined.
  
  Import NoConfusion.

  Global Instance noconf_isequiv A a b : IsEquiv (noconf A a b).
  Proof.
    unshelve refine {| equiv_inv := noconf_inv A a b |}.
    intro.
    - destruct_sigma a; destruct_sigma b.
      destruct a ; destruct b; simpl in * |-. simpl.
      on_last_hyp ltac:(fun id => destruct_tele_eq id || destruct id);
        solve [constructor].
      simpl. bang. simpl. bang.
      simpl. unfold telescope in x.
      destruct_sigma x. 
      destruct_sigma x. destruct idx, idx0. simpl in x. destruct x.
      simpl. reflexivity.
      
    - intro.
      destruct_sigma a; destruct_sigma b.
      destruct x. destruct pr1, pr2.
      destruct a; simpl in * |-; constructor.

    - intros. destruct x, a, b. destruct pr1, pr2; simpl. destruct pr3; constructor.
  Defined.

  Definition noconf_equiv A a b :
    Equiv (a =={tele (n : nat) in vector A n} b) (NoConf A a b) :=
    {| equiv := noconf A a b |}.
  
  Definition injectivity_cons2 {A} (u v : tele (x : A) (n : nat) in vector A n)
    : tele (e : S u.2.1 = S v.2.1) in
      (@Vector.cons A u.1 u.2.1 u.2.2 ==_{fun x : telescope (inj nat) => Vector.t A x;e} @Vector.cons A v.1 v.2.1 v.2.2)
        <~> u == v.
  Proof.
    refine (noconf_equiv A &(S u.2.1 & @Vector.cons A u.1 u.2.1 u.2.2)
          &(S v.2.1 & @Vector.cons A v.1 v.2.1 v.2.2)). 
  Defined.

  Ltac intros_tele :=
    match goal with
      |- Equiv (telescope (ext _ ?F)) _ =>
      refine (equiv_tele_r _);
      match F with
        (fun x => @?F x) =>
        intros ?x;
        match goal with
          id : _ |- Equiv _ ?y =>
          let f' := eval simpl in (F id) in
              change (Equiv (telescope f') y)
        end
      end
    | |- Equiv (sigma _ (fun x => _)) _ =>
      refine (equiv_tele_r _); intros ?x
    end.

  Lemma rew_sym (A : Type) {Δ : A -> Tel} (x y : A) (px : Δ x) (py : Δ y)
        (e : y = x) :
    px =={Δ x} telescopes.subst (P:=Δ) e py ->
    telescopes.subst (P:=Δ) (eq_sym e) px =={Δ y} py.
  Proof. destruct e. simpl. trivial. Defined.

  Equations sym {Δ : Tel} {s t : Δ} (e : s =={Δ} t) : t =={Δ} s :=
    sym {Δ:=(inj A)} e := eq_sym e ;
    sym {Δ:=(ext A f)} e := &(eq_sym e.1 & rew_sym _ _ _ _ _ _ (sym e.2)).

  Lemma cong_tel_proj (Δ : Tel) (A : Type) (Γ : A -> Tel)
        (f : Δ → ext A Γ) (u v : Δ) (e : u =={Δ} v) :
    (cong_tel f e).1 = cong_tel (Γ:=inj A) (fun x => (f x).1) e.
  Proof.
    induction Δ.
    
    + revert v e. refine (J _ _ _).
      simpl. unfold cong_tel. simpl. reflexivity.
    + revert v e. refine (J _ _ _).
      simpl.
      specialize (H u.1 (fun t => f &(u.1 & t)) u.2 u.2 (refl _)).
      unfold cong_tel at 1. simpl. unfold cong_tel in H.
      rewrite H. reflexivity.
  Defined.

  Lemma cong_tel_nondep {Δ Γ : Tel} (T : Γ) (u v : Δ) (e : u =={Δ} v) :
    cong_tel (fun _ => T) e == refl T.
  Proof.
    revert v e. refine (J _ _ _).
    unfold cong_tel. rewrite J_refl. apply refl.
  Defined.
  
  Arguments eq : simpl never.
  Lemma example {A} :
    &{ Γ' : Tel &
           tele (n : nat) (x y : A) (v v' : Vector.t A n) in
        (Vector.cons x v = Vector.cons y v') <~> Γ' }.
  Proof.
    intros. eexists.
    refine (equiv_compose _ _).
    do 5 intros_tele.
    2:simpl.
    refine (equiv_compose _ _).
    refine (solution_inv_tele (A:=nat) (Vector.t A) _ _ _).

    refine (equiv_compose _ _).
    refine (reorder_tele (tele (e0 : S n = S n) in (Vector.cons x v ={ vector A ; e0} (Vector.cons y v'))) (fun ρ => inj (ρ.1 = eq_refl))).
    simpl.
    refine (equiv_compose _ _).
    refine (equiv_sym _).
    refine (equiv_tele_l _).
    refine (equiv_sym _).
    refine (injectivity_cons2 &(x, n & v) &(y, n & v')).
    pose (lower_solution A n).
    pose (inv_equiv e &(x & v)).
    simpl in e.
    pose (telei x n in v : telu A).
    pose (sol:=lifted_solution (tele (_ : A) (n' : nat) in vector A n')).
    simpl in sol.
    simpl in t0.
    unfold e, lower_solution, equiv, equiv_inv, inv_equiv in t0. simpl in t0.
    unfold e, lower_solution, equiv, equiv_inv, inv_equiv in t0. simpl in t0.
    set (solinst :=
           sigmaI (fun x => sigma nat (fun n => vector A n)) t0.1 &(t0.2.1 & t0.2.2.1)).
    specialize (sol solinst).
    specialize (sol &(y, n & v')).
    (* specialize (sol solinst). (*&(y, n & v')).*) *)
    specialize (sol (telv A n)).
    specialize (sol (inj nat)). 
    simpl in e.
    specialize (sol (fun x => S x.2.1) (fun x => S n) eq_refl eq_refl). simpl in sol.
    specialize (sol e). subst e.
    simpl in sol.
    unfold solution_left in *.
    simpl in *.
    unfold inv_equiv in sol. unfold eq_points_equiv in sol. simpl in *.
    unfold equiv_inv in *. simpl in *.
    unfold cong in sol. simpl in *.
    
    refine (equiv_compose
              (C:=tele (e : x = y) in (v ={ (λ _ : A, inj (vector A n)); e} v'))
              _ sol).
    refine (equiv_tele_r _).
    intros.

    unfold equiv_sym. 
    unfold injectivity_cons2. simpl.
    unfold noconf_equiv, equiv, inv_equiv, equiv_inv. simpl.
    unfold square_tel.
    simpl.
    Transparent eq telescope.
    simpl.
  
    clear sol. subst solinst.
    unfold subst. simpl.
    rewrite (cong_tel_proj _ _ (fun x : nat => inj (vector A x))
                           (λ x0 : tele (_ : A) (n0 : nat) in vector A n0,
                             &(S (x0.2).1 & Vector.cons x0.1 (x0.2).2))
                           _ _ x0).
    simpl.
    Transparent telescope.
    unfold telescope at 1. simpl telescope.
    rewrite (cong_tel_nondep (Γ:=inj nat) (S n) _ _ x0).
    refine (equiv_id _). simpl.
    refine (equiv_id _).
  Defined.
  Print Assumptions example.
  Eval compute in (pr1 (@example nat)).

End Example_cons.
