Require Import Equations.
Set Universe Polymorphism.
Open Scope sigma_scope.
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

Definition subst {A : Type} {x : A} {P : A -> Type} {y : A} (e : x = y) (f : P x) : P y :=
  J (fun x _ => P x) f y e.

Definition subst2 {A : Type} {x : A} {P : A -> Type} (f : P x) (y : A) (e : x = y) : P y :=
  J (fun x _ => P x) f y e.

Definition cong {A B : Type} (f : A -> B) {x y : A} (e : x = y) : f x = f y :=
  J (fun y _ => f x = f y) (@eq_refl _ (f x)) y e.
(* aka ap *)

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

Axiom axiom : forall {A}, A.

Definition equiv_sym {A B} : A <~> B -> B <~> A.
Proof.
  intros.
  refine {| equiv a := inv_equiv X a |}.
  unshelve refine {| equiv_inv e := equiv X e |}.
  - red; intros. apply eissect.
  - red; intros. apply eisretr.
  - intros x. simpl. destruct X. simpl. unfold inv_equiv. simpl.
    apply axiom.
Defined.

Require Import DepElimDec.

(* Unset Equations OCaml Splitting. *)
(* BUG *)
(* Equations tel_eq (Δ : Tel) (t s : Tuple Δ) : Type :=  *)
(* tel_eq nil nil nil := unit; *)
(* tel_eq (consTel A f) (cons t ts) (cons s ss) := *)
(*   sigma (t = s) (fun e : t = s => tel_eq (f s) (rewP e at fun x => Tuple (f x) in ts) ss). *)
Set Equations Transparent.

Set Refolding Reduction.

Ltac rewrite_change c :=
  match type of c with
    ?foo = ?bar => change foo with bar in *
  end.


(* Definition path_sigma_uncurried {A : Type} {P : A -> Type} (u v : sigma A P) *)
(*            (pq : sigma _ (fun p => subst p u.2 = v.2)) : u = v. *)
(* Proof. *)
(*   destruct u, v. simpl in *. *)
(*   destruct pq. revert pr0 pr4 pr3 pr5. refine (Top.J _ _). *)
(*   simpl. refine (Top.subst2 _). reflexivity. *)
(* Defined. *)

Definition path_sigma_uncurried {A : Type} {P : A -> Type} (u v : sigma A P)
           (pq : &{p : u.1 = v.1 & subst p u.2 = v.2})
: u = v
  := match pq.2 in (_ = v2) return u = &(v.1 & v2) with
       | eq_refl => match pq.1 as p in (_ = v1) return u = &(v1 & subst p u.2) with
                | eq_refl => eq_refl
              end
     end.

(** Simplify only if [pq] is a constructor *)
Arguments path_sigma_uncurried _ _ _ _ !pq : simpl nomatch.

(* Equations path_sigma_uncurried {A : Type} {P : A -> Type} (u v : sigma A P) *)
(*   (pq : sigma _ (fun p => subst p u.2 = v.2)) *)
(*   : u = v := *)
(* path_sigma_uncurried (sigmaI u1 u2) (sigmaI v1 v2) (sigmaI eq_refl eq_refl) := *)
(*   eq_refl. *)

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

Definition path_sigma {A : Type} {P : A -> Type} {u v : sigma A P}
           (p : u.1 = v.1) (q : rew p in u.2 = v.2) : u = v
    := match q in (_ = v2) return u = &(v.1 & v2) with
       | eq_refl => match p as p in (_ = v1) return u = &(v1 & subst p u.2) with
                | eq_refl => eq_refl
              end
     end.
  

(* Equations path_sigma {A : Type} {P : A -> Type} {u v : sigma A P} *)
(*   (p : u.1 = v.1) (q : rew p in u.2 = v.2) *)
(* : u = v := *)
(* path_sigma {u:=(sigmaI _ _)} {v:=(sigmaI _ _)} eq_refl eq_refl := eq_refl. *)

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
    J {Δ:=(inj A)} a P p b e := Top.J P p b e;
    J {Δ:=(ext A f)} (sigmaI r rs) P p (sigmaI s ss) (sigmaI e es) := 
     Top.J (x:=r)
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
            (f : Δ -> Γ) (u v : Δ) (e : u =={Δ} v) : f u =={Γ} f v :=
    cong_tel f u v e := J u (fun v _ => f u =={Γ} f v) (refl _) v e.

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
  (* Notation "'tele' x .. y " := (@ext _ (fun x => .. (@ext _ (fun y => inj)) ..)) *)
  (* (at level 0, x binder, right associativity, *)
  (*  format "'[' 'tele'  '/  ' x  ..  y ']'") *)
  (*                              : telescope. *)
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
    - intros [x eq]. revert t eq. refine (Top.J _ _). constructor.
  Defined.
  
  Equations eq_eq_equiv (Δ : Tel) (u v : Δ) (e : u = v) : u == v :=
    eq_eq_equiv (inj A) a b e := e;
    eq_eq_equiv (ext A f) u v e :=
      let p := equiv_inv (IsEquiv:=path_sigma_equiv _ u v) e in
      &(p.1 & eq_eq_equiv _ _ _ p.2).

  Equations extend_tele (Δ : t) (Γ : telescope Δ -> t) : t :=
    extend_tele (inj A) Γ := ext A Γ;
    extend_tele (ext A f) Γ := ext A (fun a => extend_tele (f a) (fun fa => Γ &(a & fa))).
(*
"forall s : f t, (fun a : f t => Γ &(t & a)) s -> extend_tele (f t) (fun a : f t => Γ &(t & a))" == 

"forall s : f t, Γ &(t & s) -> extend_tele (f t) (fun a : f t => Γ &(t & a))" == 


telescope (extend_tele (f t) (fun fa : f t => Γ &(t & fa))

telescope ((fun a : A => extend_tele (f a) (fun fa : f a => Γ &(a & fa))) t))

"(fun x : A => telescope ((fun a : A => extend_tele (f a) (fun fa : f a => Γ &(a & fa))) x)) t").
 *)
  
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
    + apply axiom.     
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
    refine (@Top.subst2 _ _ _ _). simpl.
    simpl. red in H. specialize (H _ _ _ He.2). destruct He. simpl. apply Top.cong. apply H.
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
      refine (Top.subst2 _).
      refine (eisretr (path_sigma_uncurried u v) _).
  Defined.

  Lemma cong_iter {A B C} (f : A -> B) (g : B -> C) (x y : A) (e : x = y) :
    Top.cong g (Top.cong f e) = Top.cong (fun x => g (f x)) e.
  Proof. revert y e. refine (Top.J _ _). reflexivity. Qed.

  Lemma cong_subst2 {A B C} (f : C -> B) (x y : A) (e : x = y) (z w : A -> C) (p : z x = w x) :
    Top.cong f (Top.subst2 (P:=fun x : A => z x = w x) p y e) =
    Top.subst2 (P := fun x : A => f (z x) = f (w x)) (Top.cong f p) y e.
  Proof. revert y e. refine (Top.J _ _). simpl. reflexivity. Defined.

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
      + refine (Top.J _ _). constructor.
      + simpl in u; refine (Top.J _ _). simpl.
        rewrite IH.
        set (r:=retr (t u.1) u.2 u.2 eq_refl) in *.
        set(lhs:=eq_eq_equiv_inv _ _ _ _) in *.
        clearbody r. clearbody lhs.
        revert r. refine (eq_sym_dep _ _ _ _).
        revert lhs. now refine (Top.J _ _). 
  Defined.
  
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
    (fun c => Top.cong g (eisretr f (g^-1 c)) @ eisretr g c).
  exact
    (fun a => Top.cong (f^-1) (eissect g (f a)) @ eissect f a).
  intro.
  simpl.
  apply axiom.
Defined.

Definition equiv_compose {A B C} (E : Equiv A B) (E' : Equiv B C) : Equiv A C :=
  Build_Equiv A C (compose (@equiv _ _ E') (@equiv _ _ E)) _.
  
  Definition injectivity_cons {A} (u v : tele (x : A) (n : nat) in vector A n)
    : (&(S u.2.1 & @Vector.cons A u.1 u.2.1 u.2.2) =
       &(S v.2.1 & @Vector.cons A v.1 v.2.1 v.2.2)) <~> u == v :=
    equiv_compose (noconf_equiv A &(S u.2.1 & @Vector.cons A u.1 u.2.1 u.2.2)
                   &(S v.2.1 & @Vector.cons A v.1 v.2.1 v.2.2))
                  (eq_points_equiv (tele (x : A) (n : nat) in vector A n) _ _).

  
Definition square_tel {Δ : Tel} {w x y z : Δ} (t : w =={Δ} x) (b : y == z) (l : w == y) (r : x == z) : Tel :=
  subst (fun x : Δ => x == y) t l =={fun y => x == y;b} r.

Definition flip_square_tel {A} {w x y z} {t b l r} (s : @square_tel A w x y z t b l r) : square_tel l r t b.
Proof.
  revert x t b l r s. refine (J _ _ _). revert z. refine (J _ _ _).
  intros l r s. unfold square_tel in s. simpl in s.
  unfold subst in s. 
  revert r s. refine (J _ _ _).
  revert y l. refine (J _ _ _).
  unfold square_tel. unfold subst.
  rewrite 3!J_refl. apply refl.
Defined.

Instance flip_square_tel_isequiv {A : Tel} {w x y z : A} {t b l r} :
  IsEquiv (@flip_square_tel A w x y z t b l r).
Proof.
  unshelve refine {| equiv_inv := _ |}.
  - revert x t0 l r b.
    refine (J _ _ _).
    revert y. refine (J _ _ _).
    revert z. refine (J _ _ _).
    intros b s. unfold square_tel in s. simpl in s.
    unfold subst in s.
    revert b s. refine (J _ _ _).
    unfold square_tel. simpl. unfold subst.
    rewrite !J_refl. apply refl.

  (* Not shown coherent! Many J applications... *)
  - apply axiom.
  - apply axiom.
  - apply axiom.
Defined.

Definition flip_square_tel_equiv {A : Tel} {w x y z : A} {t b l r} : Equiv (@square_tel A w x y z t b l r) (square_tel l r t b) :=
  {| equiv := @flip_square_tel A w x y z t b l r |}.

End Telescopes.

Module Example_cons.

  
Lemma lower_solution : forall A n, forall (x : &{ a : nat & &{ _ : A & &{ _ : vector A a & S a = S n}}})
                        (P : forall n0 w : nat, A -> vector A w -> S x.1 = S n0 -> Type),
      (P x.1 x.1 x.2.1 x.2.2.1 eq_refl) ->
      P n x.1 (x.2).1 ((x.2).2).1 ((x.2).2).2.
Proof.
  intros A n. curry. intros.
  revert H. simplify_dep_elim. simplify_dep_elim. simpl. trivial.
Defined.

Notation " 'rewP' H 'at' B 'in' c " := (@Top.subst _ _ B _ H c) (at level 20, only parsing).

Definition square {A} {w x y z : A} (t : w = x) (b : y = z) (l : w = y) (r : x = z) : Type :=
  rewP t at (fun x => x = y) in l =_{_;b} r.

Definition flip_square {A} {w x y z} {t b l r} (s : @square A w x y z t b l r) : square l r t b.
Proof.
  destruct t. destruct b. unfold square in s. simpl in s. destruct s.
  unfold square. destruct l. constructor.
Defined.

Instance flip_square_isequiv {A} {w x y z} {t b l r} : IsEquiv (@flip_square A w x y z t b l r).
Proof.
  unshelve refine {| equiv_inv := _ |}.
  destruct t, l, r. unfold square. simpl. intros. simpl in H.
  destruct H. reflexivity.

  red. intros. destruct t, l, r. red in x0. simpl in x0. destruct x0. reflexivity.
  red. intros. destruct t, b, l. red in x0. simpl in x0. destruct x0. reflexivity.
  unfold square. intros.
  destruct t, b, l, x0. simpl. reflexivity.
Defined.

Definition flip_square_equiv {A} {w x y z : A} {t b l r} : Equiv (@square A w x y z t b l r) (square l r t b) :=
  {| equiv := flip_square |}.

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
    induction Δ; simpl; simpl in *.
    + apply (Top.cong equiv_inv) in H.
      transitivity (f ^-1 (f u)). symmetry. apply (eissect f u).
      transitivity (f ^-1 (f v)). apply H. apply (eissect f v).
      
    + assert (u = v).
      transitivity (f ^-1 (f u)). symmetry. apply (eissect f u).
      transitivity (f ^-1 (f v)).
      now apply (Top.cong equiv_inv) in H.
      apply (eissect f v).
      apply (equiv_inv (f:=path_sigma_uncurried u v)) in H0.
      exists H0.1.
      set (f' := fun v2 : t0 v.1 => f &(v.1 & v2)).
      apply (X0 _ f'). apply axiom.
      subst f'. simpl.
      apply Top.cong. apply Top.cong. exact H0.2.
  Defined.
  
  Instance cong_is_equiv (Δ : Tel) (T : Type) (f : Δ -> T) (u v : Δ) (I : IsEquiv f) :
    IsEquiv (cong f u v) :=
    { equiv_inv := _ }.
  Proof.
    intros.
    - eapply cong_equiv_inv; eauto.
    - red.
      intros x.
      induction Δ.
      simpl. apply axiom.
      simpl. apply axiom.
    - apply axiom.
    - apply axiom.
  Defined.
    
  Definition cong_equiv (Δ : Tel) (u v : Δ) (T : Type) (f : Δ -> T) (E : IsEquiv f) :
    u =={Δ} v <~> f u = f v :=
   {| equiv := cong f u v |}.

  Notation "'telei' x .. y 'in' z " := (@sigmaI _ _ x .. (@sigmaI _ _ y z) ..)
                                     (at level 0, right associativity, y at next level, 
                                      format "'[' 'telei'  '/  ' x  ..  y  'in'  z ']'", only parsing)
                                   : telescope.

  Require Import Utf8.

  Notation " a '={' P ; e } b " := (Top.subst (P:=P) e a = b) (at level 90).

  Notation " a '==={' P ; e } b " := (subst P _ _ e a = b) (at level 90, only parsing) : telescope.

  Lemma equiv_cong_subst {A B} (P : B -> Type) (f : A -> B)
        (s t : A) (e : s = t) (u : P (f s))
        (v : P (f t)) : u =_{(fun x => P (f x)); e} v <~> (u =_{P; Top.cong f e} v).
  Proof.
    unfold Top.subst.
    destruct e. simpl. apply equiv_id.
  Defined.

  Lemma equiv_cong_subst_dep {A} {B : A -> Type}
        (P : forall x : A, B x -> Type) (f : forall x : A, B x)
        (s t : A) (e : s = t) (u : P s (f s))
        (v : P t (f t)) : u =_{(fun x => P x (f x)); e} v <~>
                              (Top.J (fun y e => P y (rew e in (f s)))
                                     u _ e =_{(fun x => P _ x); Top.congd f e} v).
  Proof.
    unfold Top.subst.
    destruct e. simpl. apply equiv_id.
  Defined.
  
  Lemma equiv_cong_subst_tel {Δ Γ : Tel} (P : Γ -> Tel) (f : Δ -> Γ)
        (s t : Δ) (e : s =={Δ} t) (u : P (f s))
        (v : P (f t)) :
    subst P (cong_tel f _ _ e) u = subst (fun x => P (f x)) e u.
  Proof.
    unfold subst. revert t e v. refine (J _ _ _). intros.
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
    apply axiom. apply axiom. apply axiom.
    (* apply eisretr. *)
    (* red; intros. simpl. destruct x. simpl. apply Top.cong. *)
    (* apply eissect. *)

    (* intros [x bx]. *)
    (* simpl. rewrite eisadj. simpl. *)
    (* destruct (eissect (e x) bx). simpl. reflexivity. *)
  Defined.

  Lemma equiv_tele_r {A} {B B' : A -> Type} (e : forall x : A, Equiv (B x) (B' x)) :
    tele (x : A) in B x <~> tele (x : A) in (B' x).
  Proof.
    simpl.
    unshelve refine {| equiv a := &(a.1 & e a.1 a.2) |}.
    unshelve refine {| equiv_inv a := &(a.1 & inv_equiv (e a.1) a.2) |}.
    red; intros. simpl. destruct x. simpl. apply Top.cong.
    apply eisretr.
    red; intros. simpl. destruct x. simpl. apply Top.cong.
    apply eissect.

    intros [x bx].
    simpl. rewrite eisadj. simpl.
    destruct (eissect (e x) bx). simpl. reflexivity.
  Defined.


  (* Definition lifted_solution_lhs_type (Γ : Tel) (u v : Γ) *)
  (*       (Δ : Γ -> Tel) *)
  (*       (a b : forall ρ, Δ ρ) *)
  (*       (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ) *)
  (*       (r : eqΔ u) (s : eqΔ v) := *)
  (*   tele (e : u =={Γ} v) in *)
  (*     let lhs := dcong a u v e in *)
  (*     let rhs := dcong b u v e in *)
  (*     let lhs' := *)
  (*         subst (fun au : Δ u => au ==_{λ ρ', Δ ρ'; e} a v) (a u) (b u) r lhs in *)
  (*     let lhs'' := *)
  (*         subst (fun bv : Δ v => b u ==_{λ ρ', Δ ρ'; e} bv) (a v) (b v) s lhs' in *)
  (*     lhs'' = rhs. *)

  (* Definition lifted_solution_lhs_type (Γ : Tel) (u v : Γ) *)
  (*       (Δ : Γ -> Tel) *)
  (*       (a b : forall ρ, Δ ρ) *)
  (*       (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ) *)
  (*       (r : eqΔ u) (s : eqΔ v) := *)
  (*   tele (e : u =={Γ} v) in *)
  (*     let lhs := dcong a u v e in *)
  (*     let rhs := dcong b u v e in *)
  (*     square (cong (subst (λ ρ : Γ, Δ ρ) u v e) _ _ r) *)
  (*            (inv_equiv (eq_points_equiv (Δ v) (a v) (b v)) s) *)
  (*            lhs rhs. *)

  Definition lifted_solution_lhs_type (Γ : Tel) (u v : Γ)
        (Δ : Γ -> Tel)
        (a b : forall ρ, Δ ρ)
        (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ)
        (r : eqΔ u) (s : eqΔ v) :=
    tele (e : u =={Γ} v) in
      let lhs := dcong_tel a e in
      let rhs := dcong_tel b e in
      square (cong (subst Δ e) _ _ r)
             (inv_equiv (eq_points_equiv (Δ v) (a v) (b v)) s)
             (inv_equiv (eq_points_equiv _ _ _) lhs)
             (inv_equiv (eq_points_equiv _ _ _) rhs).

  (** This is the square we get (almost) by applying congruence *)
  Definition dep_square {Γ : Tel} (Δ : Γ -> Tel) u v (e : u =={Γ} v)
             (a b : forall ρ, Δ ρ)
             (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ)
             (r : eqΔ u) (s : eqΔ v) :=
      (subst (fun y => telescope (b u =={Δ;e} y)) s
             (subst (fun y => telescope (y =={Δ;e} a v)) r (dcong_tel a e))
       =={b u =={Δ;e} b v} (dcong_tel b e)).

  (** This is the square we want: *)
  Definition theorem_square {Γ : Tel} (Δ : Γ -> Tel) u v (e : u =={Γ} v)
             (a b : forall ρ, Δ ρ)
             (r : a u =={Δ u} b u) (s : a v =={Δ v} b v) :=
    (* subst (λ x : Δ v, x == subst Δ e (b u)) (dcong_tel a e) *)
    (*       (cong_tel (subst Δ e) (a u) (b u) r) *)
    (* =={λ y : Δ v, a v == y; dcong_tel b e} s. *)
    square_tel (dcong_tel a e) (dcong_tel b e) (cong_tel (subst (λ ρ : Γ, Δ ρ) e) _ _ r) s.
  
  Definition lifted_solution_lhs_tel_type (Γ : Tel) (u v : Γ)
        (Δ : Γ -> Tel)
        (a b : forall ρ, Δ ρ)
        (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ)
        (r : eqΔ u) (s : eqΔ v) :=
    tele (e : u =={Γ} v) in theorem_square Δ u v e a b r s.
  
  (* Definition lifted_solution_lhs_tel_type (Γ : Tel) (u v : Γ) *)
  (*       (Δ : Γ -> Tel) *)
  (*       (a b : forall ρ, Δ ρ) *)
  (*       (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ) *)
  (*       (r : eqΔ u) (s : eqΔ v) := *)
  (*   tele (e : u =={Γ} v) in *)
  (*     let lhs := dcong_tel a e : a u =={Δ;e} a v in *)
  (*     let rhs := dcong_tel b e in *)
  (*     (subst (fun y => telescope (b u =={Δ;e} y)) s *)
  (*            (subst (fun y => telescope (y =={Δ;e} a v)) r (dcong_tel a e)) *)
  (*      =={b u =={Δ;e} b v} dcong_tel b e). *)

  (* @square_tel (Δ v) _ _ _ _ (cong_tel (subst (λ ρ : Γ, Δ ρ) e) _ _ r) s lhs rhs. *)

  Definition transport_u 
             {Δ : Tel} (Γ : Δ -> Tel)
             (f : forall x : Δ, Γ x) (P : forall (x : Δ), Γ x -> Type) 
             (s : Δ) (u : P _ (f s)) :
    P s (subst (fun x => telescope (Γ x)) (refl s) (f s)).
  Proof.
    unfold subst. rewrite J_refl. exact u.
  Defined.

    
  Lemma equiv_cong_subst_tel_dep {Δ : Tel} (Γ : Δ -> Tel)
        (f : forall x : Δ, Γ x) (P : forall (x : Δ), Γ x -> Type) 
        (s t : Δ) (e : s =={Δ} t) (u : P _ (f s))
        (v : P t (f t)) :
    u ==_{(fun x => P x (f x)); e} v <~>
         (J _ (fun y e => P y (subst _ e (f s)))
            (transport_u Γ f P s u) _ e ==_{(fun x => P _ x); dcong_tel f e} v).
  Proof.
    unfold subst. revert t e v. refine (J _ _ _). intros.
    rewrite J_refl. unfold transport_u. unfold eq_rect_r. simpl.
  Admitted.     (* Not so sure this is provable *)

  Definition lifted_solution_rhs_type (Γ : Tel) (u v : Γ) (Γ' : Tel)
        (Δ : Γ -> Tel) 
        (a b : forall ρ, Δ ρ)
        (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ)
        (r : a u =={Δ u} b u)
        (s : a v =={Δ v} b v)
        (f : extend_tele Γ (fun ρ => eq (Δ ρ) (a ρ) (b ρ)) <~> Γ') :=
    f (inj_extend_tel Γ eqΔ u r) =={Γ'} f (inj_extend_tel Γ eqΔ v s).

  Definition lifted_solution (Γ : Tel) (u v : Γ) (Γ' : Tel)
        (Δ : Γ -> Tel) 
        (a b : forall ρ, Δ ρ)
        (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ)
        (r : eqΔ u) (s : eqΔ v)
        (f : extend_tele Γ eqΔ <~> Γ') :
    lifted_solution_lhs_type Γ u v Δ a b r s <~>
    lifted_solution_rhs_type Γ u v Γ' Δ a b r s f.
  Proof.
    unfold lifted_solution_rhs_type.
    unfold lifted_solution_lhs_type.
    refine (equiv_compose _ _).
    unshelve refine (@equiv_tele_r _ _ _ _). 
    intros x.
    set(lhs:=dcong_tel a x).
    set(rhs:=dcong_tel b x).
    unfold eqΔ in r, s.
    exact (@square _ _ _ _ _
                   (inv_equiv (eq_points_equiv _ _ _) lhs)
                   (inv_equiv (eq_points_equiv _ _ _) rhs)
                   (cong _ _ _ r)
                   (inv_equiv (eq_points_equiv (Δ v) (a v) (b v)) s)
          ). simpl.
    intros x.
    apply flip_square_equiv.
    pose (cong_equiv (extend_tele Γ eqΔ) (inj_extend_tel Γ eqΔ u r) (inj_extend_tel Γ eqΔ v s) _ f _).
    refine (equiv_compose _ _).
    Focus 2.
    refine (eq_points_equiv _ _ _).
    refine (equiv_compose _ _). Focus 2.
    refine e.
    
    refine (equiv_compose _ _).
    refine (equiv_sym _).
    cbv beta zeta.
    refine
      (reorder_tele
         (u =={Γ} v)
         (fun x =>
            inj (square (inv_equiv (eq_points_equiv (Δ v) (subst (λ x0 : Γ, Δ x0) x (a u)) (a v)) (dcong_tel a x))
                        (inv_equiv (eq_points_equiv (Δ v) (subst (λ x0 : Γ, Δ x0) x (b u)) (b v)) (dcong_tel b x))
                        (cong (subst (λ x0 : Γ, Δ x0) x) (a u) (b u) r)
                        (inv_equiv (eq_points_equiv (Δ v) (a v) (b v)) s)))).
    

    
    
    clear. unfold eqΔ. simpl.
    induction Γ.

    - simpl extend_tele.
      simpl inj_extend_tel.
      refine (equiv_tele_r _). intros x. revert v x s. refine (Top.J _ _). intros s.
      simpl. unfold square. unfold dcong_tel. simpl.
      unfold Telescopes.dcong_tel_obligation_1. simpl.
      subst eqΔ. simpl in *.
      unfold subst. simpl.
      unfold eq_over_refl. simpl. unfold eq_rect_r. simpl.
      set (au := a u) in *.
      set (bu := b u) in *.
      unfold dcong_tel. simpl.
      clearbody bu. clearbody au.
      revert bu r s.
      refine (J _ _ _). intros s.
      unfold cong.
      rewrite J_refl.
      unfold inv_equiv, eq_points_equiv. unfold equiv_inv. simpl.
      (* Rew equivalence *)
      rewrite eq_eq_equiv_inv_refl. simpl.
      
      unshelve refine {| equiv a := _ |}.
      apply (Top.cong (equiv (eq_points_equiv (Δ u) au au))) in a.
      unfold equiv in a. simpl in a.
      unfold inv_equiv in a. simpl in a.
      rewrite eq_eq_equiv_refl in a. symmetry in a.
      destruct a.
      pose proof (eisretr (eq_eq_equiv (Δ u) au au)). red in H.
      specialize (H s). rewrite H. apply refl.
      
      unshelve refine {| equiv_inv a := _ |}.
      revert s a. refine (J _ _ _).
      symmetry. apply eq_eq_equiv_inv_refl.

      + red. intros.
        revert s x. refine (J _ _ _).
        simpl. unfold eq_sym, Logic.eq_ind. simpl.

        apply axiom.
      + apply axiom.
      + apply axiom.

    - apply axiom.
    
    (* apply eq_eq_equiv. *)
    (* unfold Top.subst. simp. *)
    (* apply refl. *)

    (* unshelve refine {| equiv_inv a := _ |}. *)
    (* unfold eq_expl in *. *)
    (* revert s a. refine (J _ _ _). *)
    (* symmetry. apply eq_eq_equiv_inv_refl. *)

    (* - red; intros. *)
    (*   unfold eq_expl in *. *)
    (*   revert s x. refine (J _ _ _). *)
    (*   unfold Logic.eq_ind. *)
    (*   rewrite J_refl. *)
    (*   unfold inv_equiv_equiv. *)
    (*   apply axiom. *)

    (* - apply axiom. *)
    (* - apply axiom. *)

    (* - simpl.  *)
    (*   refine (equiv_tele_r _). destruct u, v. intros ->. *)
    (*   simpl. apply axiom. *)
  Defined.
  
  Lemma inj_extend_tel_tele (Γ : Tel) (Δ : Γ -> Tel)
        u v a b (f := fun ρ => a ρ =={Δ ρ} b ρ)
        (r : f u) (s : f v) :
    inj_extend_tel Γ f u r =={extend_tele Γ f} inj_extend_tel Γ f v s
                                               <~> tele (x : u =={Γ} v) in
      (subst (fun y => telescope (b u =={Δ;x} y)) s
             (subst (fun y => telescope (y =={Δ;x} a v)) r (dcong_tel a x))
       =={b u =={Δ;x} b v} dcong_tel b x).
  Proof.
  Admitted.    
  
        (* square_tel (dcong_tel a x) (dcong_tel b x) (cong_tel (subst Δ x) _ _ r) s. *)
      
  (* Definition lifted_solution' (Γ : Tel) (u v : Γ) (Γ' : Tel) *)
  (*       (Δ : Γ -> Tel)  *)
  (*       (a b : forall ρ, Δ ρ) *)
  (*       (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ) *)
  (*       (r : eqΔ u) (s : eqΔ v) *)
  (*       (f : extend_tele Γ eqΔ <~> Γ') : *)
  (*   lifted_solution_lhs_tel_type Γ u v Δ a b r s <~> *)
  (*   lifted_solution_rhs_type Γ u v Γ' Δ a b r s f. *)
  (* Proof. *)
  (*   unfold lifted_solution_rhs_type. *)
  (*   unfold lifted_solution_lhs_tel_type. *)
  (*   refine (equiv_compose _ _). *)
  (*   refine (equiv_sym _). *)
  (*   refine (equiv_compose _ _). *)
  (*   refine (inj_extend_tel_tele Γ Δ u v a b r s). *)
  (*   refine (equiv_tele_r _). *)
  (*   intros x. *)
  (*   unfold square_tel. *)
    
  (*   simpl. *)
  (*   unfold theorem_square. *)
  (*   unfold square_tel. *)
  (*   set (lhs := dcong_tel a x). *)
  (*   set (rhs := dcong_tel b x). *)
  (*   pose (@equiv_cong_subst_tel (Δ v)). *)
  (*   Unset Printing Notations. unfold eq_expl. *)
    
  (*   Close Scope telescope. *)
  (*   Unset Printing Notations. unfold eq_expl. *)
  (*   specialize (e  *)

  (*   (inj &{ u : Δ v & Δ v }) *)
  (*                                 (fun y => (eq (Δ v) y.1 y.2)) *)
  (*                                 (fun x => &(a v & x)) *)
  (*                                 (subst _ x (b u)) *)
  (*                                 (b v) *)
  (*                                 (dcong_tel b x) lhs s). *)
    

    
    
  (*   pose (cong_equiv (extend_tele Γ eqΔ) (inj_extend_tel Γ eqΔ u r) (inj_extend_tel Γ eqΔ v s) _ f _). *)

  (*   set(lhs:=dcong_tel a x). *)
  (*   set(rhs:=dcong_tel b x). *)
  (*   unfold eqΔ in r, s. *)
  (*   exact (@square_tel _ _ _ _ _ lhs rhs (cong_tel _ _ _ r) s). *)
  (*   intros x. (* Anomaly without simpl *) simpl. *)
  (*   apply flip_square_tel_equiv. *)
  (*   refine (equiv_compose _ _). *)
  (*   Focus 2. *)
  (*   refine (eq_points_equiv _ _ _). *)
  (*   refine (equiv_compose _ _). Focus 2. *)
  (*   refine e. *)

  (*   refine (equiv_compose _ _). *)
  (*   refine (equiv_tele_r _). *)
  (*   intro. *)
  (*   refine (equiv_compose _ _). *)
  (*   simpl. *)
  (*   unfold square_tel. *)

  (*   unfold eqΔ in r, s. *)


  (*   pose (@equiv_cong_subst_tel). (Δ v) (inj &{ u : Δ v & Δ v }) *)
    
    
  (*   pose (r =={cong_tel } s). *)

    
  (*   (* P (f v) = a v =={Δ v} b v *) *)
  (*   Check (dcong_tel b u v x). *)
  (*   set (lhs:= subst _ _ (a v) _ _). *)
  (*   pose (@equiv_cong_subst_tel (Δ v) (inj &{ u : Δ v & Δ v }) *)
  (*                                 (fun y => (eq (Δ v) y.1 y.2)) *)
  (*                                 (fun x => &(a v & x)) *)
  (*                                 (subst _ _ _ x (b u)) *)
  (*                                 (b v) *)
  (*                                 (dcong_tel b u v x) lhs s). *)
  (*   Unshelve. 4:intro x. simpl. *)
  (*   refine e0. simpl. *)
  (*   refine (equiv_id _). *)
  (*   refine (equiv_compose _ _). *)
  (*   refine (equiv_sym _). *)
  (*   cbv beta zeta. *)
  (*   refine (reorder_tele (u =={Γ} v) (fun x => _)). *)
    
  (*   clear. *)
    
    

    
  (*   induction Γ. *)

  (*   - simpl extend_tele. *)
  (*     simpl inj_extend_tel. *)
  (*     refine (equiv_tele_r _). intros x. revert v x s. refine (Top.J _ _). intros s. *)
  (*     simpl. unfold square_tel. unfold dcong_tel. simpl. *)
  (*     unfold Telescopes.dcong_tel_obligation_1. simpl. unfold eq_rect_r. *)
  (*     simpl. *)
  (*     subst eqΔ. simpl in *. *)
  (*     unfold subst. simpl. *)
  (*     rewrite J_refl. simpl. *)
  (*     unfold cong_tel.  rewrite J_refl. simpl. *)
      
  (*     set (au := a u) in *. *)
  (*     set (bu := b u) in *. *)
  (*     unfold dcong_tel. simpl. *)
  (*     clearbody bu. clearbody au. *)
  (*     revert bu r s. *)
  (*     refine (J _ _ _). intros s. *)
  (*     rewrite J_refl. apply equiv_id. *)

  (*   - simpl. refine (equiv_tele_r _). intros. *)
  (*     destruct v. simpl in *. subst eqΔ. simpl in *. *)
  (*     revert pr1 x pr2 s.  *)
  (*     refine (Top.J _ _). *)
  (*     simpl. intros. specialize (X u.1 u.2 pr2). *)
  (*     specialize (X (fun ρ => Δ &(u.1 & ρ))). *)
  (*     simpl in X. specialize (X (fun ρ => a &(u.1 & ρ)) *)
  (*                               (fun ρ => b &(u.1 & ρ))). *)
  (*     simpl in X. destruct u. simpl in *. *)
  (*     specialize (X r s). *)
  (*     apply X. *)
  (* Defined. *)
  Definition lifted_solution' (Γ : Tel) (u v : Γ) (Γ' : Tel)
        (Δ : Γ -> Tel) 
        (a b : forall ρ, Δ ρ)
        (eqΔ := λ ρ, a ρ =={Δ ρ} b ρ)
        (r : eqΔ u) (s : eqΔ v)
        (f : extend_tele Γ eqΔ <~> Γ') :
    lifted_solution_lhs_tel_type Γ u v Δ a b r s <~>
    lifted_solution_rhs_type Γ u v Γ' Δ a b r s f.
  Proof.
    unfold lifted_solution_rhs_type.
    unfold lifted_solution_lhs_tel_type.
    refine (equiv_compose _ _).
    unshelve refine (@equiv_tele_r _ _ _ _). 
    intros x.

    set(lhs:=dcong_tel a x).
    set(rhs:=dcong_tel b x).
    unfold eqΔ in r, s.
    exact (@square_tel _ _ _ _ _ (cong_tel _ _ _ r) s lhs rhs ).
    intros x. (* Anomaly without simpl *) simpl.
    unfold theorem_square. apply flip_square_tel_equiv.
    refine (equiv_compose _ _).
    Focus 2.
    refine (eq_points_equiv _ _ _).
    refine (equiv_compose _ _). Focus 2.
    refine (cong_equiv (extend_tele Γ eqΔ)
                       (inj_extend_tel Γ eqΔ u r) (inj_extend_tel Γ eqΔ v s) _ f _).

    refine (equiv_compose _ _).
    refine (equiv_tele_r _).
    intro.
    refine (equiv_compose _ _).
    simpl.
    unfold square_tel.

    unfold eqΔ in r, s.
    set (lhs := dcong_tel a x).
    set (rhs := dcong_tel b x).
    pose (@equiv_cong_subst_tel (Δ u) (Δ v)
                                (fun x => x == a v)
                                (subst Δ x) (a u) (b u) r
                                lhs).
    simpl in e.
    specialize (e (subst (λ x0 : Δ u, subst (λ x : Γ, Δ x) x x0 == a v) r lhs)).
    rewrite e.
    refine (equiv_id _).
    refine (equiv_id _).
    refine (equiv_compose _ _).
    refine (equiv_sym _).
    cbv beta zeta.
    refine (reorder_tele (u =={Γ} v) (fun x => _)).

    clear f.
    induction Γ.
    Transparent telescope eq.

    - simpl extend_tele.
      simpl inj_extend_tel.
      refine (equiv_tele_r _). intros x. revert v x s. refine (Top.J _ _). intros s.
      simpl. unfold square_tel. unfold dcong_tel. simpl.
      unfold Telescopes.dcong_tel_obligation_1. simpl. unfold eq_rect_r.
      simpl.
      subst eqΔ. simpl in *.
      unfold subst. simpl.
      
      set (au := a u) in *.
      set (bu := b u) in *.
      clearbody bu. clearbody au.
      revert bu r s.
      refine (J _ _ _). intros s.
      rewrite J_refl.
      apply axiom.
      

    - simpl. refine (equiv_tele_r _). intros.
      destruct v. simpl in *. subst eqΔ. simpl in *.
      revert pr1 x pr2 s. 
      refine (Top.J _ _).
      simpl. intros. specialize (X u.1 u.2 pr2).
      specialize (X (fun ρ => Δ &(u.1 & ρ))).
      simpl in X. specialize (X (fun ρ => a &(u.1 & ρ))
                                (fun ρ => b &(u.1 & ρ))).
      simpl in X. destruct u. simpl in *.
      specialize (X r s).
      apply X.
  Defined.
    
  Lemma lower_solution' :
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

    apply axiom. apply axiom. apply axiom.
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
    refine (injectivity_cons2 &(x, n & v) &(y, n & v')). simpl.
    pose (lower_solution' A n).
    pose (inv_equiv e &(x & v)).
    simpl in e.
    pose (telei x n in v : telu A).
    pose (sol:=lifted_solution'
                 (tele (_ : A) (n' : nat) in vector A n')).
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
    specialize (sol (fun x => inj nat)). (* inj (S x.1 = S x.1))). *)
    simpl in e.
    specialize (sol (fun x => S x.2.1) (fun x => S n) eq_refl eq_refl). simpl in sol.
    specialize (sol e). subst e.
    unfold lifted_solution_lhs_type, lifted_solution_lhs_tel_type, lifted_solution_rhs_type in sol.
    simpl in sol.
    unfold theorem_square, solution_left in *.
    simpl in *.
    unfold inv_equiv in sol. unfold eq_points_equiv in sol. simpl in *.
    unfold equiv_inv in *. simpl in *.
    unfold cong in sol. simpl in *.
    
    refine (equiv_compose (C:=tele (e : x = y) in (v ={ (λ _ : A, inj (vector A n)); e} v'))
                          _ sol).
    refine (equiv_tele_r _).
    intros.
    unfold square_tel.
    (*   Lemma equiv_cong_subst_tel {Δ Γ : Tel} (P : Γ -> Tel) (f : Δ -> Γ)
        (s t : Δ) (e : s =={Δ} t) (u : P (f s))
        (v : P (f t)) :
    subst P (cong_tel f _ _ e) u = subst (fun x => P (f x)) e u.
     *)
    Lemma subst_dcong_tel  {Δ} {Γ : Δ -> Tel}
          (P : forall x: Δ, Γ x -> Tel) (f : forall x : Δ, Γ x)
        (s t : Δ) (e : s =={Δ} t) (u : P (f s))
        (v : P (f t)) :
    subst P (dcong_tel f _ _ e) u = 
    
    unfold cong_tel. simpl.
    unfold subst. simpl.
    
    simpl.
    rewrite (equiv_cong_subst_tel 
    Transparent telescope eq. unfold telescope.
    simpl. 
    Opaque eq telescope.
    simpl. unfold subst. simpl.
    unfold equiv_sym. 
    unfold injectivity_cons2. simpl.
    unfold noconf_equiv, equiv, inv_equiv, equiv_inv. simpl.
    Transparent  eq telescope.
    simpl.

  
  unfold noconf_equiv, equiv, inv_equiv, equiv_inv. simpl.
  clear sol. subst solinst.
  unfold square_tel.
  unfold subst. simpl.
  simpl.
  refine (equiv_compose _ _).
  Focus 2.
  pose (@equiv_cong_subst_tel).
  specialize (e () 

  
  Lemma dcong_tel_cong_tel (Δ Γ : Tel) (f : Γ) (u v : Δ) (e : u =={Δ} v) :
    f =={fun _ => Γ; e} f <~> f == f.
  Proof.
    revert v e.
    refine (J _ _ _).
    unfold subst. rewrite J_refl. apply equiv_id.
  Defined.

  Lemma dcong_tel_cong_tel' (Δ Γ : Tel) (f : Γ) (u v : Δ) (e : u =={Δ} v) :
    f =={fun _ => Γ; e} f = (f == f).
  Proof.
    revert v e.
    refine (J _ _ _).
    unfold subst. rewrite J_refl. reflexivity.
  Defined.

  (* Lemma dcong_tel_nondep_simplify (Δ Γ : Tel) (f f' : Δ -> Γ) (u v : Δ) (e : u =={Δ} v) : *)
  (*       let lhs := @dcong_tel Δ (fun _ => Γ) f u v e in *)
  (*       let rhs := @dcong_tel Δ (fun _ => Γ) f' u v e in *)
  (*       lhs = rhs <~>(forall x : Δ, f x = f' x). *)

  
  (*     (rhs := @cong_tel Δ Γ (fun _ => f) u v e) : Type. *)
  (*   simpl in *.  *)
  (*   pose (subst (fun _ => Γ) u v e). *)
  (*   unfold eq_expl in *. *)
  
  
  
  set (rhs := dcong_tel _ _ _ _) at 2.
  simpl in rhs. unfold telescope in rhs.
  

  
  pose (dcong_tel_cong_tel' (tele (x : A) (x0 : nat) in vector A x0) (inj nat) (S n)
        &(x, n & v) &(y, n & v') x0).
  pose (Top.subst (P:=fun X : Tel => telescope X) e rhs).
  pose (@cong_tel (tele (x : A) (x0 : nat) in vector A x0) (inj nat)
                              (fun _  => S n)  &(x, n & v) &(y, n & v') x0).
  simpl in t3. simpl in t2.
  set(bar:=dcong_tel _ _ _ _). simpl in bar.
  
  
  Lemma dcong_tel_cong_tel_coerce (Δ Γ : Tel) (f : Γ) (u v : Δ) (e : u =={Δ} v)
        (lhs := @dcong_tel Δ (fun _ => Γ) (fun _ => f) u v e) 
      (rhs := @cong_tel Δ Γ (fun _ => f) u v e) : Type.
    simpl in *. 
    pose (subst (fun _ => Γ) u v e).
    unfold eq_expl in *.

    
  
  (*
  A : Type
  n : nat
  x, y : A
  v, v' : vector A n
  t0 := &(x, n, v & eq_refl) : tele (_ : A) (n' : nat) (_ : vector A n') in (S n' = S n)
  t1 := &(x, n & v) : telu A
  x0 : tele (e : x = y) (e0 : (rew e in &(n & v)).1 = n) in
         ((rew e in &(n & v)).2 ={ λ x : nat, inj (vector A x); e0} v')
  ============================
  (cong_tel (λ x1 : &{ _ : A & &{ x2 : nat & vector A x2}}, &(S (x1.2).1 & Vector.cons x1.1 (x1.2).2))
     &(x, n & v) &(y, n & v') x0).1 = eq_refl <~>
  dcong_tel (λ x1 : &{ _ : A & &{ x2 : nat & vector A x2}}, S (x1.2).1) &(x, n & v) &(y, n & v') x0 =
  dcong_tel (λ _ : &{ _ : A & &{ x2 : nat & vector A x2}}, S n) &(x, n & v) &(y, n & v') x0
*)

  
  unfold dcong_tel. unfold Telescopes.dcong_tel_obligation_1. unfold eq_rect_r.
  unfold J_refl. simpl.

  set(lhs := cong_tel _ _ _ _). simpl in lhs.
  set(rhs1 := dcong_tel _ _ _ _).
  set(rhs2 := dcong_tel _ _ _ _). simpl in *.

  unfold dcong_tel.
  
  
  apply axiom.

  refine (equiv_id _).
  Defined.

  Eval compute in (pr1 (@example nat)).
  
  unfold cong_tel. subst solinst.
  destruct x0. destruct pr2. simpl.
  unfold dcong. simpl.
  
  
  specialize (sol x0).

  Goal forall {A} n (x y : A) (v v' : Vector.t A n)
              (e : Vector.cons x v = Vector.cons y v')
            (P : forall n x y v v' (e : Vector.cons x v = Vector.cons y v'), Type),
      (P n x x v v eq_refl) -> P n x y v v' e.
Proof.
  intros. revert e P X.
  refine (solution_inv _ _ _ _ _ _).
  refine (uncurry _).
  
  Lemma apply_equiv_dom {A B} (P : B -> Type) (e : Equiv A B) :
    (forall x : A, P (equiv e x)) -> forall x : B, P x.
  Proof.
    intros.
    specialize (X (e ^-1 x)).
    rewrite inv_equiv_equiv in X. exact X.
  Defined.
  
  unshelve refine (apply_equiv_dom _ _ _).
  shelve.
  refine (equiv_tele_l _).
  refine (equiv_sym _).
  refine (injectivity_cons &(x, n & v) &(y, n&v')).
  
  intros.
  pose (lower_solution' A n).
  pose (inv_equiv e &(x & v)).
  simpl in e.
  pose (telei x n in v : telu A).
  pose (sol:=lifted_solution
          (tele (_ : A) (n' : nat) in vector A n')).
  simpl in sol.
  simpl in t0.
  set (solinst :=
         sigmaI (fun x => sigma nat (fun n => vector A n)) t0.1 &(t0.2.1 & t0.2.2.1)).
  specialize (sol solinst).
  specialize (sol &(y, n & v')).
  (* specialize (sol solinst). (*&(y, n & v')).*) *)
  specialize (sol (telv A n)).
  specialize (sol (fun x => inj nat)). (* inj (S x.1 = S x.1))). *)
  simpl in e.
  specialize (sol (fun x => S x.2.1) (fun x => S n) eq_refl eq_refl). simpl in sol.
  specialize (sol e). subst e.
  simpl in sol.
  unfold solution_left in *.
  simpl in *.
  
  simpl in *.
  unfold inv_equiv in sol. unfold eq_points_equiv in sol. simpl in *.
  unfold equiv_inv in *. simpl in *.
  unfold dcong in sol. 
  specialize (sol x0).
  
  unfold subst in sol. simpl in sol.
  
  pose (inv_equiv sol).
  specialize (s &(pr1 & pr3)).
  destruct s as (s & s').
  destruct s as [Hx
  simpl in s'.
  simpl in s.
    
    unfold equiv, equiv_inv, inv_equiv in H. simpl in H.
    unfold injectivity_cons in H. simpl in H.
    unfold eq_points_equiv in H. simpl in *.
    unfold inv_equiv at 1 in H. simpl in H.
    unfold equiv_compose in H. simpl in *.
    unfold compose in H. simpl in H.
    unfold pr1_seq in H. simpl in *.
    unfold noconf_equiv in H. simpl in H.
    unfold compose in H. simpl in H.
    unfold equiv, equiv_inv, inv_equiv in H. simpl in H.
    unfold isequiv_compose in H. simpl in H.
    unfold compose in H. simpl in H.
    unfold equiv_inv in H. simpl in H.
    unfold path_sigma_equivalence in H.
    simpl in H. unfold equiv in H.
    
    unfold path_sigma_uncurried in H.
    simpl in H.
    simpl.
    revert P X.
    unfold equiv_sym, equiv, equiv_inv, injectivity_cons. simpl.
    unfold equiv_compose, equiv, equiv_inv, injectivity_cons. simpl.
    unfold inv_equiv, equiv, equiv_inv, injectivity_cons. simpl.
    unfold compose. unfold rewh.
    unfold eq_expl. unfold subst. unfold eq_rect.
    simpl.
    pose (inv_equiv e &(eq_refl & eq_refl)).
    
    pose (equiv_inv e).
    
    
    simpl.
    compute.
    
    
    set (foo:=(equiv_sym (injectivity_cons &(x, n & v) &(y, n & v'))) a) in *.
    
    
    specialize (equiv0 H).
    unfold inv_equiv in equiv0.
    unfold equiv_inv in equiv0. simpl in equiv0.
    unfold cong in equiv0. simpl in equiv0.
    simpl in equiv0.
    specialize (equiv0 t1.2.2.2).
    unfold dcong in equiv0. simpl in equiv0.
    specialize (equiv0 eq_refl).
    unfold solution_left in equiv0. simpl in equiv0.
    clear t0 t1.
    
    rewrite dcong_refl in equiv0.
    specialize (equiv0 eq_refl).
    
    curry equiv0.
    specialize (equiv0 eq_refl).

    destruct a.
    
    simpl in e.

  
  Goal
    forall A n (x y : A) (xs : vector A n) (ys : vector A n)
           (r : n = n),
      &(n, x, xs) 
      tele (e1 : n = n) (e2 : x = y) (e3 : xs = ys) in (Top.cong S e1 = eq_refl)
    <~>
      tele (e2'' : x = y) in (xs = ys).
  Proof.
    intros.
    pose (lifted_solution ).
    pose (lower_solution' A n).

    pose (telei n x in xs : telu A).
    simpl in e.
    pose (inv_equiv e0 &(x & xs)).
    specialize (e (tele (n' : nat) (_ : A) in vector A n')). 
    specialize (e &(t1.1, t1.2.1 & t1.2.2.1)).
    specialize (e &(t1.1, t1.2.1 & t1.2.2.1)).
    specialize (e (telv A n)).
    specialize (e (fun x => inj nat)). (* inj (S x.1 = S x.1))). *)
    simpl in e. specialize (e (fun x => S x.1) (fun x => S n)).
    simpl in e. specialize (e t1.2.2.2 t1.2.2.2). simpl in e.
    specialize (e e0). subst e0.
    simpl in e.
    destruct e.
    simpl in *.
    unshelve refine {| equiv a := _ |}.
    
    
    simpl in e.
    
    
    specialize (e (tele (n' : nat) (_ : A) (_ : vector A n') in (S n' = S n))).
    specialize (e t1 t1). specialize (e (telv A)).
    specialize (e (fun x => inj unit)).
    specialize (e (fun x => tt) (fun x => tt)).
    specialize (e eq_refl eq_refl). simpl in e.
    


    
    specialize (e (telu A) t0 t0 (telv A)). 
    specialize (e (fun ρ => inj (S ρ.1 = S n))).
        
    
    unshelve refine {| equiv a := _ |}.
    
    specialize (e (fun ρ => S n)).
    
    simpl in e.
    
    
    
    
    match goal with
      H : telescope ?u <~> telescope ?v |- _ =>
      set (telu:= u) in *; set (telv := v) in *
    end.
    pose (cong_equiv telu (telei n x xs in (Top.cong S r)) (telei n y ys in eq_refl)).
    specialize (e0 _ (equiv e) _).

  
  Lemma lifted_solution :
    forall A n (x y : A) (xs : vector A n) (ys : vector A n)
           (r : n = n),
      tele (e1 : n = n) (e2 : x = y) (e3 : xs = ys) in (Top.cong S e1 = eq_refl)
    <~>
      tele (e2'' : x = y) in (xs = ys).
  Proof.
    intros.
    set (foo :=telu A n).
    pose ((telei n x xs in (Top.cong S r)) : telu A n).
    
    pose (lower_solution' A n).
    match goal with
      H : telescope ?u <~> telescope ?v |- _ =>
      set (telu:= u) in *; set (telv := v) in *
    end.
    pose (cong_equiv telu (telei n x xs in (Top.cong S r)) (telei n y ys in eq_refl)).
    specialize (e0 _ (equiv e) _).
    

    
    refine (equiv_compose _ _).
    

    
    Lemma equiv_teleeq {A : Type} (Δ : A -> Tel) (f g : forall x : A, Δ x) (x y : A) :
      (&(x & f x) =={ext A Δ} &(y & g y)) <~> 
      ext (x = y) (fun e1 => rewP e1 at (fun x => telescope (Δ x)) in f x =={Δ y} g y).
    Proof.
    Admitted.


    
    refine (equiv_teleeq (fun A => tele (_ : x = y) (_ : xs = ys) in (Top.cong S e1 = eq_refl)) _ _ _ _).

    

  Lemma lifted_solution :
    forall A n (x y : A) (xs : vector A n) (ys : vector A n),
      tele (e1 : n = n) (e2 : x = y) (e3 : xs = ys) in (Top.cong S e1 = eq_refl)
    <~>
      tele (e2'' : x = y) in (xs = ys).
  Proof.
    intros.
    refine (equiv_compose _ _).
    pose (lower_solution' A n).
    match goal with
      H : telescope ?u <~> telescope ?v |- _ =>
      set (telu:= u) in *; set (telv := v) in *
    end.
    pose (cong_equiv telu (telei n x xs in eq_refl) (telei n y ys in eq_refl)).
    specialize (e0 _ (equiv e) _).
    

    
    (* Lemma fold_teleq (Δ : Tel) (u v : Δ) : u =={Δ} v -> (u = v). *)
    (*   match goal with *)
    (*   H : telescope ?x <~> telescope ?y |- _ => *)
    (*   pose (cong_equiv _ x y _ e) *)
    (* end. *)
    pose (cong_equiv 
    
  
Goal forall {A} n (x y : A) (v v' : Vector.t A n) (e : Vector.cons x v = Vector.cons y v')
            (P : forall n x y v v' (e : Vector.cons x v = Vector.cons y v'), Type),
    (P n x x v v eq_refl) -> P n x y v v' e.
Proof.
  intros. revert e P X.
  refine (solution_inv _ _ _ _ _ _).
  refine (uncurry _).
  change (  forall (s : tele (x0 : &(S n & Vector.cons x v) = &(S n & Vector.cons y v')) in (pr1_seq x0 = eq_refl))
    (P : forall (n0 : nat) (x0 y0 : A) (v0 v'0 : vector A n0),
         Vector.cons x0 v0 = Vector.cons y0 v'0 -> Type),
  P n x x v v eq_refl -> P n x y v v' (rewh s.1 s.2)).

  Lemma apply_equiv_dom {A B} (P : B -> Type) (e : Equiv A B) :
    (forall x : A, P (equiv e x)) -> forall x : B, P x.
  Proof.
    intros. Admitted.

  
  unshelve refine (apply_equiv_dom _ _ _).
  shelve.
  refine (equiv_compose _ _). shelve.
  unshelve refine (equiv_tele_l _).
  shelve. 
  refine (equiv_sym _).
  refine (injectivity_cons &(x, n & v) &(y, n&v')).
  Unshelve.
  all:cycle 1. shelve.
  Opaque telescope.
  simpl.
  unfold injectivity_cons. simpl.
  Transparent telescope.
  (* Anomaly *)
  (* pose (reorder_tele (tele (e : x = y) (e0 : (rew e in &(n & v)).1 = n) in ((rew e in &(n & v)).2 =_{ *)
  (*                                                           fun x0 : nat =>  *)
  (*                                                           inj (vector A x0);e0} v')) _). *)
  
  unshelve refine (equiv_tele_l _). shelve.
  
  

  
  simpl.
  
  
  
  Lemma equiv_tele_l {A} {A'} {B : A' -> Type} (e : Equiv A A') :
    tele (x : A) in B (equiv e x) <~> tele (x : A) (b : rew e in c ) in C x b.
  Proof.
    simpl.
  Admitted.

  
  
  



  refine (simpleeq _).
  refine (geninj_eq_inv_goal (fun A n x y v v' e =>
                         forall (e' : pr1_seq (pack_pathover (cons x v) (cons y v') e) = eq_refl)
    (P : forall (n0 : nat) (x0 y0 : A) (v0 v'0 : vector A n0), cons x0 v0 = cons y0 v'0 -> Type),
  P n x x v v eq_refl -> P n x y v v' (rewh (pack_pathover (cons x v) (cons y v') e) e')) _).
  intros e.

  pose proof (pr2_seq_pack_pathover (geninj_eq e)).
  set (pr1_seq_pack_pathover (geninj_eq e)) in *.
  clearbody e0.
  unfold rewh.
  rewrite H.
  rewrite e0. clear e0 H.
  revert e.
  intros [e]. revert pr2. intros [e' e''].
  simpl pr1.
  cbn -[geninj_eq].


