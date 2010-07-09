Require Import Program Equations Bvector List.
Require Import Relations.
Require Import DepElimDec.


Instance eqsig {A} (x : A) : Signature (x = x) A :=
  { signature a := x = a ;
    signature_pack e := existT _ x e }.

Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
K A x P p eq_refl := p.

Equations eq_sym {A} (x y : A) (H : x = y) : y = x :=
eq_sym A x x eq_refl := eq_refl.

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans A x x x eq_refl eq_refl := eq_refl.

Notation " x |:| y " := (@Vcons _ x _ y) (at level 20, right associativity) : vect_scope.
Notation " x |: n :| y " := (@Vcons _ x n y) (at level 20, right associativity) : vect_scope.
Notation " [[ x .. y ]] " := (Vcons x .. (Vcons y Vnil) ..) : vect_scope.
Notation " [[]] " := Vnil : vect_scope.

Open Local Scope vect_scope.

Equations (nocomp) vapp' {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vapp' A ?(0) m [[]] w := w ;
vapp' A ?(S n) m (Vcons a n v) w := Vcons a (vapp' v w).

Print Assumptions vapp'.

Inductive Split {X : Type}{m n : nat} : vector X (m + n) -> Type :=
  append : Π (xs : vector X m)(ys : vector X n), Split (vapp' xs ys).

Implicit Arguments Split [ [ X ] ].

Equations(nocomp) filter {A} (l : list A) (p : A -> bool) : list A :=
filter A [] p := [] ;
filter A (cons a l) p <= p a => {
  | true := a :: filter l p ;
  | false := filter l p }.

Inductive incl {A} : relation (list A) :=
  stop : incl nil nil 
| keep {x : A} {xs ys : list A} : incl xs ys -> incl (x :: xs) (x :: ys)
| skip {x : A} {xs ys : list A} : incl xs ys -> incl (xs) (x :: ys).

Global Transparent filter.

Equations(nocomp) sublist {A} (p : A -> bool) (xs : list A) : incl (filter xs p) xs :=
sublist A p nil := stop ;
sublist A p (cons x xs) with p x := {
  | true := keep (sublist p xs) ;
  | false := skip (sublist p xs) }.

Print Assumptions sublist.

Ltac rec ::= rec_wf_eqns.

(* Derive Subterm for nat.  *)
Derive Subterm for vector.

Require Import Arith Wf_nat.
Instance wf_nat : WellFounded lt := lt_wf.
Hint Resolve lt_n_Sn : lt.
Ltac solve_rec ::= simpl in * ; cbv zeta ; intros ; 
  try typeclasses eauto with subterm_relation Below lt.

Equations testn (n : nat) : nat :=
testn n by rec n lt :=
testn 0 := 0 ;
testn (S n) <= testn n => {
  | O := S O ;
  | (S n') := S n' }.

Recursive Extraction testn.

Derive Signature for vector.

Require Import EqDec.

Instance vector_eqdec {A n} `(EqDec A) : EqDec (vector A n). 
Proof. intros. intros x. induction x. left. now depelim y.
  intro y; depelim y.
  destruct (eq_dec a a0); subst. 
  destruct (IHx y0). subst.
  left; reflexivity.
  right. intro. apply n. injection H0. simpdep. reflexivity.
  right. intro. apply n. injection H0. simpdep. reflexivity.
Defined.

Print Assumptions well_founded_vector_direct_subterm.

(** A closed proof of well-foundedness relying on the decidability
   of [A]. *)

Definition vector_subterm' A := vector_subterm A.

Instance well_founded_vector_direct_subterm' :
  forall A : Type, EqDec A -> WellFounded (vector_subterm' A) | 0.
Proof. intros.
apply Transitive_Closure.wf_clos_trans.
  intro. simp_exists. induction X0. constructor; intros.
  simp_exists. depelim H.
  constructor; intros.
  simp_exists. depelim H.
  assumption.
Defined.

Instance eqdep_prod A B `(EqDec A) `(EqDec B) : EqDec (prod A B).
Proof. intros. intros x y. decide equality. Defined.

Hint Unfold vector_subterm' : subterm_relation.
Typeclasses Opaque vector_subterm'.

(* Ltac generalize_by_eqs id ::= generalize_eqs id. *)
(* Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars id. *)

Equations unzip_dec {A B} `{EqDec A} `{EqDec B} {n} (v : vector (A * B) n) : vector A n * vector B n :=
unzip_dec A B _ _ n v by rec v (@vector_subterm' (A * B)) :=
unzip_dec A B _ _ ?(O) Vnil := (Vnil, Vnil) ;
unzip_dec A B _ _ ?(S n) (Vcons (pair x y) n v) with unzip_dec v := {
  | (pair xs ys) := (Vcons x xs, Vcons y ys) }.

Equations unzip {A B} {n} (v : vector (A * B) n) : vector A n * vector B n :=
unzip A B n v by rec v (@vector_subterm (A * B)) :=
unzip A B ?(O) Vnil := (Vnil, Vnil) ;
unzip A B ?(S n) (Vcons (pair x y) n v) <= unzip v => {
  | (pair xs ys) := (Vcons x xs, Vcons y ys) }.

Print Assumptions unzip.
Print Assumptions unzip_dec.

(*
Ltac generalize_by_eqs v ::= generalize_eqs v.

Equations(nocomp) unzip_n {A B} {n} (v : vector (A * B) n) : vector A n * vector B n :=
unzip_n A B O Vnil := (Vnil, Vnil) ;
unzip_n A B (S n) (Vcons (pair x y) n v) with unzip_n v := {
  | pair xs ys := (Vcons x xs, Vcons y ys) }. *)

Equations nos_with (n : nat) : nat :=
nos_with n by rec n :=
nos_with O := O ;
nos_with (S m) with nos_with m := {
  | O := S O ;
  | S n' := O }.

Hint Unfold noConfusion_nat : equations.


Equations split {X : Type} {m n} (xs : vector X (m + n)) : Split m n xs :=
split X m n xs by rec m :=
split X O    n xs := append Vnil xs ;
split X (S m) n (Vcons x ?(m + n) xs) <= split xs => {
  | append xs' ys' := append (Vcons x xs') ys' }.

Equations(nocomp) equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := in_left ;
equal (S n) (S m) <= equal n m => {
  equal (S n) (S n) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := in_right } ;
equal x y := in_right.
Print Assumptions equal.
Equations app_with {A} (l l' : list A) : list A :=
app_with A nil l := l ;
app_with A (cons a v) l <= app_with v l => {
  | vl := cons a vl }.

Print Assumptions app_with.
(* About app_with_elim. *)
(* Print app_with_ind. *)
(* Print app_with_ind_ind. *)

(* Scheme app_with_elim := Minimality for app_with_ind Sort Prop *)
(*   with app_with_help_elim := Minimality for app_with_ind_1 Sort Prop. *)

(* About app_with_elim. *)

Equations plus' (n m : nat) : nat :=
plus' O n := n ; 
plus' (S n) m := S (plus' n m).

(* Ltac generalize_by_eqs id ::= generalize_eqs id. *)
(* Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars id. *)

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.

Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b. funelim (neg b); auto. Qed.

Equations head A (default : A) (l : list A) : A :=
head A default nil := default ;
head A default (cons a v) := a.

Equations tail {A} (l : list A) : list A :=
tail A nil := nil ;
tail A (cons a v) := v.

(* Eval compute in @tail. *)
(* Eval compute in (tail (cons 1 nil)). *)

Equations app' {A} (l l' : list A) : (list A) :=
app' A nil l := l ;
app' A (cons a v) l := cons a (app' v l).

Global Transparent app'.

Notation  " x +++ y " := (@app' _ x y)  (at level 60, right associativity).

Equations rev_acc {A} (l : list A) (acc : list A) : list A :=
rev_acc A nil acc := acc;
rev_acc A (cons a v) acc := rev_acc v (a :: acc).

Equations rev {A} (l : list A) : list A :=
rev A nil := nil;
rev A (cons a v) := rev v +++ [a].


Lemma app'_nil : forall {A} (l : list A), l +++ [] = l.
Proof. intros. Opaque app'.
  funelim (app' l []). reflexivity.
  rewrite H. reflexivity.
Qed.

Lemma app'_assoc : forall {A} (l l' l'' : list A), (l +++ l') +++ l'' = app' l (app' l' l'').
Proof. intros. Opaque app'. revert l''.
  funelim (l +++ l'); intros; simp app'. 
  rewrite H. reflexivity.
Qed.

Lemma rev_rev_acc : forall {A} (l : list A), rev_acc l [] = rev l.
Proof. intros. replace (rev l) with (rev l +++ []) by apply app'_nil.
  generalize (@nil A). 
  funelim (rev l). reflexivity.
  intros l'. simp rev_acc. rewrite H, app'_assoc. reflexivity.
Qed.
Hint Rewrite @rev_rev_acc : rev_acc.

Equations vector_append_one {A n} (v : vector A n) (a : A) : vector A (S n) :=
vector_append_one A ?(0) Vnil a := Vcons a Vnil;
vector_append_one A ?(S n) (Vcons a' n v) a := Vcons a' (vector_append_one v a).

Equations vrev {A n} (v : vector A n) : vector A n :=
vrev A ?(0) Vnil := Vnil;
vrev A ?(S n) (Vcons a n v) := vector_append_one (vrev v) a.

Definition cast {A n m} (v : vector A n) (H : n = m) : vector A m.
intros; subst; assumption. Defined.

Equations(nocomp) vrev_acc {A n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vrev_acc A ?(0) m Vnil w := w;
vrev_acc A ?(S n) m (Vcons a n v) w := cast (vrev_acc v (Vcons a w)) _.
About vapp'.

Record vect {A} := mkVect { vect_len : nat; vect_vector : vector A vect_len }.
Coercion mkVect : vector >-> vect.
Derive NoConfusion for @vect. 
Program Lemma vapp_vector_append_one {A n m} (v : vector A n) (w : vector A m) (a : A) :
  @eq vect (vapp' (vector_append_one v a) w) (vapp' v (Vcons a w)).
Proof. intros. funelim (vector_append_one v a). simp vapp'.
  
  simp vapp'.
  specialize (H _ w). noconf H.

Scheme JMeq_first := Elimination for JMeq Sort Prop.
  About JMeq_first.

  elim H0.
  rewrite (plus_n_Sm n m).
  Print vrev_acc_obligation_1.
  rewrite H.
  repeat
  f_equal.

Lemma vrec_acc_vrec {A n m} v w : @vrev_acc A n m v w = vapp' (vrev v) w.
Proof.
  intros. funelim (vrev v). simp vapp' vrev.
  simp vapp' vrev vrev_acc. rewrite H. 
  
  


Lemma app'_funind : forall {A} (l l' l'' : list A), (l +++ l') +++ l'' = app' l (app' l' l'').
Proof. intros. funelim (l +++ l'); simp app'.
  rewrite H. reflexivity. 
Qed.

Hint Rewrite @app'_nil @app'_assoc : app'.

Lemma rev_app' : forall {A} (l l' : list A), rev (l +++ l') = rev l' +++ rev l.
Proof. intros. funelim (l +++ l'); simp rev app'.
  now (rewrite H, <- app'_assoc).
Qed.

(* Eval compute in @app'. *)

Lemma split_vapp' : Π (X : Type) m n (v : vector X m) (w : vector X n), 
  let 'append v' w' := split (vapp' v w) in
    v = v' /\ w = w'.
Proof.
  intros. funelim (vapp' v w); simp split. intuition.
  destruct (split (vapp' v w)); simp split.
  intuition congruence.
Qed.

Equations zip' {A} (f : A -> A -> A) (l l' : list A) : list A :=
zip' A f nil nil := nil ;
zip' A f (cons a v) (cons b w) := cons (f a b) (zip' f v w) ;
zip' A f x y := nil.

Equations zip'' {A} (f : A -> A -> A) (l l' : list A) (def : list A) : list A :=
zip'' A f nil nil def := nil ;
zip'' A f (cons a v) (cons b w) def := cons (f a b) (zip'' f v w def) ;
zip'' A f nil (cons b w) def := def ;
zip'' A f (cons a v) nil def := def.

(* Eval compute in @zip''. *)

Require Import Bvector.

Equations (nocomp) split_struct {X : Type} {m n} (xs : vector X (m + n)) : Split m n xs :=
split_struct X O    n xs := append Vnil xs ;
split_struct X (S m) n (Vcons x _ xs) <= split_struct xs => {
  split_struct X (S m) n (Vcons x _ xs) (append xs' ys') := append (Vcons x xs') ys' }.

Lemma split_struct_vapp : Π (X : Type) m n (v : vector X m) (w : vector X n),
  let 'append v' w' := split_struct (vapp' v w) in
    v = v' /\ w = w'.
Proof.
  intros. funelim (vapp' v w); simp split_struct. intuition.
  destruct (split_struct (vapp' v w)).
  simp split_struct.
  intuition congruence.
Qed.

Equations vhead {A n} (v : vector A (S n)) : A := 
vhead A ?(n) (Vcons a n v) := a.

Equations vmap' {A B} (f : A -> B) {n} (v : vector A n) : vector B n :=
vmap' A B f ?(O) Vnil := Vnil ;
vmap' A B f ?(S n) (Vcons a n v) := Vcons (f a) (vmap' f v).

Hint Resolve lt_n_Sn : subterm_relation.

Equations vmap {A B} (f : A -> B) {n} (v : vector A n) : vector B n :=
vmap A B f n v by rec n :=
vmap A B f O Vnil := Vnil ;
vmap A B f (S n) (Vcons a n v) := Vcons (f a) (vmap f v).

Transparent vmap.

Transparent vmap'.
(* Eval compute in (vmap' id (@Vnil nat)). *)
(* Eval compute in (vmap' id (@Vcons nat 2 _ Vnil)). *)

(* Eval compute in @vmap'. *)

Section Image.
  Context {S T : Type}.
  Variable f : S -> T.

  Inductive Imf : T -> Type := imf (s : S) : Imf (f s).

  Equations inv (t : T) (im : Imf t) : S :=
  inv ?(f s) (imf s) := s.

End Image.

Section Univ.

  Inductive univ : Set :=
  | ubool | unat | uarrow (from:univ) (to:univ).

  Equations (nocomp) interp (u : univ) : Type :=
  interp ubool := bool; interp unat := nat;
  interp (uarrow from to) := interp from -> interp to.

  (* Eval compute in interp. *)

  Transparent interp.

  Definition interp' := Eval compute in @interp.

  Equations foo (u : univ) (el : interp' u) : interp' u :=
  foo ubool true := false ;
  foo ubool false := true ;
  foo unat t := t ;
  foo (uarrow from to) f := id ∘ f.

  Transparent foo.
  (* Eval lazy beta delta [ foo foo_obligation_1 foo_obligation_2 ] iota zeta in foo. *)

End Univ.

(* Eval compute in (foo ubool false). *)
(* Eval compute in (foo (uarrow ubool ubool) negb). *)
(* Eval compute in (foo (uarrow ubool ubool) id). *)

Inductive foobar : Set := bar | baz.

Equations bla (f : foobar) : bool :=
bla bar := true ;
bla baz := false.

(* Eval simpl in bla. *)

Lemma eq_trans_eq A x : @eq_trans A x x x eq_refl eq_refl = eq_refl.
Proof. reflexivity. Qed.

(* Equations(nocomp) vlast {A} {n} (v : vector A (S n)) : A := *)
(* vlast A O (Vcons a ?(O) Vnil) := a ; *)
(* vlast A (S n) (Vcons a ?(S n) v) := vlast v. *)

Ltac generalize_by_eqs id ::= generalize_eqs id.
Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars id.

Equations(nocomp) vlast' {A} {n} (v : vector A (S n)) : A :=
vlast' A ?(0) (Vcons a O Vnil) := a ;
vlast' A ?(S n) (Vcons a (S n) v) := vlast' v.

Ltac generalize_by_eqs id ::= generalize_eqs_sig id.
Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars_sig id.

Ltac fix_block tac :=
  match goal with
    [ |- ?T ] => tac ; on_last_hyp ltac:(fun id => change (fix_proto T) in id)
  end.

(* Equations (nocomp) vliat {A} {n} (v : vector A (S n)) : vector A n := *)
(* vliat A ?(O) (Vcons a O Vnil) := Vnil ; *)
(* vliat A ?(S n) (Vcons a n v) := Vcons a (vliat v). *)

(* Eval compute in (vliat (Vcons 2 (Vcons 5 (Vcons 4 Vnil)))). *)

Fixpoint vapp {A n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
  match v with
    | Vnil => w
    | Vcons a n' v' => Vcons a (vapp v' w)
  end.

Lemma JMeq_Vcons_inj A n m a (x : vector A n) (y : vector A m) : n = m -> JMeq x y -> JMeq (Vcons a x) (Vcons a y).
Proof. intros until y. simplify_dep_elim. reflexivity. Qed.
  
(* Eval compute in (split (vapp Vnil (Vcons 2 Vnil))). *)
(* Eval compute in (split (vapp (Vcons 3 Vnil) (Vcons 2 Vnil))). *)

(* Recursive Extraction split. *)
(* Transparent split. *)
(* Eval cbv beta iota zeta delta [ split split_obligation_1 split_obligation_2  ] in @split. *)

Equations mult (n m : nat) : nat :=
mult O m := 0 ; mult (S n) m := mult n m + m.

Transparent mult.

(* Equations mult' (n m acc : nat) : nat := *)
(* mult' O m acc := acc ; mult' (S n) m acc := mult' n m (n + acc). *)

Inductive Parity : nat -> Set :=
| even : forall n, Parity (mult 2 n)
| odd : forall n, Parity (S (mult 2 n)).

(* Eval compute in (fun n => mult 2 (S n)). *)
Definition cast {A B : Type} (a : A) (p : A = B) : B.
  intros. subst. exact a.
Defined.
  
Equations(nocomp) parity (n : nat) : Parity n :=
parity O := even 0 ;
parity (S n) <= parity n => {
  parity (S ?(2 * k))     (even k) := odd k ;
  parity (S ?(2 * k + 1)) (odd k)  := cast (even (S k)) _ }.

Equations half (n : nat) : nat :=
half n <= parity n => {
  half ?(2 * k) (odd k) := k ;
  half ?(2 * k + 1) (even k) := k }.

Equations(nocomp) vtail {A n} (v : vector A (S n)) : vector A n :=
vtail A n (Vcons a n v') := v'.

Ltac generalize_by_eqs id ::= generalize_eqs id.
Ltac generalize_by_eqs_vars id ::= generalize_eqs_vars id.

Equations(nocomp) diag {A n} (v : vector (vector A n) n) : vector A n :=
diag A O Vnil := Vnil ;
diag A (S n) (Vcons (Vcons a n v) n v') := Vcons a (diag (vmap vtail v')).

Definition mat A n m := vector (vector A m) n.

Equations vmake {A} (n : nat) (a : A) : vector A n :=
vmake A O a := Vnil ;
vmake A (S n) a := Vcons a (vmake n a).

Equations(nocomp) vfold_right {A : nat -> Type} {B} (f : Π n, B -> A n -> A (S n)) (e : A 0) {n} (v : vector B n) : A n :=
vfold_right A B f e ?(0) Vnil := e ;
vfold_right A B f e ?(S n) (Vcons a n v) := f n a (vfold_right f e v).

Equations(nocomp) vzip {A B C n} (f : A -> B -> C) (v : vector A n) (w : vector B n) : vector C n :=
vzip A B C ?(O) f Vnil _ := Vnil ;
vzip A B C ?(S n) f (Vcons a n v) (Vcons a' n v') := Vcons (f a a') (vzip f v v').

Definition transpose {A m n} : mat A m n -> mat A n m :=
  vfold_right (A:=λ m, mat A n m)
  (λ m', vzip (λ a, Vcons a))
  (vmake n Vnil).

(* Lemma vfold_right_e {A : Type} {B} {n} (f : Π n', B' -> vector (vector A 0) n' -> vector (vector A 0) (S n')) *)
(*   (e : vector (vector A 0) n) v : vfold_right f (vmake n Vnil) v =  *)
(* Typeclasses eauto :=. *)

Require Import Fin.

Generalizable All Variables.

Opaque vmap. Opaque vtail. Opaque nth.

Lemma nth_vmap `(v : vector A n) `(fn : A -> B) (f : fin n) : nth (vmap fn v) f = fn (nth v f).
Proof. intros. revert B fn. funelim (nth v f). intros; simp nth vmap. Qed.

Lemma nth_vtail `(v : vector A (S n)) (f : fin n) : nth (vtail v) f = nth v (fs f).
Proof. intros until v. funelim (vtail v); intros; simp nth. Qed.

Hint Rewrite @nth_vmap @nth_vtail : nth.
  
Lemma diag_nth `(v : vector (vector A n) n) (f : fin n) : nth (diag v) f = nth (nth v f) f.
Proof. 
  intros. revert f. funelim (diag v); intros f.
    depelim f.

    depelim f; simp nth. rewrite H. simp nth.
Qed.
