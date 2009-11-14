Require Import Program Equations Bvector List.
Require Import Relations.
Equations vlast' {A} {n} (v : vector A (S n)) : A :=
vlast' A ?(0) (Vcons a O Vnil) := a ;
vlast' A ?(S n) (Vcons a (S n) v) := vlast' v.

Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl) (H : x = x) : P H :=
K A x P p eq_refl := p.

Equations eq_sym {A} (x y : A) (H : x = y) : y = x :=
eq_sym A x x eq_refl := eq_refl.

Equations eq_trans {A} (x y z : A) (p : x = y) (q : y = z) : x = z :=
eq_trans A x x x eq_refl eq_refl := eq_refl.

Equations (nocomp) vapp' {A} {n m} (v : vector A n) (w : vector A m) : vector A (n + m) :=
vapp' A ?(0) m Vnil w := w ;
vapp' A ?(S n) m (Vcons a n v) w := Vcons a (vapp' v w).

Inductive Split {X : Type}{m n : nat} : vector X (m + n) -> Type :=
  append : Π (xs : vector X m)(ys : vector X n), Split (vapp' xs ys).

Implicit Arguments Split [[X]].

Equations(nocomp) filter {A} (l : list A) (p : A -> bool) : list A :=
filter A nil p := nil ;
filter A (cons a l) p <= p a => {
  filter A (cons a l) p true := a :: filter l p ;
  filter A (cons a l) p false := filter l p }.

Inductive incl {A} : relation (list A) :=
  stop : incl nil nil 
| keep {x : A} {xs ys : list A} : incl xs ys -> incl (x :: xs) (x :: ys)
| skip {x : A} {xs ys : list A} : incl xs ys -> incl (xs) (x :: ys).

Global Transparent filter.

Equations(nocomp) sublist {A} (p : A -> bool) (xs : list A) : incl (filter xs p) xs :=
sublist A p nil := stop ;
sublist A p (cons x xs) <= p x => {
  sublist A p (cons x xs) true := keep (sublist p xs) ;
  sublist A p (cons x xs) false := skip (sublist p xs) }.

Equations (nostruct) testn (n : nat) : nat :=
testn n ! n ;
testn O := 0 ;
testn (S n) <= testn n => {
  testn (S n) O := S O ;
  testn (S n) (S n') := S n' }.

Equations (nostruct) unzip {A B} {n} (v : vector (A * B) n) : vector A n * vector B n :=
unzip A B n v ! v ;
unzip A B ?(O) Vnil := (Vnil, Vnil) ;
unzip A B ?(S n) (Vcons (pair x y) n v) <= unzip v => {
  unzip A B ?(S n) (Vcons (pair x y) n v) (pair xs ys) := (Vcons x xs, Vcons y ys) }.

Equations (nostruct) nos_with (n : nat) : nat :=
nos_with n ! n ;
nos_with O := O ;
nos_with (S m) <= nos_with m => {
  nos_with (S m) O := S O ;
  nos_with (S m) (S n') := O }.

Scheme nos_with_unfold_mut := Minimality for nos_with_ind Sort Prop
  with nos_with_unfold_h_mut := Minimality for nos_with_ind_1 Sort Prop.

Equations (nostruct) split {X : Type} {m n} (xs : vector X (m + n)) : Split m n xs :=
split X m n xs ! m ;
split X O    n xs := append Vnil xs ;
split X (S m) n (Vcons x ?(S m + n) xs) <= split xs => {
  split X (S m) n (Vcons x ?(S m + n) xs) (append xs' ys') :=
    append (Vcons x xs') ys' }.

Equations(nocomp) equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := in_left ;
equal (S n) (S m) <= equal n m => {
  equal (S n) (S n) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := in_right } ;
equal x y := in_right.

Equations app_with {A} (l l' : list A) : list A :=
app_with A nil l := l ;
app_with A (cons a v) l <= app_with v l => {
  app_with A (cons a v) l vl := cons a vl }.

(* About app_with_elim. *)

(* Print app_with_ind. *)
(* Print app_with_ind_ind. *)

(* Scheme app_with_elim := Minimality for app_with_ind Sort Prop *)
(*   with app_with_help_elim := Minimality for app_with_ind_1 Sort Prop. *)

(* About app_with_elim. *)




Equations plus' (n m : nat) : nat :=
plus' O n := n ; 
plus' (S n) m := S (plus' n m).

Equations unzip_n {A B} {n} (v : vector (A * B) n) : vector A n * vector B n :=
unzip_n A B O Vnil := (Vnil, Vnil) ;
unzip_n A B (S n) (Vcons (pair x y) n v) :=
  let vs := unzip_n v in
  let '(xs, ys) := vs in
    (Vcons x xs, Vcons y ys).

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.

Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b.
  elim (neg_ind_fun b) ; auto.
Qed.

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

Equations rev {A} (l : list A) : list A :=
rev A nil := nil;
rev A (cons a v) := rev v +++ [a].

Ltac funelim c :=
  match c with
    appcontext C [ ?f ] => 
      let x := constr:(fun_elim (f:=f)) in
        (let prf := eval simpl in x in
          dependent_pattern c ; apply prf ; clear ; intros)
  end.

Lemma app'_nil : forall {A} (l : list A), l +++ [] = l.
Proof. intros.
  funind (app' l []) applnil.
  rewrite IHapp'_ind. reflexivity.
Qed.

Lemma app'_assoc : forall {A} (l l' l'' : list A), (l +++ l') +++ l'' = app' l (app' l' l'').
Proof. intros. Opaque app'. revert l''. 
  dependent_pattern (l +++ l').
  pose (fun_elim (f:=@app')). simpl in f. apply f; clear ; intros.
  simp app'. simp app'. rewrite H. reflexivity.
Qed.

Lemma app'_funind : forall {A} (l l' l'' : list A), (l +++ l') +++ l'' = app' l (app' l' l'').
Proof. intros. Opaque app'. funind (l +++ l') ll'. 
  rewrite IHapp'_ind. reflexivity. 
Qed.

Hint Rewrite @app'_nil @app'_assoc : app'.

Lemma rev_app' : forall {A} (l l' : list A), rev (l +++ l') = rev l' +++ rev l.
Proof. intros. funind (l +++ l') l'l.
  simp rev. rewrite IHapp'_ind. rewrite <- app'_assoc. reflexivity. 
Qed.

(* Eval compute in @app'. *)

Lemma split_vapp' : Π (X : Type) m n (v : vector X m) (w : vector X n), 
  let 'append v' w' := split (vapp' v w) in
    v = v' /\ w = w'.
Proof.
  intros. funind (vapp' v w) vw; simp split. intuition.
  destruct (split (vapp' v w)).
  simp split.
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
split_struct X (S m) n (Vcons x ?(S m + n) xs) <= split_struct xs => {
  split_struct X (S m) n (Vcons x ?(S m + n) xs) (append xs' ys') := append (Vcons x xs') ys' }.

Lemma split_struct_vapp : Π (X : Set) m n (v : vector X m) (w : vector X n),
  let 'append v' w' := split_struct (vapp' v w) in
    v = v' /\ w = w'.
Proof.
  intros. funind (vapp' v w) vw; simp split_struct. intuition.
  destruct (split_struct (vapp' v w)).
  simp split_struct.
  intuition congruence.
Qed.

Equations vhead {A n} (v : vector A (S n)) : A := 
vhead A ?(n) (Vcons a n v) := a.

Equations (nocomp) vmap {A B} (f : A -> B) {n} (v : vector A n) : vector B n :=
vmap A B f O Vnil := Vnil ;
vmap A B f (S n) (Vcons a ?(n) v) := Vcons (f a) (vmap f v).

Transparent vmap.
(* Set Printing All.  *)
(* Eval compute in @vmap. *)

Equations vmap' {A B} (f : A -> B) {n} (v : vector A n) : (vector B n) :=
vmap' A B f ?(O) Vnil := Vnil ;
vmap' A B f ?(S n) (Vcons a ?(n) v) := Vcons (f a) (vmap' f v).

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

Equations(nocomp) vlast {A} {n} (v : vector A (S n)) : A :=
vlast A O (Vcons a ?(O) Vnil) := a ;
vlast A (S n) (Vcons a ?(S n) v) := vlast v.

Equations vlast' {A} {n} (v : vector A (S n)) : A :=
vlast' A ?(0) (Vcons a O Vnil) := a ;
vlast' A ?(S n) (Vcons a (S n) v) := vlast' v.

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

Print mult. Transparent mult. Eval compute in mult.

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

Equations diag {A n} (v : vector (vector A n) n) : vector A n :=
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

Ltac funind_call f H :=
  on_call f ltac:(fun call => funind call H).
