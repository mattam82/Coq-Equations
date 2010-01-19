Require Import Equations List Bvector Relations.

(** Case analysis *)

Equations neg (b : bool) : bool :=
neg true := false ;
neg false := true.

Lemma neg_inv : forall b, neg (neg b) = b.
Proof. intros b. funelim (neg b). 
  simp neg. simp neg. 
Defined.



































(** Polymorphism, recursion *)

Equations app {A} (l l' : list A) : list A :=
app A nil l' := l' ;
app A (cons a l) l' := cons a (app l l').

Lemma app_assoc {A} (l l' l'' : list A) :
  app (app l l') l'' = app l (app l' l'').
Proof. intros. funelim (app l l'). 
  simp app. simp app. now rewrite H. 
Qed.







































(** [with] construct *)

Equations filter {A} (l : list A) (p : A -> bool) : list A :=
filter A nil p := nil ;
filter A (cons a l) p with p a := {
  filter A (cons a l) p true := a :: filter l p ;
  filter A (cons a l) p false := filter l p }.

Inductive incl {A} : relation (list A) :=
  stop : incl nil nil 
| keep {x : A} {xs ys : list A} : 
  incl xs ys -> incl (x :: xs) (x :: ys)
| skip {x : A} {xs ys : list A} : 
  incl xs ys -> incl (xs) (x :: ys).

Global Transparent filter.

Equations(nocomp noeqns noind) sublist {A} (p : A -> bool) 
  (xs : list A) : incl (filter xs p) xs :=
sublist A p nil := stop ;
sublist A p (cons x xs) <= p x => {
  | true := keep (sublist p xs) ;
  | false := skip (sublist p xs) }.


























(** Matching on equalities and inaccesible patterns. *)

Equations equal (n m : nat) : { n = m } + { n <> m } :=
equal O O := left eq_refl ;
equal (S n) (S m) with equal n m := {
  equal (S n) (S ?(n)) (left eq_refl) := left eq_refl ;
  equal (S n) (S m) (right p) := right _ } ;
equal x y := right _.



























(** Empty types *)

Equations head A (l : list A) (pf : l <> nil) : A :=
head A nil pf :=! pf;
head A (cons a v) _ := a.


























(** Inversion on dependent types. *)

Equations vmap {A B} (f : A -> B) {n} (v : vector A n) :
  vector B n :=
vmap A B f ?(0) Vnil := Vnil ;
vmap A B f ?(S n) (Vcons a n v) := Vcons (f a) (vmap f v).

Equations(nocomp) vtail {A n} (v : vector A (S n)) 
  : vector A n :=
vtail A n (Vcons a n v') := v'.

Equations(nocomp) diag {A n} (v : vector (vector A n) n) 
  : vector A n :=
diag A O Vnil := Vnil ;
diag A (S n) (Vcons (Vcons a n v) n v') := 
  Vcons a (diag (vmap vtail v')).

Equations K {A} (x : A) (P : x = x -> Type) (p : P eq_refl) 
  (H : x = x) : P H :=
K A x P p eq_refl := p.





