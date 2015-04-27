Lemma existT_encode {A} {P : A -> Type} {a b : A} (p : P a) (q : P b) :
  existT _ a p = existT _ b q -> 
  { e : a = b & eq_rect a P p _ e = q}.
Proof. intros. dependent rewrite H. exists eq_refl. simpl. reflexivity. Defined.

Lemma existT_decode {A} {P : A -> Type} {a b : A} (p : P a) (q : P b) : 
  { e : a = b & eq_rect a P p _ e = q} -> 
  existT _ a p = existT _ b q.
Proof. intros. destruct H. destruct x. destruct e. reflexivity. Defined.

Lemma existT_encode_decode A {P : A -> Type} (a b : A) (p : P a) (q : P b) 
  (prf : { e : a = b & eq_rect a P p _ e = q}) : existT_encode _ _ (existT_decode _ _ prf) = prf.
Proof. 
  destruct prf; cbn. destruct x, e. cbn in *. apply eq_refl.
Defined.

Notation " x .1 " := (projT1 x) (at level 3).
Notation " x .2 " := (projT2 x) (at level 3).

Lemma existT_encode' {A} {P : A -> Type} (x y : {x : A & P x}):
  x = y ->
  { e : x.1 = y.1 & eq_rect x.1 P x.2 _ e = y.2}.
Proof. intros ->. exists eq_refl. simpl. reflexivity. Defined.

Lemma existT_decode' {A} {P : A -> Type} (x y : {x : A & P x}):
  { e : x.1 = y.1 & eq_rect x.1 P x.2 _ e = y.2} -> x = y.
Proof. intros [e1 e2]. destruct x as [x px], y as [y py]; simpl in *. 
       destruct e1, e2. reflexivity. 
Defined.

Lemma existT_decode_encode' A {P : A -> Type} (x y : {x : A & P x})
  (prf : x = y) : existT_decode' _ _ (existT_encode' _ _ prf) = prf.
Proof. 
  destruct prf. destruct x. reflexivity. 
Qed.

Lemma existT_encode_decode' A {P : A -> Type} (x y : {x : A & P x})
  (prf : {e : x.1 = y.1 & eq_rect x.1 P x.2 _ e = y.2}) : 
  existT_encode' _ _ (existT_decode' _ _ prf) = prf.
Proof. 
  destruct prf as [e1 e2]. 
  destruct x as [x px], y as [y py]. 
  simpl in *. destruct e1. destruct e2. reflexivity. 
Defined.

Lemma existT_decode_encode A {P : A -> Type} (a b : A) (p : P a) (q : P b) 
  (prf : existT _ a p = existT _ b q) : existT_decode _ _ (existT_encode _ _ prf) = prf.
Proof. apply existT_decode_encode'. Defined.
