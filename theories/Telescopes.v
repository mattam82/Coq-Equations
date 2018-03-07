Require Import HoTT.Basics.Overture.

Lemma existT_encode {A} {P : A -> Type} {a b : A} (p : P a) (q : P b) :
  existT _ a p = existT _ b q -> 
  { e : a = b & paths_ind a (fun a _ => P a) p _ e = q}.
Proof. intro H.
refine (
  paths_ind
    (a; p)
    (fun s _ =>
      {e : a = proj1_sig s
      & paths_ind a (
          fun (a' : A) (_ : a = a') => P a') p (proj1_sig s) e = proj2_sig s})
    {| proj1_sig := idpath; proj2_sig := idpath |}
    (b; q)
    H).
Defined.

Lemma existT_decode {A} {P : A -> Type} {a b : A} (p : P a) (q : P b) : 
  { e : a = b & paths_ind a (fun x _ => P x) p _ e = q} ->
  existT _ a p = existT _ b q.
Proof. intros. destruct X. destruct proj1_sig. destruct proj2_sig. reflexivity. Defined.

Lemma existT_encode_decode A {P : A -> Type} (a b : A) (p : P a) (q : P b) 
  (prf : { e : a = b & paths_ind a (fun x _ => P x) p _ e = q}) : existT_encode _ _ (existT_decode _ _ prf) = prf.
Proof. 
  destruct prf; cbn. destruct proj1_sig, proj2_sig. cbn in *. constructor.
Defined.

Notation " x .1 " := (projT1 x) (at level 3).
Notation " x .2 " := (projT2 x) (at level 3).

Lemma existT_encode' {A} {P : A -> Type} (x y : {x : A & P x}):
  x = y ->
  { e : x.1 = y.1 & paths_ind x.1 (fun a _ => P a) x.2 _ e = y.2}.
Proof. intros ->. exists idpath. simpl. reflexivity. Defined.

Lemma existT_decode' {A} {P : A -> Type} (x y : {x : A & P x}):
  { e : x.1 = y.1 & paths_ind x.1 (fun a _ => P a) x.2 _ e = y.2} -> x = y.
Proof. intros [e1 e2]. destruct x as [x px], y as [y py]; simpl in *. 
       destruct e1, e2. reflexivity. 
Defined.

Lemma existT_decode_encode' A {P : A -> Type} (x y : {x : A & P x})
  (prf : x = y) : existT_decode' _ _ (existT_encode' _ _ prf) = prf.
Proof. 
  destruct prf. destruct x. reflexivity. 
Qed.

Lemma existT_encode_decode' A {P : A -> Type} (x y : {x : A & P x})
  (prf : {e : x.1 = y.1 & paths_ind x.1 (fun a _ => P a) x.2 _ e = y.2}) :
  existT_encode' _ _ (existT_decode' _ _ prf) = prf.
Proof. 
  destruct prf as [e1 e2]. 
  destruct x as [x px], y as [y py]. 
  simpl in *. destruct e1. destruct e2. reflexivity. 
Defined.

Lemma existT_decode_encode A {P : A -> Type} (a b : A) (p : P a) (q : P b) 
  (prf : existT _ a p = existT _ b q) : existT_decode _ _ (existT_encode _ _ prf) = prf.
Proof.
refine (
  paths_ind
    (a; p)
    (fun s prf' =>
      existT_decode p s.(proj2_sig) (existT_encode p s.(proj2_sig) prf') = prf')
    idpath
    (b; q)
    prf).
Defined.
