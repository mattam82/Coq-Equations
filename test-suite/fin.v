Require Import Program Equations.Equations.

Set Equations WithKDec.

Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).
Derive Signature NoConfusion NoConfusionHom for fin.

Inductive ilist (A : Set) : nat -> Set :=
| Nil : ilist A 0
| Cons : forall {n}, A -> ilist A n -> ilist A (S n).
Arguments Nil [A].
Arguments Cons [A n] _ _.

Derive Signature NoConfusion for ilist.

Equations fin_to_nat {n : nat} (i : fin n) : nat :=
fin_to_nat fz := 0;
fin_to_nat (fs j) := S (fin_to_nat j).

Lemma fin_lt_n : forall (n : nat) (i : fin n), fin_to_nat i < n.
Proof.
  intros. funelim (fin_to_nat i).
    - apply Le.le_n_S; apply Le.le_0_n.
    - apply Lt.lt_n_S; assumption.
Defined.
Derive Signature for le.

Equations nat_to_fin {n : nat} (m : nat) (p : m < n) : fin n :=
nat_to_fin (n:=(S n)) 0 _ := fz;
nat_to_fin (n:=(S n)) (S m) p := fs (nat_to_fin m _).

Next Obligation. apply Lt.lt_S_n; assumption. Defined.

Set Program Mode.

Equations fin_to_nat_bound {n : nat} (i : fin n) : {m : nat | m < n} :=
fin_to_nat_bound fz := 0;
fin_to_nat_bound (fs j) := let (m, p) := fin_to_nat_bound j in (S m).
Next Obligation. apply Le.le_n_S; apply Le.le_0_n. Defined.
Next Obligation. apply Lt.lt_n_S; assumption. Defined.

Arguments exist {A} {P} _ _.

Equations nat_bound_to_fin (n : nat) (m : {m : nat | m < n}) : fin n :=
nat_bound_to_fin 0 (exist _ p) :=! p;
nat_bound_to_fin (S n') (exist 0 _) := fz;
nat_bound_to_fin (S n') (exist (S m) p) := fs (nat_bound_to_fin _ m).

Next Obligation. auto with arith || inversion p. Defined.

Lemma fin__nat : forall (n : nat) (m : nat) (p : m < n),
  fin_to_nat (nat_to_fin m p) = m.
Proof.
  intros.
  funelim (nat_to_fin m p); simp fin_to_nat.
  simpl. now rewrite H.
Qed.

Lemma nat__fin : forall (n : nat) (i : fin n),
  nat_to_fin (fin_to_nat i) (fin_lt_n n i) = i.
Proof.
  intros.
  funelim (fin_to_nat i).
  simp fin_to_nat.
  Transparent fin_to_nat. simpl.
  simp nat_to_fin. f_equal. rewrite <- H at 4. f_equal.
  apply proof_irrelevance.
Qed.

Equations iget {A : Set} {n : nat} (l : ilist A n) (i : fin n) : A :=
iget (Cons x t) fz := x;
iget (Cons _ t) (fs j) := iget t j.

Equations isnoc {A : Set} {n : nat} (l : ilist A n) (x : A) : ilist A (S n) :=
isnoc Nil x := Cons x Nil;
isnoc (Cons y t) x := Cons y (isnoc t x).

Lemma append_get : forall (A : Set) (n : nat) (l : ilist A n) (x : A),
  iget (isnoc l x) (nat_to_fin n (Lt.lt_n_Sn n)) = x.
Proof.
  induction n ; intros.
    - depelim l. simp isnoc nat_to_fin iget.
    - depelim l. simp isnoc nat_to_fin iget.
      unfold nat_to_fin_obligation_1.
      replace (Lt.lt_S_n n0 (S n0) (Lt.lt_n_Sn (S n0))) with (Lt.lt_n_Sn n0) by (apply proof_irrelevance).
      apply IHn.
Qed.

Equations convert_ilist {A : Set} {n m : nat} (p : n = m) (l : ilist A n) : ilist A m :=
convert_ilist p Nil with p => { | eq_refl := Nil };
convert_ilist p (Cons a l) with p => { | eq_refl := Cons a (convert_ilist eq_refl l) }.
Transparent convert_ilist.
Lemma convert_ilist_refl {A} (n : nat) (l : ilist A n) : convert_ilist eq_refl l = l.
Proof.
  induction l. reflexivity. simpl. now rewrite IHl.
Defined.

Lemma convert_ilist_trans : forall {A : Set} {n m o : nat} (p : n = m) (r : m = o) (l : ilist A n),
  convert_ilist r (convert_ilist p l) = convert_ilist (eq_trans p r) l.
Proof. intros. simplify_eqs. now rewrite !convert_ilist_refl. Qed.

Hint Rewrite @convert_ilist_refl @convert_ilist_trans : convert_ilist.

Equations irev_aux {A : Set} {i j : nat} (l : ilist A i) (acc : ilist A j) : ilist A (i + j) :=
irev_aux Nil acc := acc;
irev_aux (Cons x t) acc := convert_ilist _ (irev_aux t (Cons x acc)).

Definition irev {A : Set} {n : nat} (l : ilist A n) : ilist A n :=
  convert_ilist _ (irev_aux l Nil).

Ltac match_refl :=
match goal with
| [ |- context[ match ?P with _ => _ end ] ] => rewrite UIP_refl with (p := P)
end.

Example rev_ex : forall (A : Set) (x y : A), irev (Cons x (Cons y Nil)) = Cons y (Cons x Nil).
Proof.
  intros.
  unfold irev; simp irev_aux.
  compute; repeat match_refl; reflexivity.
Qed.

Equations iapp {A : Set} {n m : nat} (l1 : ilist A n) (l2 : ilist A m) : ilist A (n + m) :=
iapp Nil l := l;
iapp (Cons x t) l := Cons x (iapp t l).

Lemma iapp_cons : forall (A : Set) (i j : nat) (l1 : ilist A i) (l2 : ilist A j) (x : A),
  iapp (Cons x l1) l2 = Cons x (iapp l1 l2).
Proof. simp iapp. Qed.

Definition rev_aux_app_stmt := forall (A : Set) (i j1 j2 : nat) (l : ilist A i)
  (acc1 : ilist A j1) (acc2 : ilist A j2) H,
  convert_ilist H (irev_aux l (iapp acc1 acc2)) = iapp (irev_aux l acc1) acc2.

Lemma rev_aux_app : rev_aux_app_stmt.
Proof.
  unfold rev_aux_app_stmt.
  intros.
  (* FIXME *)
  funelim (irev_aux l acc1).
    - simp irev_aux iapp. simpl in H. depelim H; simp convert_ilist. 
    - simp irev_aux iapp. rewrite convert_ilist_trans.
      rewrite <- iapp_cons.
      set (He := eq_trans _ _). clearbody He.
      set (He' := irev_aux_obligation_1 _ _ _ _ _ _ _). clearbody He'.
      simpl in H0. simpl in H.
Admitted.


Equations irev' {A : Set} {n : nat} (l : ilist A n) : ilist A n :=
irev' Nil := Nil;
irev' (Cons x t) := isnoc (irev' t) x.

Lemma isnoc_irev A n a (l : ilist A n) : isnoc (irev l) a = irev (Cons a l).
Proof.
  unfold irev. symmetry. 
Admitted.

Lemma rev__rev' : forall (A : Set) (i : nat) (l : ilist A i), irev l = irev' l.
Proof.
  intros.
  funelim (irev' l). unfold irev. simplify_eqs. simp irev_aux.
  unfold irev.
Admitted.
  
Equations rev_range (n : nat) : ilist nat n :=
rev_range 0 := Nil;
rev_range (S n) := Cons n (rev_range n).

Equations(noind) negb (b : bool) : bool :=
negb true := false;
negb false := true.

Inductive fle : forall {n}, fin n -> fin n -> Set :=
| flez : forall {n j}, @fle (S n) fz j
| fles : forall {n i j}, fle i j -> @fle (S n) (fs i) (fs j).
Derive Signature for fle.

Equations fin0_empty (i : fin 0) : False :=
fin0_empty i :=! i.

Set Equations OCaml Splitting.
Unset Equations WithK.

Transparent NoConfusionHom_fin.

Equations fle_trans {n : nat} {i j k : fin n} (p : fle i j) (q : fle j k) : fle i k :=
fle_trans flez _ := flez;
fle_trans (fles p') (fles q') := fles (fle_trans p' q').

Hint Unfold NoConfusion.noConfusion_nat_obligation_1 : equations.

Require Import EqDec EqDecInstances DepElimDec.
Derive DependentElimination EqDec for fin.

Derive Signature for eq.

Print Assumptions fin_eqdec.

Derive NoConfusion NoConfusionHom EqDec Subterm for fle.

Print Assumptions fle_eqdec.

Equations fle_trans' {n : nat} {i j : fin n} (p : fle i j) {k} (q : fle j k) : fle i k
 by rec (Signature.signature_pack p) (@fle_subterm) :=
fle_trans' flez _ := flez;
fle_trans' (fles p') (fles q') := fles (fle_trans' p' q').
Print Assumptions fle_trans'.
Extraction fle_trans'.
