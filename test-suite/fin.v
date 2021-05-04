Require Import Program Equations.Prop.Equations.
Import Sigma_Notations.
Local Open Scope equations_scope.
Set Equations Transparent.
Set Keyed Unification.

Inductive fin : nat -> Set :=
| fz : forall {n}, fin (S n)
| fs : forall {n}, fin n -> fin (S n).
Derive Signature NoConfusion NoConfusionHom for fin.

Inductive ilist (A : Set) : nat -> Set :=
| Nil : ilist A 0
| Cons : forall {n}, A -> ilist A n -> ilist A (S n).
Arguments Nil {A}.
Arguments Cons {A n} _ _.

Derive Signature NoConfusion for ilist.

Equations fin_to_nat {n : nat} (i : fin n) : nat :=
fin_to_nat fz := 0;
fin_to_nat (fs j) := S (fin_to_nat j).

Derive Signature for le.
Scheme le_dep := Induction for le Sort Prop.

Set Equations With UIP.
Instance le_uip m n : UIP (m <= n).
Proof.
  intros x. induction x using le_dep; simplify_dep_elim; reflexivity.
Defined.
Derive Subterm for nat.

Lemma le_subterm m n : m <= n -> (m = n \/ nat_subterm m n).
Proof.
  induction 1.
  - left; reflexivity.
  - intuition subst. right; constructor. constructor.
    right. eapply Subterm.clos_trans_stepr; eauto. constructor.
Qed.

Lemma well_founded_antisym {A} {R : A -> A -> Prop}{wfR : WellFounded R} :
  forall x y : A, R x y -> R y x -> False.
Proof.
  intros x y Rxy Ryx. red in wfR.
  induction (wfR y) as [y accy IHy] in x, Rxy, Ryx.
  specialize (IHy _ Rxy). apply (IHy _ Ryx Rxy).
Qed.

Lemma le_Sn_n n : S n <= n -> False.
Proof.
  intros. apply le_subterm in H as [Heq|Hlt].
  depelim Heq.
  apply well_founded_antisym in Hlt. auto.
  repeat constructor.
Qed.

Lemma le_hprop m n : forall e e' : m <= n, e = e'.
Proof.
  induction e using le_dep. intros e'. depelim e'. constructor.
  elimtype False; now apply le_Sn_n in e'.
  intros. depelim e'.
  elimtype False; clear IHe; now apply le_Sn_n in e.
  now rewrite (IHe e').
Qed.

Lemma fin_lt_n : forall (n : nat) (i : fin n), fin_to_nat i < n.
Proof.
  intros. funelim (fin_to_nat i).
    - apply Le.le_n_S; apply Le.le_0_n.
    - apply Lt.lt_n_S; assumption.
Defined.

Equations? nat_to_fin {n : nat} (m : nat) (p : m < n) : fin n :=
nat_to_fin (n:=(S n)) 0 _ := fz;
nat_to_fin (n:=(S n)) (S m) p := fs (nat_to_fin m _).
Proof. apply Lt.lt_S_n; assumption. Defined.

Set Program Mode.

Equations? fin_to_nat_bound {n : nat} (i : fin n) : {m : nat | m < n} :=
fin_to_nat_bound fz := 0;
fin_to_nat_bound (fs j) := let (m, p) := fin_to_nat_bound j in (S m).
Proof.
  - apply Le.le_n_S; apply Le.le_0_n.
  - apply Lt.lt_n_S; assumption.
Defined.

Arguments exist {A} {P} _ _.

Equations? nat_bound_to_fin (n : nat) (m : {m : nat | m < n}) : fin n :=
nat_bound_to_fin 0 (exist _ !);
nat_bound_to_fin (S n') (exist 0 _) := fz;
nat_bound_to_fin (S n') (exist (S m) p) := fs (nat_bound_to_fin _ m).

Proof. auto with arith || inversion p. Defined.

Lemma fin__nat : forall (n : nat) (m : nat) (p : m < n),
  fin_to_nat (nat_to_fin m p) = m.
Proof.
  intros.
  funelim (nat_to_fin m p); simp fin_to_nat. reflexivity.
  simpl. now rewrite H.
Qed.

Lemma nat__fin : forall (n : nat) (i : fin n),
  nat_to_fin (fin_to_nat i) (fin_lt_n n i) = i.
Proof.
  intros.
  funelim (fin_to_nat i); simpl. reflexivity.
   f_equal. rewrite <- H at 4. f_equal.
   apply le_hprop.
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
    - depelim l. now simp isnoc nat_to_fin iget.
    - depelim l. simp isnoc nat_to_fin iget.
      unfold nat_to_fin_obligation_1.
      replace (Lt.lt_S_n n (S n) (Lt.lt_n_Sn (S n))) with (Lt.lt_n_Sn n) by (apply le_hprop).
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
Import PeanoNat.Nat.

Equations irev_aux {A : Set} {i j : nat} (l : ilist A i) (acc : ilist A j) : ilist A (i + j) :=
irev_aux Nil acc := acc;
irev_aux (Cons x t) acc with eq_sym (add_succ_comm l j), (S l + j) :=
                      { | refl_equal | ?(l + S j) := irev_aux t (Cons x acc) }.

Obligation Tactic := idtac.

Equations? irev {A : Set} {n : nat} (l : ilist A n) : ilist A n :=
  irev l := irev_aux l Nil.
(* FIXME bug with 3 refines *)
    (* { | rec with eq_sym (add_0_r n) := *)
    (*       { | Heq := _ } }. *)
apply add_0_r.
Defined.
Ltac match_refl :=
match goal with
| [ |- context[ match ?P with _ => _ end ] ] => rewrite UIP_refl with (p := P)
end.

Example rev_ex : forall (A : Set) (x y : A), irev (Cons x (Cons y Nil)) = Cons y (Cons x Nil).
Proof.
  intros.
  unfold irev. simp irev_aux.
  compute. now repeat (match_refl; compute; simp irev_aux).
Qed.

Equations iapp {A : Set} {n m : nat} (l1 : ilist A n) (l2 : ilist A m) : ilist A (n + m) :=
iapp Nil l := l;
iapp (Cons x t) l := Cons x (iapp t l).

Lemma iapp_eq {A : Set} (l1 l1' l2 l2' : Σ n, ilist A n) :
  l1 = l1' -> l2 = l2' ->
  (_, iapp l1.2 l2.2) = (_, iapp l1'.2 l2'.2).
Proof. now simplify *. Defined.

Lemma iapp_cons : forall (A : Set) (i j : nat) (l1 : ilist A i) (l2 : ilist A j) (x : A),
  iapp (Cons x l1) l2 = Cons x (iapp l1 l2).
Proof. now simp iapp. Qed.

Notation "p # t" := (eq_rect _ _ t _ p) (right associativity, at level 65) : equations_scope.

Lemma rev_aux_app_hetero : forall (A : Set) (i j1 j2 : nat) (l : ilist A i)
  (acc1 : ilist A j1) (acc2 : ilist A j2),
    (_, irev_aux l (iapp acc1 acc2)) = (_, iapp (irev_aux l acc1) acc2).
Proof.
  intros.
  funelim (irev_aux l acc1).
    - simpl. now simp irev_aux iapp.
    - simp irev_aux.
      destruct (eq_sym (add_succ_comm n (j + j2))).
      simpl. specialize (H _ acc2). rewrite H. clear H.
      refine (iapp_eq (n + S j, _)
                      (S n + j, _) (_, _) (_, _) _ _); try constructor.
      clear Heq0.
      unshelve refine (DepElim.pack_sigma_eq _ _). exact (eq_sym Heq). reflexivity.
Defined.

Equations hetero_veq {A} {n m : nat} (v : ilist A n) (w : ilist A m) : Type :=
  hetero_veq v w := Σ (e : n = m), e # v = w.
Notation "x ~=~ y" := (hetero_veq x y) (at level 90).

Notation "p # e" := (Logic.transport _ p e).

Section hetero_veq.
  Context {A : Set}.
  Context {n m : nat}.

  Lemma hetero_veq_refl (v : ilist A n) : hetero_veq v v.
  Proof. red. exists refl_equal. constructor. Defined.

  Lemma hetero_veq_sym (v : ilist A n) (w : ilist A m) : hetero_veq v w -> hetero_veq w v.
  Proof. red. intros [eq Heq]. destruct eq. destruct Heq.  exists refl_equal. constructor. Defined.

  Lemma hetero_veq_trans {k} (v : ilist A n) (w : ilist A m) (x : ilist A k) :
    hetero_veq v w -> hetero_veq w x -> hetero_veq v x.
  Proof. red. intros [eq Heq]. destruct eq. destruct Heq.
         intros [eq Heq]. destruct eq, Heq.
         exists refl_equal. constructor.
  Defined.
  Set Equations With UIP.
  Lemma iapp_hetero_cong {n' m'} (v : ilist A n) (v' : ilist A n') (w : ilist A m) (w' : ilist A m') :
    hetero_veq v v' -> hetero_veq w w' -> hetero_veq (iapp v w) (iapp v' w').
  Proof. red. intros [eq Heq].
         depelim eq. destruct Heq.
         intros [eq Heq]. depelim eq. destruct Heq.
         exists refl_equal. constructor.
  Defined.
End hetero_veq.
#[export] Hint Resolve hetero_veq_refl hetero_veq_sym hetero_veq_trans : hetero_veq.
Unset Program Mode.
Lemma hetero_veq_transport_right {A} {n m} (v : ilist A n) (w : ilist A m) (eq : m = n) :
        hetero_veq v w -> hetero_veq v (eq # w).
Proof.
  destruct eq. simpl. trivial.
Qed.

Lemma hetero_veq_transport_right' {A} {n m} (v : ilist A n) (eq : n = m) :
  hetero_veq v (eq # v).
Proof.
  destruct eq. simpl. apply hetero_veq_refl.
Qed.

Lemma hetero_veq_transport_left {A} {n m} (v : ilist A n) (w : ilist A m) (eq : n = m) :
        hetero_veq v w -> hetero_veq (eq # v) w.
Proof.
  destruct eq. simpl. trivial.
Qed.

#[export] Hint Resolve hetero_veq_transport_left hetero_veq_transport_right : hetero_veq.

Lemma rev_aux_app_hetero_eq : forall (A : Set) (i j1 j2 : nat) (l : ilist A i)
  (acc1 : ilist A j1) (acc2 : ilist A j2),
    (irev_aux l (iapp acc1 acc2)) ~=~ iapp (irev_aux l acc1) acc2.
Proof.
  intros.
  funelim (irev_aux l acc1).
    - simpl. apply hetero_veq_refl.
    - simp irev_aux.
      destruct (eq_sym (add_succ_comm n (j + j2))).
      simpl. specialize (X _ acc2). simp iapp in X. eapply hetero_veq_trans. eapply X.
      apply (iapp_hetero_cong (n:=n + S j) (n' := S n + j)); auto with hetero_veq.
      apply hetero_veq_transport_right'.
Qed.

Equations irev' {A : Set} {n : nat} (l : ilist A n) : ilist A n :=
irev' Nil := Nil;
irev' (Cons x t) := isnoc (irev' t) x.

Lemma isnoc_irev A n a (l : ilist A n) : isnoc (irev l) a = irev (Cons a l).
Proof.
(* Exercise ! *)
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

Equations fin0_empty (i : fin 0) : False := { }.

Transparent NoConfusionHom_fin.

Equations fle_trans {n : nat} {i j k : fin n} (p : fle i j) (q : fle j k) : fle i k :=
fle_trans flez _ := flez;
fle_trans (fles p') (fles q') := fles (fle_trans p' q').

#[export] Hint Unfold NoConfusion.noConfusion_nat_obligation_1 : equations.

Derive DependentElimination EqDec for fin.

Derive Signature for Logic.eq.

Print Assumptions fin_eqdec.

Derive NoConfusion NoConfusionHom EqDec Subterm for fle.

Print Assumptions fle_eqdec.

Obligation Tactic := program_simpl; try typeclasses eauto 10 with Below subterm_relation.

Equations fle_trans' {n : nat} {i j : fin n} (p : fle i j) {k} (q : fle j k) : fle i k
 by wf (Signature.signature_pack p) (@fle_subterm) :=
fle_trans' flez _ := flez;
fle_trans' (fles p') (fles q') := fles (fle_trans' p' q').

Print Assumptions fle_trans'.
(* Extraction fle_trans'. *)

Equations lookup {A n} (f : fin n) (v : ilist A n) : A :=
  lookup fz (Cons x xs) := x;
  lookup (fs f) (Cons _ xs) := lookup f xs.

Inductive vforall {A : Set}(P : A -> Type) : forall {n}, ilist A n -> Type :=
| VFNil  : vforall P Nil
| VFCons : forall {n} x (xs : ilist A n),
      P x -> vforall P xs -> vforall P (Cons x xs).
Derive Signature for vforall.

Equations vforall_lookup
            {n}
            {A : Set}
            {P : A -> Type}
            {xs : ilist A n}
            (idx : fin n) :
            vforall P xs -> P (lookup idx xs) :=
    vforall_lookup fz (VFCons _ pf _) := pf ;
    vforall_lookup (fs ix) (VFCons _ _ ps) := vforall_lookup ix ps.
