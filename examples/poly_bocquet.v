(** Polynoms and a reflexive tactic for solving boolean goals (using heyting algebra).
   Original version by Rafael Bocquet, 2016. Updated to use Equations for all definitions by M. Sozeau, 2016

 *)
Require Import Equations.Equations.
Require Import ZArith.
Require Import Program.
Require Import Psatz.
Require Import NPeano.
Require Import Nat.
From Equations Require Import DepElimDec.

Derive Signature for vector. 
Derive Signature for @eq.

Module M1.
  Require Import Coq.Vectors.VectorDef.

  (** Je ne sais pas pourquoi je n'ai pas utilisé [z <> 0] ici *)
  
  Inductive IsNZ : Z -> Prop :=
  | IsPos : forall z, IsNZ (Zpos z)
  | IsNeg : forall z, IsNZ (Zneg z).
  Derive Signature for IsNZ.

  (**
   * Le type des polynômes.
   Les indices permettent d'assurer qu'un polynôme à une représentation unique.
   Le premier indice est true si le polynôme est nul.
   Le deuxième donne le nombre de variables disponible.
   [poly_s P Q : poly _ n] représente [P + n * Q].
   *)
  Inductive poly : bool -> nat -> Type :=
  | poly_z : poly true O
  | poly_c : forall z, IsNZ z -> poly false O
  | poly_l : forall {n b}, poly b n -> poly b (S n)
  | poly_s : forall {n b}, poly b n -> poly false (S n) -> poly false (S n).
  Derive Signature for poly.
  Derive NoConfusion for poly.
  (**
   * Le type des monômes.
   ** 1.2.a
   L'indice donne le nombre de variables disponibles.
   *)
  Inductive mono : nat -> Type :=
  | mono_z : mono O
  | mono_l : forall {n}, mono n -> mono (S n)
  | mono_s : forall {n}, mono (S n) -> mono (S n).
  Derive Signature for mono.
  Derive NoConfusion for mono.

  Equations(nocomp noind) get_coef {n} (m : mono n) {b} (p : poly b n) : Z :=
  get_coef mono_z     poly_z       := 0%Z;
  get_coef mono_z     (poly_c z _) := z;
  get_coef (mono_l m) (poly_l p)   := get_coef m p;
  get_coef (mono_l m) (poly_s p _) := get_coef m p;
  get_coef (mono_s m) (poly_l _)   := 0%Z;
  get_coef (mono_s m) (poly_s p1 p2) := get_coef m p2.

  (** Un polynôme non nul a un coefficient non nul *)
  Lemma poly_nz : forall {n} (p : poly false n), exists m, IsNZ (get_coef m p).
  Proof with (autorewrite with get_coef; auto).
    intros. depind p; unfold poly_sig in *; simplify_IH_hyps.
    exists mono_z...
    destruct IHp. exists (mono_l x)...
    specialize (IHp2 _ _ eq_refl).
    destruct IHp2. exists (mono_s x)...
  Qed.

  (**
   ** 1.2.b
   Deux polynômes avec les mêmes coefficients sont égaux
   *)
  Theorem get_coef_eq : forall {n} (b1 : bool) (p1 : poly b1 n) (b2 : bool) (p2 : poly b2 n),
                           (forall (m : mono n), get_coef m p1 = get_coef m p2) ->
                           existT (fun b => poly b n) b1 p1 = existT _ b2 p2.
  Proof with (autorewrite with get_coef in *; auto).
    depind p1; depelim p2; intros; try rename n0 into n; auto;
    try (specialize (H mono_z); autorewrite with get_coef in H; destruct i; discriminate; fail).
    specialize (H mono_z); autorewrite with get_coef in H; depelim i; depelim i0; inversion H; auto.

    specialize (IHp1 _ p2).
    assert (existT (λ b : bool, poly b n) b p1 =
            existT (λ b : bool, poly b n) b0 p2).
    apply IHp1. intro. specialize (H (mono_l m)). autorewrite with get_coef in H. auto.
    inversion H0. auto.

    destruct (poly_nz p2_2).
    specialize (H (mono_s x))... destruct H0; discriminate.

    destruct (poly_nz p1_2).
    specialize (H (mono_s x))... destruct H0; discriminate.

    assert(existT (λ b : bool, poly b (S n)) false p1_2 =
           existT (λ b : bool, poly b (S n)) false p2_2).
    apply IHp1_2; auto. intro. specialize (H (mono_s m))...
    depelim H0.
    assert(existT (λ b : bool, poly b n) b p1_1 =
           existT (λ b : bool, poly b n) b0 p2_1).
    apply IHp1_1; auto. intro. specialize (H (mono_l m))...
    depelim H0. auto.
  Qed.

  (**
   Une valuation des variables est donnée par le type Vector.t Z n
   ** 1.2.c
   *)
  Equations(nocomp) eval {n} {b} (p : poly b n) (v : Vector.t Z n) : Z :=
  eval poly_z         Vector.nil           := 0%Z;
  eval (poly_c z _)   Vector.nil           := z;
  eval (poly_l p)     (Vector.cons x xs)   := eval p xs;
  eval (poly_s p1 p2) (Vector.cons y _ ys) := (eval p1 ys + y * eval p2 (Vector.cons y ys))%Z.
  Next Obligation.
    depind p; depelim v; simp eval. (* FIXME *)
  Defined.
    (**
   On veut montrer qu'un polynôme non nul peut s'évaluer vers un entier non nul.
   Le lemme principal est [poly_nz_eval].
   Il procède par induction sur le [n] le nombre de variables et montre d'abord le résultat cherché puis un résultat plus fort via [poly_nz_eval'] pour que l'induction fonctionne.
   Les inégalités entières sont vérifiées par [nia].
   *)
  Lemma poly_nz_eval' : forall {n},
                          (forall (p : poly false n), exists v, eval p v <> 0%Z) ->
                          (forall (p : poly false (S n)),
                           exists v, forall m, exists x,
                                       x <> 0%Z /\
                                       (Z.abs (x * eval p (Vector.cons x v)) > Z.abs m)%Z).
  Proof with (autorewrite with eval).
    depind p.
    - destruct (H p) as [v Hv].
      exists v; intros; exists (1 + Z.abs m)%Z... nia.
    - destruct (IHp2 p2 eq_refl) as [v Hv]; exists v; intros.
      destruct (Hv (Z.abs (eval p1 v) + Z.abs m)%Z) as [x [Hx0 Hx1]]; exists x...
      split; auto.
      nia.
  Qed.

  Lemma poly_nz_eval : forall {n},
                         (forall (p : poly false n), exists v, eval p v <> 0%Z)
                         /\ (forall (p : poly false (S n)),
                             exists v, forall m, exists x,
                                         x <> 0%Z /\
                                         (Z.abs (x * eval p (Vector.cons x v)) > Z.abs m)%Z).
  Proof with (autorewrite with eval; auto using poly_nz_eval').
    depind n; match goal with
                | [ |- ?P /\ ?Q ] => assert (HP : P); [|split;[auto|]]
              end...
    - depelim p; exists Vector.nil... depelim i; auto; discriminate.
    - destruct IHn as [IHn1 IHn2]; depelim p.
      + destruct (IHn1 p) as [v Hv]; exists (Vector.cons 0%Z v)...
      + destruct (IHn2 p2) as [v Hv].
        destruct (Hv (eval p1 v)) as [x [_ Hx]].
        exists (Vector.cons x v)...
        nia.
  Qed.

  (**
   Un polynôme nul ne peut s'évaluer que vers 0.
   *)
  Lemma poly_z_eval : forall {n} (p : poly true n) {v}, eval p v = 0%Z.
  Proof.
    intros n p v. funelim (eval p v); auto.
    (* Was: 
    depind p; depelim v.
    autorewrite with eval; auto.
    specialize (IHp _ _ eq_refl).
    depelim v; autorewrite with eval; auto. *)
  Qed.

  Definition apoly {n} := sigmaI (fun b => poly b n).

  (** Définition de [plus] (extraite d'une définition via Equations) *)
  (** ** 1.3.a *)

  Equations(noind nocomp) plus {n} {b1} (p1 : poly b1 n) {b2} (p2 : poly b2 n) : { b : bool & poly b n } :=
    plus poly_z        poly_z          := apoly _ poly_z;
    plus poly_z        (poly_c y ny)   := apoly _ (poly_c y ny);
    plus (poly_c x nx) poly_z          := apoly _ (poly_c x nx);
    plus (poly_c x nx) (poly_c y ny)   := let z := (x + y)%Z in
                                          match z with
                                            | Z0 => apoly _ poly_z
                                            | Zpos z' => apoly _ (poly_c (Zpos z') (IsPos z'))
                                            | Zneg z' => apoly _ (poly_c (Zneg z') (IsNeg z'))
                                          end;                                            
    plus (poly_l p1)    (poly_l p2)    := apoly _ (poly_l (pr2 (plus p1 p2)));
    plus (poly_l p1)    (poly_s p2 q2) := apoly _ (poly_s (pr2 (plus p1 p2)) q2);
    plus (poly_s p1 q1) (poly_l p2)    := apoly _ (poly_s (pr2 (plus p1 p2)) q1);

    plus (poly_s p1 q1) (poly_s p2 q2) := match plus q1 q2 with
                                            | (false; q3) => apoly _ (poly_s (pr2 (plus p1 p2)) q3)
                                            | (true; _)   => apoly _ (poly_l (pr2 (plus p1 p2)))
                                          end.

  (** [plus] se comporte comme il faut par rapport à [eval] *)
  Lemma plus_eval : forall {n} {b1} (p1 : poly b1 n) {b2} (p2 : poly b2 n) v,
                      (eval p1 v + eval p2 v)%Z = eval (pr2 (plus p1 p2)) v.
  Proof with (autorewrite with plus eval; auto with zarith).
    Ltac X := (autorewrite with plus eval; auto with zarith).
    depind p1; depelim p2; intros; depelim v; X; simpl; X.
    - destruct (z + z0)%Z; simpl...
    - simpl... rewrite <- IHp1...
    - simpl... rewrite <- IHp1_1...
    - specialize (IHp1_2 _ p2_2 (Vector.cons h v)).
      remember (plus p1_2 p2_2) as p.
      destruct p as [p1 p2]; depelim p1.
      + simpl... rewrite <- IHp1_1...
        rewrite poly_z_eval in IHp1_2; nia.
      + simpl... rewrite <- IHp1_1... rewrite <- IHp1_2...
        nia.
  Qed.

  Hint Rewrite <- @plus_eval : eval.

  (**
   La négation d'un polynôme (utilisée pour définir la soustraction)
   *)
  Equations(nocomp) poly_neg {n} {b} (p : poly b n) : poly b n :=
    poly_neg poly_z := poly_z;
    poly_neg (poly_c (Z.pos a) _) := poly_c (Z.neg a) (IsNeg a);
    poly_neg (poly_c (Z.neg a) _) := poly_c (Z.pos a) (IsPos a);
    poly_neg (poly_l p) := poly_l (poly_neg p);
    poly_neg (poly_s p q) := poly_s (poly_neg p) (poly_neg q).

  Lemma neg_eval : forall {n} {b1} (p1 : poly b1 n) v,
                     (- eval p1 v)%Z = eval (poly_neg p1) v.
  Proof.
    Ltac XX := (autorewrite with poly_neg plus eval; auto with zarith).
    depind p1; depelim v; XX.
    depelim i; XX.
    rewrite <- IHp1_1; rewrite <- IHp1_2; nia.
  Qed.
  Hint Rewrite <- @neg_eval : eval.

  (**
   Si la différence de deux polynômes est nulle, ces deux polynômes sont égaux.
   *)
  Lemma poly_diff_z_eq : forall {n} {b1} (p1 : poly b1 n) {b2} (p2 : poly b2 n),
                           pr1 (plus p1 (poly_neg p2)) = true ->
                           existT (fun b => poly b n) _ p1 = existT _ _ p2.
  Proof.
    intros.
    depind p1; depelim p2; auto;
    try (autorewrite with poly_neg plus in H; discriminate; fail).
    - destruct i; autorewrite with poly_neg plus in *; discriminate.
    - f_equal; depelim i; depelim i0; autorewrite with poly_neg plus in H.
      assert (z = z0).
      remember (Z.pos z + Z.neg z0)%Z as z1; destruct z1; try discriminate; simpl in H; nia.
      subst; auto.
      remember (Z.pos z + Z.pos z0)%Z as z1; destruct z1; try discriminate.
      remember (Z.neg z + Z.neg z0)%Z as z1; destruct z1; try discriminate.
      assert (z = z0).
      remember (Z.neg z + Z.pos z0)%Z as z1; destruct z1; try discriminate; simpl in H; nia.
      subst; auto.
    - autorewrite with poly_neg plus in H.
      specialize (IHp1 _ p2 H).
      depelim IHp1. auto.
    - autorewrite with poly_neg plus in H.
      specialize (IHp1_1 _ p2_1); specialize (IHp1_2 _ p2_2).
      remember (plus p1_2 (poly_neg p2_2)) as P; remember (plus p1_1 (poly_neg p2_1)) as Q.
      destruct P as [bP P]; destruct Q as [bQ Q].
      destruct bP; destruct bQ; simpl in H; try discriminate.
      specialize (IHp1_1 eq_refl); specialize (IHp1_2 eq_refl).
      depelim IHp1_1; (*MS: fixme, depends on depelimdec *) try depelim IHp1_2; auto.
  Qed.

  (**
   * Deux polynômes avec les mêmes valeurs sont égaux.
   ** 1.2.d
   On montre que la différence de deux polynôme avec les mêmes valeurs est nulle par l'absurde via [poly_nz_eval], puis on applique le lemme [poly_diff_z_eq]
   *)
  Theorem poly_eval_eq : forall {n} {b1} (p1 : poly b1 n) {b2} (p2 : poly b2 n),
                           (forall v, eval p1 v = eval p2 v) ->
                           existT (fun b => poly b n) _ p1 = existT _ _ p2.
  Proof.
    intros.
    remember (plus p1 (poly_neg p2)) as P; destruct P as [b P]; destruct b.
    - apply poly_diff_z_eq; inversion HeqP; auto.
    - exfalso.
      destruct (@poly_nz_eval n) as [H0 _]; destruct (H0 P) as [v H1].
      assert (eval P v = eval (pr2 (plus p1 (poly_neg p2))) v); [inversion HeqP; auto|].
      rewrite H2 in H1; autorewrite with eval in H1; rewrite (H v) in H1. nia.
  Qed.

  (**
   * Multiplication
   ** 1.3.b
   La définition de la multiplication est un peu plus laborieuse que celle de l'addition car on a des cas inductifs sur le deuxième argument.
   *)

  (**
   [poly_l_or_s] permet de construire p + X * q lorsque q peut être nul.
   *)
  Definition poly_l_or_s {n} {b1} (p1 : poly b1 n) {b2} :
    poly b2 (S n) -> {b : bool & poly b (S n) } :=
    match b2 with
      | false => fun p2 => apoly _ (poly_s p1 p2)
      | true  => fun p2 => apoly _ (poly_l p1)
    end.

  Lemma poly_l_or_s_eval : forall {n} {b1} (p1 : poly b1 n) {b2} (p2 : poly b2 (S n)) h v,
                             eval (pr2 (poly_l_or_s p1 p2)) (Vector.cons h v) =
                             (eval p1 v + h * eval p2 (Vector.cons h v))%Z.
  Proof.
    unfold poly_l_or_s.
    depelim b2; intros; autorewrite with eval.
    rewrite poly_z_eval; nia.
    reflexivity.
  Qed.
  Hint Rewrite @poly_l_or_s_eval : eval.

  (* [mult (poly_l p) q = mult_l q (mult p)] *)
  (* MS: FIXME: noind necessary *)
  Equations(nocomp noind) mult_l {n} {b2} (p2 : poly b2 (S n)) (m : forall {b2} (p2 : poly b2 n), { b : bool & poly b n }) :
    { b : bool & poly b (S n) } :=
  mult_l (poly_l p2) m := apoly _ (poly_l (pr2 (m _ p2)));
  mult_l (poly_s p1 p2) m := poly_l_or_s (pr2 (m _ p1)) (pr2 (mult_l p2 m)).

  (* [mult (poly_s p1 p2) q = mult_s q (mult p1) (mult p2)] *)
  Equations(nocomp noind) mult_s {n} {b2} (p2 : poly b2 (S n))
     (m1 : forall {b2} (p2 : poly b2 n), { b : bool & poly b n })
     (m2 : forall {b2} (p2 : poly b2 (S n)), { b : bool & poly b (S n) }) :
    { b : bool & poly b (S n) } :=
  mult_s (poly_l p1) m1 m2 := poly_l_or_s (pr2 (m1 _ p1)) (pr2 (m2 _ (poly_l p1)));
  mult_s (poly_s p2 q2) m1 m2 :=
  poly_l_or_s (pr2 (m1 _ p2))
              (pr2 (plus (pr2 (m2 _ (poly_l p2))) (pr2 (mult_s q2 m1 m2)))).
  
  (* Définition de la multiplication *)

  Equations(noind nocomp) mult n b1 (p1 : poly b1 n) b2 (p2 : poly b2 n) : { b : bool & poly b n } :=
    mult n b1 poly_z        b2 _ := apoly _ poly_z;
    mult n b1 (poly_c x nx) b2 poly_z := apoly _ poly_z;
    mult n b1 (poly_c x nx) b2 (poly_c y ny) :=
    match (x * y)%Z with
      | Z0 => apoly _ poly_z
      | Zpos z' => apoly _ (poly_c (Zpos z') (IsPos z'))
      | Zneg z' => apoly _ (poly_c (Zneg z') (IsNeg z'))
    end;
    mult n b1 (poly_l p1)    b2 q := mult_l q (mult _ _ p1);
    mult n b1 (poly_s p1 q1) b2 q := mult_s q (mult _ _ p1) (mult _ _ q1).
  Arguments mult {n} {b1} p1 {b2} p2.

  (**
   La preuve que la multiplication commute à l'évaluation se fait par récurrence.
   Les lemmes déjà prouvés sur l'évaluation permettent d'arriver à des équations dans Z que [nia] est capable de traiter.
   *)
  Lemma mult_eval : forall {n} {b1} (p1 : poly b1 n) {b2} (p2 : poly b2 n) v,
                      (eval p1 v * eval p2 v)%Z = eval (pr2 (mult p1 p2)) v.
  Proof with (autorewrite with mult mult_l mult_s eval; auto with zarith).
    Ltac Y := (autorewrite with mult mult_l mult_s eval; auto with zarith).
    depind p1; try (depind p2; intros; depelim v; Y; simpl; Y; fail).
    depind p2; intros; depelim v; Y; simpl; Y; destruct (z * z0)%Z; simpl...
    - assert (mult_l_eval : forall {b2} (q : poly b2 (S n)) v h,
                              match mult_l q (@mult _ _ p1) with
                                | (mb; mp) => eval mp (Vector.cons h v) =
                                             (eval q (Vector.cons h v) * eval p1 v)%Z
                              end).
      + depind q; intros; Y;
        rewrite <- IHp1...
        rewrite IHq2; auto; nia.
      + intros; depelim v; Y; simpl; Y; rewrite mult_l_eval...
    - assert (mult_s_eval :
                forall {b2} (q : poly b2 (S n)) v h,
                  match mult_s q (@mult _ _ p1_1) (@mult _ _ p1_2) with
                    | (mb; mp) =>
                      eval mp (Vector.cons h v) =
                      (eval q (Vector.cons h v) * (eval p1_1 v + h * eval p1_2 (Vector.cons h v)))%Z
                  end).
      + depind q; intros; Y; simpl; Y.
        rewrite <- IHp1_1, <- IHp1_2; Y; nia.
        rewrite <- IHp1_1. rewrite IHq2, <- IHp1_2; auto; Y; nia.
      + intros; depelim v; Y; simpl; Y; rewrite mult_s_eval...
  Qed.
  Hint Rewrite <- @mult_eval : eval.

  (** ** 2.1.a
   formules avec variables de type [A]
   *)
  Inductive formula {A} :=
  | f_var : A -> formula
  | f_const : bool -> formula
  | f_and : formula -> formula -> formula
  | f_or : formula -> formula -> formula
  | f_not : formula -> formula
  .

  (** ** 2.1.b
   Évaluation des formules étant donné une valuation [v : A -> bool]
   *)
  Equations(nocomp) eval_formula {A} (v : A -> bool) (f : @formula A) : bool :=
  eval_formula f (f_var v)   := f v;
  eval_formula f (f_const b) := b;
  eval_formula f (f_and a b) := andb (eval_formula f a) (eval_formula f b);
  eval_formula f (f_or a b)  := orb (eval_formula f a) (eval_formula f b);
  eval_formula f (f_not v)   := negb (eval_formula f v).

  (**
   [close_formula] permet d'obtenir une formule avec un nombre connu de variables étant donné une formule avec des variables dans [nat].
   *)
  Definition close_formula : @formula nat -> { n : nat & forall m, m >= n -> @formula (Fin.t m) }.
  Proof.
    intro f; depind f.
    - apply (sigmaI _ (S a)); intros m p; apply f_var.
      apply @Fin.of_nat_lt with (p := a). omega.
    - exact (sigmaI _ O (fun _ _ => f_const b)).
    - destruct IHf1 as [n1 e1]; destruct IHf2 as [n2 e2].
      apply (sigmaI _ (max n1 n2)); intros m p; apply f_and; [apply e1|apply e2]; nia.
    - destruct IHf1 as [n1 e1]; destruct IHf2 as [n2 e2].
      apply (sigmaI _ (max n1 n2)); intros m p; apply f_or; [apply e1|apply e2]; nia.
    - destruct IHf as [n e].
      apply (sigmaI _ n); intros m p; apply f_not; apply e; nia.
  Defined.
  
  Definition close_formulas (f1 f2 : @formula nat) : { n : nat & (@formula (Fin.t n) * @formula (Fin.t n))%type }.
  Proof.
    destruct (close_formula f1) as [n1 e1]; destruct (close_formula f2) as [n2 e2].
    apply (sigmaI _ (max n1 n2)); apply pair; [apply e1|apply e2]; nia.
  Defined.

  (**
   On définit les polynômes constants 0 ([poly_zero]) et 1 ([poly_one]) ainsi que les polynômes variables ([poly_var]) et les lemmes d'évaluation correspondants.
   *)
  Fixpoint poly_zero {n} : poly true n :=
    match n with
      | O   => poly_z
      | S m => poly_l poly_zero
    end.
  Lemma zero_eval : forall n v, 0%Z = eval (@poly_zero n) v.
  Proof. intros; rewrite poly_z_eval; auto. Qed.
  Hint Rewrite <- @zero_eval : eval.
  
  Fixpoint poly_one {n} : poly false n :=
    match n with
      | O   => poly_c 1%Z (IsPos _)
      | S m => poly_l poly_one
    end.
  Lemma one_eval : forall n v, 1%Z = eval (@poly_one n) v.
  Proof. depind n; depelim v; intros; simpl; autorewrite with eval; auto. Qed.  
  Hint Rewrite <- @one_eval : eval.
  
  Equations(nocomp) poly_var {n} (f : Fin.t n) : poly false n :=
  poly_var Fin.F1     := poly_s poly_zero poly_one;
  poly_var (Fin.FS f) := poly_l (poly_var f).
  Lemma var_eval : forall n f v, Vector.nth v f = eval (@poly_var n f) v.
  Proof with autorewrite with poly_var eval in *; simpl; auto with zarith.
    induction f; depelim v; intros...
  Qed.
  Hint Rewrite <- @var_eval : eval.
  
  (** ** 2.2.a
   [poly_of_formula] transforme une formule avec [n] variables en polynôme à [n] variables.
   *)
  Equations(noind) poly_of_formula {n} (f : @formula (Fin.t n)) : { b : bool & poly b n } :=
  poly_of_formula (f_var v)       := apoly _ (poly_var v);
  poly_of_formula (f_const false) := apoly _ poly_zero;
  poly_of_formula (f_const true)  := apoly _ poly_one;
  poly_of_formula (f_not a)       := plus poly_one (poly_neg (pr2 (poly_of_formula a)));
  poly_of_formula (f_and a b)     := mult (pr2 (poly_of_formula a)) (pr2 (poly_of_formula b));
  poly_of_formula (f_or a b)      := plus (pr2 (poly_of_formula a))
                                          (pr2 (plus (pr2 (poly_of_formula b))
                                                     (poly_neg (pr2 (mult (pr2 (poly_of_formula a)) (pr2 (poly_of_formula b))))))).

  (**
   Évaluer [poly_of_formula f] donne le même résultat qu'évaluer le formule [f].
      
   *)
  Theorem poly_of_formula_eval : forall {n} (f : @formula (Fin.t n)) (v : Vector.t bool n),
                                   (if eval_formula (Vector.nth v) f then 1%Z else 0%Z) =
                                   eval (pr2 (poly_of_formula f)) (Vector.map (fun x : bool => if x then 1%Z else 0%Z) v).
  Proof.
    depind f; intros;
    autorewrite with eval_formula poly_of_formula eval in *.
    - erewrite Vector.nth_map; auto.
    - destruct b; autorewrite with eval; auto.
    - rewrite <- IHf1, <- IHf2; destruct (eval_formula (Vector.nth v) f1); destruct (eval_formula (Vector.nth v) f2); auto.
    - rewrite <- IHf1, <- IHf2; destruct (eval_formula (Vector.nth v) f1); destruct (eval_formula (Vector.nth v) f2); auto.
    - rewrite <- IHf; destruct (eval_formula (Vector.nth v) f); auto.
  Qed.
  
  (**
   Cette preuve permet de prouver l'équivalence des formules booléenes [f1] et [f2] en montrant l'égalité de [poly_of_formula f1] et [poly_of_formula f2].
   *)
  Lemma proof_1 : forall {n} (f1 f2 : @formula (Fin.t n)),
                 poly_of_formula f1 = poly_of_formula f2 ->
                 forall v, eval_formula (Vector.nth v) f1 = eval_formula (Vector.nth v) f2.
  Proof.
    intros n f1 f2 H v.
    assert (H1 := poly_of_formula_eval f1 v); assert (H2 := poly_of_formula_eval f2 v).
    remember (eval_formula (Vector.nth v) f1) as b1; remember (eval_formula (Vector.nth v) f2) as b2.
    rewrite H in H1; rewrite <- H1 in H2.
    destruct b1; destruct b2; simpl in *; (discriminate || auto).
  Qed.


  (** * Preuve de complétude *)
  

  Equations(nocomp) reduce_aux {n} {b1} (p1 : poly b1 n) {b2} (p2 : poly b2 (S n)) : { b : bool & poly b (S n) } :=
  reduce_aux p1 (poly_l p2) := poly_l_or_s p1 (poly_l p2);
  reduce_aux p1 (poly_s p2_1 p2_2) := poly_l_or_s p1 (pr2 (plus (poly_l p2_1) p2_2)).
  
  Equations(noind nocomp) reduce {n} {b} (p : poly b n) : { b : bool & poly b n } :=
  reduce poly_z       := apoly _ poly_z;
  reduce (poly_c x y) := apoly _ (poly_c x y);
  reduce (poly_l p)   := apoly _ (poly_l (pr2 (reduce p)));
  reduce (poly_s p q) := reduce_aux (pr2 (reduce p)) (pr2 (reduce q)).
  
  Theorem reduce_eval :
    forall {n} {b} (p : poly b n) (v : Vector.t bool n),
      eval p (Vector.map (fun x : bool => if x then 1%Z else 0%Z) v) =
      eval (pr2 (reduce p)) (Vector.map (fun x : bool => if x then 1%Z else 0%Z) v).
  Proof.
    Ltac YY := autorewrite with reduce reduce_aux eval; auto.
    depind p; intros; depelim v; YY.
    - rewrite IHp1, (IHp2 (Vector.cons h v)).
      remember (reduce p2) as P. 
      destruct P as [bP P]. simpl. depelim P; simpl; YY.
      destruct h; nia.
  Qed.
   
  Inductive is_reduced : forall {b} {n}, poly b n -> Prop :=
  | is_reduced_z : is_reduced poly_z
  | is_reduced_c : forall {z} {i}, is_reduced (poly_c z i)
  | is_reduced_l : forall {b} {n} (p : poly b n), is_reduced p -> is_reduced (poly_l p)
  | is_reduced_s : forall {b1} {n} (p : poly b1 n) (q : poly false n),
                     is_reduced p -> is_reduced q -> is_reduced (poly_s p (poly_l q))
  .

  Lemma is_reduced_compat_plus : forall {n} {b1} (p1 : poly b1 n) (Hp1 : is_reduced p1)
                                   {b2} (p2 : poly b2 n) (Hp2 : is_reduced p2),
                                   is_reduced (pr2 (plus p1 p2)).
  Proof.
    intros.
    depind Hp1; depelim Hp2; autorewrite with plus; unfold apoly; try constructor; auto.
    remember (z+z0)%Z as Z; destruct Z; constructor.
    specialize (IHHp1_2 _ q0 Hp2_2).
    remember (plus q q0) as Q; destruct Q as [bQ Q].
    destruct bQ; simpl. constructor; auto. constructor; auto.
  Qed.    

  Lemma is_reduced_compat_neg : forall {n} {b1} (p1 : poly b1 n) (Hp1 : is_reduced p1),
                                  is_reduced (poly_neg p1).
  Proof.
    intros. depind Hp1; try destruct i; autorewrite with poly_neg; try constructor; auto.
  Qed.
 
  Lemma is_reduced_ok : forall {b} {n} (p : poly b n), is_reduced (pr2 (reduce p)).
  Proof.
    depind p; try constructor; auto.
    autorewrite with reduce reduce_aux.
    remember (reduce p2) as P2; destruct P2 as [bP2 P2]; depelim P2; simpl.
    destruct b0; simpl. constructor. auto. constructor; auto. depelim IHp2. auto.
    depelim IHp2. unfold solution_left. simpl. autorewrite with reduce_aux plus. unfold apoly. simpl.
    assert (R := is_reduced_compat_plus _ IHp2_1 _ IHp2_2).
    remember (plus p q) as P3; destruct P3 as [bP3 P3].
    destruct bP3; simpl; constructor; auto.
  Qed.
  
  Lemma red_ok : forall {n} {b} (p : poly b n),
                   is_reduced p ->
                   (forall v, eval p (Vector.map (fun x : bool => if x then 1%Z else 0%Z) v) = 0%Z) ->
                   b = true.
  Proof.
    intros n b p Hp H; depind Hp.
    - auto.
    - specialize (H Vector.nil); autorewrite with eval in H; destruct i; discriminate.
    - apply IHHp. intro v. specialize (H (Vector.cons false v)). autorewrite with eval in H. auto.
    - assert (b1 = true).
      + apply IHHp1. intro v. specialize (H (Vector.cons false v)). autorewrite with eval in H. simpl in H. rewrite Z.add_0_r in H. auto.
      + subst. apply IHHp2.
        intro v. specialize (H (Vector.cons true v)). simpl in H. autorewrite with eval in H. rewrite poly_z_eval in H. nia.
  Qed.
      
  (** ** 2.2.c
   Cette preuve permet de prouver l'équivalence des formules booléenes [f1] et [f2] en montrant l'égalité de [reduce (poly_of_formula f1)] et [reduce (poly_of_formula f2)].
   On montre que cette stratégie est complète (on montre une équivalence)
   *)
  Lemma proof_2 : forall {n} (f1 f2 : @formula (Fin.t n)),
                    reduce (pr2 (poly_of_formula f1)) = reduce (pr2 (poly_of_formula f2)) <->
                    forall v, eval_formula (Vector.nth v) f1 = eval_formula (Vector.nth v) f2.
  Proof.
    intros n f1 f2; split.
    - intros H v.
      assert (H1 := poly_of_formula_eval f1 v); assert (H2 := poly_of_formula_eval f2 v).
      rewrite reduce_eval in H1; rewrite reduce_eval in H2.
      remember (eval_formula (Vector.nth v) f1) as b1; remember (eval_formula (Vector.nth v) f2) as b2.
      rewrite H in H1; rewrite <- H1 in H2.
      destruct b1; destruct b2; simpl in *; (discriminate || auto).
    - intros.
      assert (pr1 (plus (pr2 (reduce (pr2 (poly_of_formula f1)))) (poly_neg (pr2 (reduce (pr2 (poly_of_formula f2)))))) = true). 
      + apply red_ok with (p := pr2 (plus (pr2 (reduce (pr2 (poly_of_formula f1)))) (poly_neg (pr2 (reduce (pr2 (poly_of_formula f2))))))).
        * auto using is_reduced_compat_plus, is_reduced_ok, is_reduced_compat_neg.
        * intro; autorewrite with eval.
          assert (H1 := poly_of_formula_eval f1 v); assert (H2 := poly_of_formula_eval f2 v).
          rewrite <- !reduce_eval, <- H1, <- H2, (H v); nia.
      + apply poly_diff_z_eq in H0.
        remember (reduce (pr2 (poly_of_formula f1))) as P1; destruct P1 as [bP1 P1].
        remember (reduce (pr2 (poly_of_formula f2))) as P2; destruct P2 as [bP2 P2].
        destruct bP1; destruct bP2; auto; simpl in H0; depelim H0; auto.
  Qed.

  (** * Tactique de preuve d'égalité sur des formules booléenes *)

  (* begin hide *)
  Ltac list_add a l :=
    let rec aux a l n :=
        match l with
          | nil => constr:(n, cons a l)
          | cons a _ => constr:(n, l)
          | cons ?x ?l =>
            match aux a l (S n) with (?n, ?l) => constr:(n, cons x l) end
        end in
    aux a l 0.

  Ltac vector_of_list l :=
    match l with
      | nil => constr:Vector.nil
      | cons ?x ?xs => constr:(Vector.cons x xs)
    end.
  (* end hide *)
  
  (**
   On a besoin de lire deux formules à la fois pour que les variables correspondent.
   On lit ici des formules avec variables dans [nat].
   *)

  (** ** 2.1.c *)
  Ltac read_formula f l :=
    match f with
      | true => constr:(@f_const nat true, l)
      | false => constr:(@f_const nat false, l)
      | orb ?x ?y => match read_formula x l with (?x', ?l') =>
                    match read_formula y l' with (?y', ?l'') => constr:(f_or x' y', l'')
                    end end
      | andb ?x ?y => match read_formula x l with (?x', ?l') =>
                     match read_formula y l' with (?y', ?l'') => constr:(f_and x' y', l'')
                     end end
      | negb ?x => match read_formula x l with (?x', ?l') => constr:(f_not x', l') end
      | _ => match list_add f l with (?n, ?l') => constr:(f_var n, l') end
    end.

  Ltac read_formulas x y :=
    match read_formula x (@nil bool) with (?x', ?l) =>
    match read_formula y l with (?y', ?l') => constr:((x', y'), l')
    end end.

  (** La tactique finale.
   ** 2.2.b
      [proof_1] et [proof_2] peuvent être utilisés comme paramètres, ce qui permet de voir que [proof_1] ne donne pas une tactique complète.
   *)
  Ltac bool_tauto_with f :=
    intros;
    match goal with
      | [ |- ?x = ?y ] =>
        match read_formulas x y with
          | ((?x', ?y'), ?l) =>
            let ln := fresh "l" in
            let xyn := fresh "xy" in
            let nn := fresh "n" in
            let xn := fresh "x" in
            let yn := fresh "y" in
            match vector_of_list l with ?lv => pose (ln := lv) end;
            pose (xyn := close_formulas x' y');
            pose (n := pr1 xyn); pose (xn := fst (pr2 xyn)); pose (yn := snd (pr2 xyn));
            cbv in xyn, n, xn, yn;
            assert (H : eval_formula (Vector.nth ln) xn = eval_formula (Vector.nth ln) yn);
            [ apply f; vm_compute; reflexivity
            | exact H
            ]
        end
    end.

  (** Quelques exemples *)
  
  Goal forall a b, andb a b = andb b a.
  bool_tauto_with @proof_1.
  Qed.
  Goal forall a b, andb (negb a) (negb b) = negb (orb a b).
  bool_tauto_with @proof_1.
  Qed.
  Goal forall a b, orb (negb a) (negb b) = negb (andb a b).
  bool_tauto_with @proof_1.
  Qed.
  Goal forall a, orb (negb a) a = true.
  try bool_tauto_with @proof_1.
  bool_tauto_with @proof_2.
  Qed.
  
End M1.

(** * Preuve des premières questions *)

Module M2.
  Require Import List.

  Inductive poly : Type :=
  | Cst  : Z -> poly
  | Poly : poly -> nat -> poly -> poly
  .

  Fixpoint poly_variables (p : poly) : list nat :=
    match p with
      | Cst _      => []
      | Poly p i q => poly_variables p ++ [i] ++ poly_variables q
    end.

  (** ** 1.1.a *)
  Inductive valid : poly -> Prop :=
  | valid_Cst : forall {x}, valid (Cst x)
  | valid_Poly : forall {i} {p q},
                   Forall (fun x => ltb i x = true) (poly_variables p) ->
                   Forall (fun x => leb i x = true) (poly_variables q) ->
                   q <> Cst 0%Z ->
                   valid p -> valid q ->
                   valid (Poly p i q)
  .

  Fixpoint valid_bool (p : poly) : bool :=
    match p with
      | Cst _ => true
      | Poly p i q => forallb (ltb i) (poly_variables p) &&
                     forallb (leb i) (poly_variables q) &&
                     (match q with Cst 0%Z => false | _ => true end) &&
                     valid_bool p && valid_bool q
    end.

  Lemma Forall_forallb : forall {A} f (xs : list A), Forall (fun x => f x = true) xs -> forallb f xs = true.
  Proof.
    depind xs; auto.
    intro. depelim H. simpl. rewrite H, (IHxs H0); auto.
  Qed.
 
  Lemma forallb_Forall : forall {A} f (xs : list A), forallb f xs = true -> Forall (fun x => f x = true) xs.
  Proof.
    depind xs; auto.
    intro. simpl in H. rewrite Bool.andb_true_iff in H. destruct_pairs.
    specialize (IHxs H0). constructor; auto.
  Qed.

  (** ** 1.1.b *)
  Lemma valid_ok1 : forall p, valid p -> valid_bool p = true.
  Proof.
    induction p; intro H; auto.
    depelim H; simpl.
    rewrite (IHp1 H2), (IHp2 H3).
    rewrite !Forall_forallb; auto.
    destruct q; auto; destruct z; auto; discriminate.
  Qed.

  Lemma valid_ok2 : forall p, valid_bool p = true -> valid p.
  Proof.
    induction p; intro H.
    constructor.
    unfold valid_bool in H; rewrite !Bool.andb_true_iff in H.
    destruct_pairs.
    constructor; try apply forallb_Forall; auto.
    destruct p2; auto; try discriminate; destruct z; auto; try discriminate.
  Qed.
    
  Record valid_poly : Type :=
    { VP_value : poly;
      VP_prop  : valid_bool VP_value = true }.

  Lemma bool_uip : forall {a b : bool} (p q : a = b), p = q.
  Proof.
    destruct a; destruct b; intros;
    try inversion p;
    try exact (match p with | eq_refl => (match q with | eq_refl => eq_refl end) end).
  Qed.

  (** ** 1.1.c *)
  Lemma valid_poly_leibniz : forall (p1 p2 : poly) (r : p1 = p2) (q1 : valid_bool p1 = true) (q2 : valid_bool p2 = true), Build_valid_poly p1 q1 = Build_valid_poly p2 q2.
  Proof. intros; induction r; rewrite (bool_uip q1 q2); auto. Qed.
 
End M2.

(* *)

Print Assumptions M1.red_ok.
Print Assumptions M1.proof_2.