Require Import Arith List Omega Program.
 
Definition fvar : Type := nat. 
Definition bvar : Type := nat. 
 
Inductive sort : Type :=
| N : sort
| ArrowS : sort -> sort -> sort.
 
Definition env := list (fvar * sort).
 
Definition get (x : fvar) (e : env) : option sort :=
  match 
    find (fun p => if eq_nat_dec x (fst p) then true else false) e
  with 
    | Some p => Some (snd p) 
    | None => None
  end.
 
(* A very simple language with locally nameless binder representation *)
Inductive index : Type :=
| IBVar : bvar -> index 
| IFVar : fvar -> index
| Z : index
| Plus1 : index -> index  
| IAbs : sort -> index -> index
| IApp : index -> index -> index.
 
(* Typing rules *)
Inductive sorting (e : env) : index -> sort -> Prop :=
| IFVarRule : 
    forall (i : fvar) (s : sort),
      get i e = Some s -> 
      sorting e (IFVar i) s
| ZRule : sorting e Z N
| Plus1Rule : forall (I : index), 
                sorting e I N -> sorting e (Plus1 I) N
(* Commenting out the abstraction rule to make the example simpler *)
(* | IAbsRule : forall (I : index) (s1 s2 : sort), *)
(*                (forall (i : ifvar), *)
(*                   i # e = true -> i \notin (ifv I) = true -> *)
(*                   sorting (i :~ s1 & e) (I ii_open_var i) s2) -> *)
(*                sorting e (IAbs s1 I) (ArrowS s1 s2) *)
| IAppRule : forall (I1 I2 : index) (S1 S2 : sort),
               sorting e I1 (ArrowS S1 S2) -> sorting e I2 S1 -> 
               sorting e (IApp I1 I2) S2.
 
Definition sort_eq_dec (s1 s2 : sort) : {s1 = s2} + {s1 <> s2}. 
Proof. do 2 decide equality. Defined.
 
Fixpoint ii_open_rec (k : nat) (i : index) (x : fvar) : index :=
  match i with
    | IBVar n => if eq_nat_dec k n then (IFVar x) else (IBVar n)
    | IFVar _ | Z => i 
    | Plus1 i => Plus1 (ii_open_rec k i x)
    | IAbs s i => IAbs s (ii_open_rec (S k) i x)
    | IApp i1 i2 => IApp (ii_open_rec k i1 x) (ii_open_rec k i2 x)
  end.
 
Definition ii_open_var (i : index) (x : fvar) := ii_open_rec 0 i x. 
 
Fixpoint index_size (i : index) : nat :=
  match i with
    | IBVar _ | IFVar _ | Z => 0
    | Plus1 i | IAbs _ i  => 1 + index_size i 
    | IApp i1 i2 => 1 + (index_size i1 + index_size i2)
  end.
 
Lemma size_ii_open_rec :
  forall (i : index) (x : fvar) (rec :nat), 
    index_size (ii_open_rec rec i x) = index_size i.
Proof.
  intros i x. induction i; intros n; simpl; 
              repeat
                (match goal with
                   | [ H : forall (_ : nat), _ = _ |- _ ] => 
                     rewrite H
                 end); try omega.
  now destruct (eq_nat_dec _ _).
Defined.

Lemma size_ii_open_rec_lt :
  forall (i : index) (x : fvar),
    index_size (ii_open_var i x) < S (index_size i).
Proof.
  intros; unfold ii_open_var; rewrite size_ii_open_rec. auto with arith.
Defined.

Require Import Equations. 

Hint Resolve size_ii_open_rec_lt : Below.
Hint Extern 3 => progress auto with arith : Below.
(*
Equations infer_sort (ie : env) (i : index) : option sort :=
infer_sort ie i by rec i (MR lt index_size) := (** Need to strengthen the subst *)
infer_sort ie (IBVar x) := None ;
infer_sort ie (IFVar x) := get x ie;
infer_sort ie Z := Some N;
infer_sort ie (Plus1 i) <= infer_sort ie i => {
                     | Some N := Some N;
                     | _ := None };
infer_sort ie (IAbs s i) <= infer_sort ((0, s) :: ie) (ii_open_var i 0) => {
  infer_sort ie (IAbs s i) (Some s2) := Some (ArrowS s s2) ;
  infer_sort _ _ _ := None } ;
infer_sort ie (IApp i1 i2) <= infer_sort ie i1 => {
  | Some (ArrowS s1 s2) <= infer_sort ie i2 =>
    { | None := None;
      | Some s1' <= sort_eq_dec s1 s1' => {
               | (left _) := Some s2;
               | (right _) := None } };
  | _ := None }.
*)
(* BUG! not general enough *)
Equations infer_sort (i : index)  (ie : env) : option sort :=
infer_sort i ie by rec i (MR lt index_size) :=
infer_sort (IBVar x) ie := None ;
infer_sort (IFVar x) ie := get x ie;
infer_sort Z ie := Some N;
infer_sort (Plus1 i) ie <= infer_sort i ie => {
                     | Some N := Some N;
                     | _ := None };
infer_sort (IAbs s i) ie <= infer_sort (ii_open_var i 0)  ((0, s) :: ie)  => {
  infer_sort (IAbs s i) ie (Some s2) := Some (ArrowS s s2) ;
  infer_sort _ _ _ := None } ;
infer_sort (IApp i1 i2) ie <= infer_sort i1 ie => {
infer_sort (IApp i1 i2) ie (Some (ArrowS s1 s2)) <= infer_sort i2 ie =>
  { | None := None;
    | Some s1' <= sort_eq_dec s1 s1' => {
                 | (left _) := Some s2;
                 | (right _) := None } };
                           | _ := None }.

Lemma infer_sort_sound: 
  forall (i : index) (ie: env)  (s : sort),
    infer_sort i ie = Some s -> 
    sorting ie i s.
Proof.
  intros i ie. funelim (infer_sort i ie); intros s' Heqs; 
               try (noconf Heqs || (rewrite Heq in Heqs; noconf Heqs)).
  - now constructor. 
  - subst s'. now constructor.
  - subst s'. specialize (Hind _ Heq). now constructor.
  - subst s'. specialize (Hind _ Heq). admit.
  - subst s0. pose proof (Hind _ Heq0). pose proof (Hind0 _ Heq1).
    econstructor; eauto.
Admitted.
