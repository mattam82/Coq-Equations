From Equations Require Import Equations.
From Coq Require Import Program Arith Compare_dec List.
Import ListNotations.
(*


In environment
eos := CoreTactics.the_end_of_the_section : CoreTactics.end_of_section
H : forall z : exp, c_exp_tc_graph z (c_exp_tc z)
c_exps : forall zs : list exp, c_exps_graph zs (c_exps zs)
zs : list exp
a : exp
l : list exp
c_exp_notc : forall z : exp, c_exp_notc_graph z (c_exp_notc z)
z : exp
l0 : list exp
Recursive call to c_exps has principal argument equal to 
"l0" instead of "l".
Recursive definition is:
"fun zs : list exp =>
 (fun zs0 : list exp =>
  match
    zs0 as l
    return
      (let H := CoreTactics.block in
       let H0 := CoreTactics.block in c_exps_graph l (issue_mutual.c_exps l))
  with
  | [] =>
      let _H := CoreTactics.block in
      eq_rec_r (fun n : nat => c_exps_graph [] n) c_exps_graph_equation_1
        c_exps_equation_1
  | a :: l =>
      (fun (e : exp) (zs1 : list exp) =>
       let _H := CoreTactics.block in
       eq_rec_r (fun n : nat => c_exps_graph (e :: zs1) n)
         (c_exps_graph_equation_2 e zs1
            (let
               fix c_exp_notc (z : exp) :
                   c_exp_notc_graph z (c_exp_notc z) :=
                 (fun z0 : exp =>
                  match
                    z0 as e0
                    return
                      (let H := CoreTactics.block in
                       let H0 := CoreTactics.block in
                       c_exp_notc_graph e0 (issue_mutual.c_exp_notc e0))
                  with
                  | Const n =>
                      (fun n0 : nat =>
                       let _H0 := CoreTactics.block in
                       eq_rec_r
                         (fun n1 : nat => c_exp_notc_graph (Const n0) n1)
                         (c_exp_notc_graph_equation_1 n0)
                         (c_exp_notc_equation_1 n0)) n
                  | Var n =>
                      (fun n0 : nat =>
                       let _H0 := CoreTactics.block in
                       eq_rec_r
                         (fun n1 : nat => c_exp_notc_graph (Var n0) n1)
                         (c_exp_notc_graph_equation_2 n0)
                         (c_exp_notc_equation_2 n0)) n
                  | Op l0 =>
                      (fun l1 : list exp =>
                       let _H0 := CoreTactics.block in
                       eq_rec_r (fun n : nat => c_exp_notc_graph (Op l1) n)
                         (c_exp_notc_graph_equation_3 l1 (c_exps l1))
                         (c_exp_notc_equation_3 l1)) l0
                  | If l0 e0 e1 =>
                      (fun (l1 : list exp) (z1 z2 : exp) =>
                       let _H0 := CoreTactics.block in
                       eq_rec_r
                         (fun n : nat => c_exp_notc_graph (If l1 z1 z2) n)
                         (c_exp_notc_graph_equation_4 l1 z1 z2 
                            (c_exps l1)
                            (let r1 := issue_mutual.c_exps l1 in
                             c_exp_notc z2)
                            (let r1 := issue_mutual.c_exps l1 in
                             let r2 := issue_mutual.c_exp_notc z2 in
                             c_exp_notc z1)) (c_exp_notc_equation_4 l1 z1 z2))
                        l0 e0 e1
                  | Let n e0 e1 =>
                      (fun (n0 : nat) (z1 z2 : exp) =>
                       let _H0 := CoreTactics.block in
                       eq_rec_r
                         (fun n1 : nat => c_exp_notc_graph (Let n0 z1 z2) n1)
                         (c_exp_notc_graph_equation_5 n0 z1 z2
                            (c_exp_notc z1)
                            (let r1 := issue_mutual.c_exp_notc z1 in
                             c_exp_notc z2)) (c_exp_notc_equation_5 n0 z1 z2))
                        n e0 e1
                  | Call n l0 =>
                      (fun (n0 : nat) (l1 : list exp) =>
                       let _H0 := CoreTactics.block in
                       eq_rec_r
                         (fun n1 : nat => c_exp_notc_graph (Call n0 l1) n1)
                         (c_exp_notc_graph_equation_6 n0 l1 (c_exps l1))
                         (c_exp_notc_equation_6 n0 l1)) n l0
                  end) z in
             c_exp_notc e) (let res1 := c_exp_notc e in c_exps zs1))
         (c_exps_equation_2 e zs1)) a l
  end) zs".
This will become an error in the future [solve_obligation_error,tactics]coqtop
Functional induction principle could not be p

olve Obligations tactic returned error: Recursive definition of c_exps is ill-formed.
In environment
eos := CoreTactics.the_end_of_the_section : CoreTactics.end_of_section
H : forall z : exp, c_exp_tc_graph z (c_exp_tc z)
c_exps : forall zs : list exp, c_exps_graph zs (c_exps zs)
zs : list exp
a : exp
l : list exp
c_exp_notc : forall z : exp, c_exp_notc_graph z (c_exp_notc z)
z : exp
l0 : list exp
Recursive call to c_exps has principal argument equal to 
"l0" instead of "l".
Recursive definition is:
"fun zs : list exp =>
 (fun zs0 : list exp =>
  match
    zs0 as l
    return
      (let H := CoreTactics.block in
       let H0 := CoreTactics.block in c_exps_graph l (issue_mutual.c_exps l))
  with
  | [] => let _H := CoreTactics.block in c_exps_graph_equation_1
  | a :: l =>
      (fun (e : exp) (zs1 : list exp) =>
       let _H := CoreTactics.block in
       c_exps_graph_equation_2 e zs1
         (let
            fix c_exp_notc (z : exp) : c_exp_notc_graph z (c_exp_notc z) :=
              (fun z0 : exp =>
               match
                 z0 as e0
                 return
                   (let H := CoreTactics.block in
                    let H0 := CoreTactics.block in
                    c_exp_notc_graph e0 (issue_mutual.c_exp_notc e0))
               with
               | Const n =>
                   (fun n0 : nat =>
                    let _H0 := CoreTactics.block in
                    c_exp_notc_graph_equation_1 n0) n
               | Var n =>
                   (fun n0 : nat =>
                    let _H0 := CoreTactics.block in
                    c_exp_notc_graph_equation_2 n0) n
               | Op l0 =>
                   (fun l1 : list exp =>
                    let _H0 := CoreTactics.block in
                    c_exp_notc_graph_equation_3 l1 (c_exps l1)) l0
               | If l0 e0 e1 =>
                   (fun (l1 : list exp) (z1 z2 : exp) =>
                    let _H0 := CoreTactics.block in
                    c_exp_notc_graph_equation_4 l1 z1 z2 
                      (c_exps l1)
                      (let r1 := issue_mutual.c_exps l1 in c_exp_notc z2)
                      (let r1 := issue_mutual.c_exps l1 in
                       let r2 := issue_mutual.c_exp_notc z2 in c_exp_notc z1))
                     l0 e0 e1
               | Let n e0 e1 =>
                   (fun (n0 : nat) (z1 z2 : exp) =>
                    let _H0 := CoreTactics.block in
                    c_exp_notc_graph_equation_5 n0 z1 z2 
                      (c_exp_notc z1)
                      (let r1 := issue_mutual.c_exp_notc z1 in c_exp_notc z2))
                     n e0 e1
               | Call n l0 =>
                   (fun (n0 : nat) (l1 : list exp) =>
                    let _H0 := CoreTactics.block in
                    c_exp_notc_graph_equation_6 n0 l1 (c_exps l1)) n l0
               end) z in
          c_exp_notc e) (let res1 := c_exp_notc e in c_exps zs1)) a l
  end) zs".
This will become an error in the future [solve_obligation_error,tactics]coqtop


*)

Set Equations Transparent.
Inductive exp :=
  | If : list exp -> exp -> exp.
  
Equations c_exp_tc (z: exp) : nat by struct z :=
{ c_exp_tc (If xs x) :=
    let r1 := c_exps xs in
    let r2 := c_exp_tc x in
    r1 }
where c_exp_notc (z: exp) : nat by struct z :=
{ c_exp_notc (If xs x) :=
    let r1 := c_exps xs in
    let r2 := c_exp_notc x in
    r1 }
where c_exps (zs: list exp) : nat by struct zs :=
{ c_exps [] := 0 ;
  c_exps (x :: xs) :=
    let res2 := c_exps xs in
    let res1 := c_exp_notc x in
    res1 + res2 }.
    Transparent c_exp_tc c_exp_notc c_exps.
  Obligation Tactic := idtac.
  Equations? (noind) gc_exp_tc (z: exp) : c_exp_tc_graph z (c_exp_tc z) :=
    { gc_exp_tc (If xs y) :=
      let r1 := gc_exps xs in
      let r2 := gc_exp_tc y in
      _ }
  where gc_exp_notc (z: exp) : c_exp_notc_graph z (c_exp_notc z) by struct z :=
  { gc_exp_notc (If xs y) :=
      let r1 := c_exps xs in
      let r2 := gc_exp_notc y in
      _ }
  where gc_exps (zs: list exp) : c_exps_graph zs (c_exps zs) by struct zs :=
  { gc_exps [] := _ ;
    gc_exps (x :: xs) :=
      let res2 := gc_exps xs in
      let res1 := gc_exp_notc x in _ }.
  Proof.
    all:autorewrite with c_exp_tc; simpl; constructor; try assumption.
    apply gc_exps.
  Defined.
  





      (*
        zs0 as l
    return
      (let H := CoreTactics.block in
       let H0 := CoreTactics.block in c_exps_graph l (issue_mutual.c_exps l))
  with
  | [] => let _H := CoreTactics.block in c_exps_graph_equation_1
  | a :: l =>
      (fun (e : exp) (zs1 : list exp) =>
       let _H := CoreTactics.block in
       c_exps_graph_equation_2 e zs1 (c_exps zs1)
         (let res2 := issue_mutual.c_exps zs1 in
          let
            fix c_exp_notc (z : exp) : c_exp_notc_graph z (c_exp_notc z) :=
              (fun z0 : exp =>
               match
                 z0 as e0
                 return
                   (let H := CoreTactics.block in
                    let H0 := CoreTactics.block in
                    c_exp_notc_graph e0 (issue_mutual.c_exp_notc e0))
               with
               | If l0 =>
                   (fun l1 : list exp =>
                    let _H0 := CoreTactics.block in
                    c_exp_notc_graph_equation_1 l1 (c_exps l1)) l0
               end) z in
          c_exp_notc e)) a l
  end) zs *)

 
Fixpoint c_exps (zs : list exp) : c_exps_graph zs (issue_mutual.c_exps zs) :=
   match
     zs as l
     return
       (c_exps_graph l (issue_mutual.c_exps l))
   with
   | [] => c_exps_graph_equation_1
   | e :: zs1 =>
        c_exps_graph_equation_2 e zs1 (c_exps zs1)
          (let
             fix c_exp_notc (z : exp) : c_exp_notc_graph z (c_exp_notc z) :=
                match
                  z as e0
                  return
                    (c_exp_notc_graph e0 (issue_mutual.c_exp_notc e0))
                with
                | If l0 => c_exp_notc_graph_equation_1 l0 (c_exps l0)
                end in
           c_exp_notc e)
   end.


Equations c_exp_tc (z: exp) : nat by struct z :=
{ c_exp_tc (Let n x y) :=
    let r1 := c_exp_notc x in
    let r2 := c_exp_tc y in
    r1 + r2 ;
  c_exp_tc (If xs y z) :=
    let r1 := c_exps xs in
    let r2 := c_exp_tc z in
    let r3 := c_exp_tc y in
    r1 + r2 + r3 ;
  c_exp_tc (Call n xs) :=
    c_exps xs ;
  c_exp_tc z :=
    c_exp_notc z }
where c_exp_notc (z: exp) : nat by struct z :=
{ c_exp_notc (Let n x y) :=
    let r1 := c_exp_notc x in
    let r2 := c_exp_notc y in
    r1 + r2 ;
  c_exp_notc (If xs y z) :=
    let r1 := c_exps xs in
    let r2 := c_exp_notc z in
    let r3 := c_exp_notc y in
    r1 + r2 + r3 ;
  c_exp_notc (Call n xs) := c_exps xs ;
  c_exp_notc (Const n) := n ;
  c_exp_notc (Var n) := n ;
  c_exp_notc (Op xs) := c_exps xs }
where c_exps (zs: list exp) : nat by struct zs :=
{ c_exps [] := 0 ;
  c_exps (x :: xs) :=
    let res2 := c_exps xs in
    let res1 := c_exp_notc x in
    res1 + res2 }.
