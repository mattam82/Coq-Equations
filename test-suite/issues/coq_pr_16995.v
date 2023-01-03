(* -*- mode: coq; coq-prog-args: ("-emacs" "-q" "-w" "-deprecated-native-compiler-option" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/equations/test-suite" "TestSuite" "-R" "/github/workspace/builds/coq/coq-failing/_build_ci/equations/theories" "Equations" "-Q" "/github/workspace/cwd" "Top" "-Q" "/github/workspace/builds/coq/coq-failing/_install_ci/lib/coq/user-contrib/Ltac2" "Ltac2" "-I" "/github/workspace/builds/coq/coq-failing/_build_ci/equations/src" "-top" "TestSuite.LogicType" "-native-compiler" "no") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 119 lines to 7 lines, then from 20 lines to 75 lines, then from 80 lines to 9 lines, then from 22 lines to 165 lines, then from 170 lines to 83 lines, then from 96 lines to 207 lines, then from 212 lines to 106 lines, then from 119 lines to 931 lines, then from 931 lines to 106 lines, then from 111 lines to 106 lines *)
(* coqc version 8.18+alpha compiled with OCaml 4.09.0
   coqtop version runner-jztamce-project-6138686-concurrent-0:/builds/coq/coq/_build/default,(HEAD detached at b5df8e0) (b5df8e0be892b66f6f48f588ceb3130c7e853be2)
   Expected coqc runtime on this file: 0.314 sec *)
Require Equations.Type.DepElim.

Register Equations.Init.sigma as equations.sigma.type.
Register Equations.Init.sigmaI as equations.sigma.intro.
Register Equations.Init.pr1 as equations.sigma.pr1.
Register Equations.Init.pr2 as equations.sigma.pr2.

Register Logic.Id as equations.equality.type.
Register Logic.id_refl as equations.equality.refl.

Register Logic.Empty as equations.bottom.type.
Register Logic.Empty_case as equations.bottom.case.
Register Logic.Empty_rect as equations.bottom.elim.

Register Coq.Init.Datatypes.unit as equations.top.type.
Register Equations.Type.Logic.unit_rect as equations.top.elim.

Register DepElim.solution_left as equations.depelim.solution_left.
Register DepElim.solution_right_dep as equations.depelim.solution_right_dep.

Register Classes.NoConfusionPackage as equations.noconfusion.class.
Register Classes.apply_noConfusion as equations.depelim.apply_noConfusion.
Register DepElim.simplification_sigma1_dep as equations.depelim.simpl_sigma_dep.
Register DepElim.opaque_ind_pack_inv as equations.depelim.opaque_ind_pack_eq_inv.
Import Equations.CoreTactics.

Set Warnings "-notation-overridden".
Import Equations.Type.Logic.
Import Equations.Type.DepElim.

Ltac solve_noconf_prf := intros;
    on_last_hyp ltac:(fun id => destruct id) ;
    on_last_hyp ltac:(fun id =>
                        destruct_sigma id;
                        destruct id) ;
    constructor.

Ltac solve_noconf_inv_eq a b :=
    destruct_sigma a; destruct_sigma b;
    destruct a ; depelim b; simpl in * |-;
    on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || destruct id);
    solve [constructor].

Ltac solve_noconf_inv := intros;
    match goal with
    |- ?R ?a ?b => destruct_sigma a; destruct_sigma b;
                    destruct a ; depelim b; simpl in * |-;
                on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || destruct id);
                solve [constructor]
    | |- @Id _ (?f ?a ?b _) _ => solve_noconf_inv_eq a b
    end.

Ltac solve_noconf_inv_equiv :=
    intros;

    on_last_hyp ltac:(fun id => destruct id) ;

    on_last_hyp ltac:(fun id => destruct_sigma id; destruct id) ;
    simpl; constructor.

Ltac solve_noconf := simpl; intros;
    match goal with
        [ H : @Id _ _ _ |- @Id _ _ _ ] => try solve_noconf_inv_equiv
    | [ H : @Id _ _ _ |- _ ] => try solve_noconf_prf
    | [ |- @Id _ _ _ ] => try solve_noconf_inv
    end.

Ltac solve_noconf_hom_inv_eq a b :=
    destruct_sigma a; destruct_sigma b;
    destruct a ; depelim b; simpl in * |-;
    on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || depelim id);
    solve [constructor || simpl_equations; constructor].

Ltac solve_noconf_hom_inv := intros;
    match goal with
    | |- @Id _ (?f ?a ?b _) _ => solve_noconf_hom_inv_eq a b
    | |- ?R ?a ?b =>
    destruct_sigma a; destruct_sigma b;
    destruct a ; depelim b; simpl in * |-;
    on_last_hyp ltac:(fun id => hnf in id; destruct_tele_eq id || depelim id);
    solve [constructor || simpl_equations; constructor]
    end.

Ltac solve_noconf_hom_inv_equiv :=
    intros;

    on_last_hyp ltac:(fun id => destruct id) ;

    on_last_hyp ltac:(fun id => destruct_sigma id; depelim id) ;
    simpl; simpl_equations; constructor.

Ltac solve_noconf_hom := simpl; intros;
    match goal with
        [ H : @Id _ _ _ |- @Id _ _ _ ] => try solve_noconf_hom_inv_equiv
    | [ H : @Id _ _ _ |- _ ] => try solve_noconf_prf
    | [ |- @Id _ _ _ ] => try solve_noconf_hom_inv
    end.

Ltac Equations.Init.solve_noconf ::= solve_noconf.
Ltac Equations.Init.solve_noconf_hom ::= solve_noconf_hom.

Derive NoConfusion for unit bool nat option sum Datatypes.prod list sigT sig.
Inductive vector@{i} (A : Type@{i}) : nat -> Type@{i} :=
| nil : vector A 0
| cons {n : nat} : A -> vector A n -> vector A (S n).
Derive Signature NoConfusionHom for vector.