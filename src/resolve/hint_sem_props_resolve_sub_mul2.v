Require Import vgtac.
Require Import vellvm.

Require Import decs.
Require Import validator_aux.
Require Import validator_props.
Require Import set_facts2.
Require Import state_props.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import logical_step.
Require Import infrules.

Import Opsem.
Require Import syntax_ext.
Require Import hints.

Require Import hint_sem_props_resolve_defs.

Lemma infrule_correct_sub_mul2:
  forall m1 m2 z y sz x c c', infrule_prop m1 m2 (rule_sub_mul2 z y sz x c c').
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  generalize dependent H6.
  generalize dependent H5.
  unfold BOPEXT; simpl.
  rewrite Hlookup0.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  unfold cond_minus in H1; arith_tac; inv H1.
  rewrite e2.
  repeat rewrite Int.sub_add_opp.
  rewrite Int.mul_add_distr_r; f_equal.
  rewrite <- Int.neg_mul_distr_r; f_equal.
  by apply Int.mul_one.
Qed.
Hint Resolve infrule_correct_sub_mul2: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
