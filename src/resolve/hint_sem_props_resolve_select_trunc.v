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
Require Import hint_sem_props_resolve_cond.

Lemma infrule_correct_select_trunc:
  forall m1 m2 z x y z' s1 s2 a b c, infrule_prop m1 m2 (rule_select_trunc z x y z' s1 s2 a b c).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; inv Hrhs1.
  generalize dependent H4.
  generalize dependent H5.
  generalize dependent H6.
  clear -Hrhs2 Hlookup0 Hlookup1 Hlookup2.

  unfold TRUNCEXT; simpl.
  rewrite Hlookup2.
  remember (getOperandValueExt (CurTargetData cfg2) a olc2 lc2 (Globals cfg2)) as ga; destruct ga as [ga|]; [|done].
  remember (getOperandValueExt (CurTargetData cfg2) b olc2 lc2 (Globals cfg2)) as gb; destruct gb as [gb|]; [|done].
  simpl. unfold mtrunc. infrule_tac.

  inv Hrhs2;
  repeat match goal with
           | [H: _ @ _ |- _] => inv H
         end.
  - intros. eapply rhs_ext_select_true_sem; simpl; eauto.
    rewrite <- Heqga in H5. inv H5.
    rewrite H4 in H0. inv H0.
    done.
  - intros. eapply rhs_ext_select_false_sem; simpl; eauto.
    rewrite <- Heqgb in H5. inv H5.
    rewrite H4 in H6. inv H6.
    done.
Qed.
Hint Resolve infrule_correct_select_trunc: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
