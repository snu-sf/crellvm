Require Import sflib.
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

Lemma infrule_correct_replace_rhs:
  forall m1 m2 z x y e e', infrule_prop m1 m2 (rule_replace_rhs z x y e e').
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac.

  clear - H H0 H1.
  inv H; inv H0; infrule_tac.
  - econstructor; eauto; [|by apply eq_gvs_refl].
    eapply cond_replace_rhs_ext_prop in Hrhs0; eauto.
    rewrite Hlookup.
    by inv Hrhs0.
  - by destruct rhs; inv H1; eapply eq_reg_sem_old_alloca; eauto.
Qed.
Hint Resolve infrule_correct_replace_rhs: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
