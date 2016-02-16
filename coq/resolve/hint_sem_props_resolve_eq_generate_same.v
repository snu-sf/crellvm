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

Lemma infrule_correct_eq_generate_same:
  forall m1 m2 x y e, infrule_prop m1 m2 (rule_eq_generate_same x y e).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Heq; infrule_tac.
  destruct Heq; infrule_tac.
  inv H; inv H0; try by inv H1.
  econstructor; eauto.
  constructor; simpl; infrule_tac.
  rewrite Hlookup0.
  f_equal.
  by eapply rhs_ext_value_sem_proper; eauto.
Qed.
Hint Resolve infrule_correct_eq_generate_same: InfRuleDb.
