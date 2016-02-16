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

Lemma infrule_correct_ptr_trans:
  forall m1 m2 p q v t a, infrule_prop m1 m2 (rule_ptr_trans p q v t a).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros r tt aa s; infrule_tac.

  intro HH; infrule_tac; destruct HH as [HH|HH]; infrule_tac.
  inv H; infrule_tac.
  generalize dependent H0.
  rewrite <- Hlookup in H1.
  unfold eq_heap_sem.
  by rewrite H1; infrule_tac.
Qed.
Hint Resolve infrule_correct_ptr_trans: InfRuleDb.
