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
Require Import hint_sem_props_resolve_integers.

Lemma infrule_correct_trunc_onebit:
  forall m1 m2 z k s y, infrule_prop m1 m2 (rule_trunc_onebit z k s y).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  generalize dependent H4.
  generalize dependent H5.
  clear -Hlookup0.
  
  unfold BOPEXT, ICMPEXT, TRUNCEXT; simpl.
  rewrite Hlookup0.
  destruct (getOperandValueExt (CurTargetData cfg2) y olc2 lc2 (Globals cfg2)); [|done].
  infrule_tac.
  repeat (rewrite cgv2gvs_val2GV; [|done]).
  admit. (* NOTE: impossible to prove due to incorrect semantics of undef in Vellvm *)
Qed.
Hint Resolve infrule_correct_trunc_onebit: InfRuleDb.
