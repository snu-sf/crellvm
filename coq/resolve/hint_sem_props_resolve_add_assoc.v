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

Lemma infrule_correct_add_assoc:
  forall m1 m2 z y x s c1 c2 c3, infrule_prop m1 m2 (rule_add_assoc z y x s c1 c2 c3).
Proof.
  repeat intro; infrule_tac.
  infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  generalize dependent H5.
  generalize dependent H6.
  clear -H1 Hlookup Hlookup0.
  
  unfold BOPEXT; simpl.
  rewrite Hlookup0.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  rewrite Int.add_assoc; f_equal.
  by unfold cond_plus in H1; arith_tac.
Qed.
Hint Resolve infrule_correct_add_assoc: InfRuleDb.
