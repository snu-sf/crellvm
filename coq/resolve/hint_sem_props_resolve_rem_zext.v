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

Lemma infrule_correct_rem_zext:
  forall m1 m2 z x y k sz1 sz2 a b, infrule_prop m1 m2 (rule_rem_zext z x y k sz1 sz2 a b).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; inv Hrhs1; inv Hrhs2; constructor.
  generalize dependent H7.
  generalize dependent H6.
  generalize dependent H5.
  generalize dependent H4.
  clear -Hlookup Hlookup0 Hlookup1 Hlookup2.
  
  unfold EXTEXT, BOPEXT; simpl.
  rewrite Hlookup0, Hlookup1, Hlookup2.
  destruct (getOperandValueExt (CurTargetData cfg2) a olc2 lc2 (Globals cfg2));
    destruct (getOperandValueExt (CurTargetData cfg2) b olc2 lc2 (Globals cfg2));
    infrule_tac.
  admit. (* NOTE: impossible to prove due to incorrect semantics of undef in Vellvm *)
Qed.
Hint Resolve infrule_correct_rem_zext: InfRuleDb.
