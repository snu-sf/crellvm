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

Lemma infrule_correct_remove_maydiff:
  forall m1 m2 v e, infrule_prop m1 m2 (rule_remove_maydiff v e).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intro var; infrule_tac.
  intro HH; destruct HH as [HH|HH]; [by apply Hmd|]; infrule_tac.
  inv H; inv H0; infrule_tac.
  unfold variable_equivalent.
  rewrite Hlookup0, Hlookup.
  by eapply cond_same_prop; eauto.
Qed.
Hint Resolve infrule_correct_remove_maydiff: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
