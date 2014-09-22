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

Lemma infrule_correct_remove_maydiff_rhs:
  forall m1 m2 v e, infrule_prop m1 m2 (rule_remove_maydiff_rhs v e).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intro var; infrule_tac.
  intro HH; destruct HH as [HH|HH]; [by apply Hmd|]; infrule_tac.
Qed.
Hint Resolve infrule_correct_remove_maydiff_rhs: InfRuleDb.

(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
