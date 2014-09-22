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

Lemma infrule_correct_replace_lhs:
  forall m1 m2 x y e, infrule_prop m1 m2 (rule_replace_lhs x y e).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac.
  inv H0; [|inv H1].
  destruct H; infrule_tac.
  - inv H; infrule_tac.
    rewrite Hlookup in Hlookup0; inv Hlookup0.
      by econstructor; eauto; infrule_tac.
  - inv H; infrule_tac.
    simpl in H0.
    rewrite Hlookup in H0; inv H0.
      by econstructor; eauto; infrule_tac.
Qed.
Hint Resolve infrule_correct_replace_lhs: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
