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

Lemma infrule_correct_add_mask:
  forall m1 m2 z y y' s x c1 c2, infrule_prop m1 m2 (rule_add_mask z y y' s x c1 c2).
Proof.
  repeat intro; infrule_tac.
  infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; inv Hrhs1; constructor.
  generalize dependent H5.
  generalize dependent H6.
  generalize dependent H7.
  clear -H2 Hlookup Hlookup0 Hlookup1.
  
  unfold BOPEXT; simpl.
  rewrite Hlookup0, Hlookup1.
  destruct (getOperandValueExt (CurTargetData cfg2) x olc2 lc2 (Globals cfg2));
    infrule_tac; arith_tac.
  clear -H2. unfold cond_mask_up in H2. arith_tac.
  admit. (* arithmetic *)
Qed.
Hint Resolve infrule_correct_add_mask: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
