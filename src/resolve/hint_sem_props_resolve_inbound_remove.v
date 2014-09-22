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
Require Import hint_sem_props_resolve_cond.

Lemma infrule_correct_inbound_remove:
  forall m1 m2 x y pt pa t a idx u v, infrule_prop m1 m2 (rule_inbound_remove x y pt pa t a idx u v).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  simpl in *.
  rewrite Hlookup0.
  unfold MDGVs.lift_op1 in *.
  rewrite <- H9, <- H13.
  rewrite H6 in H10. inv H10.
  rewrite H7 in H11. inv H11.
  clear Hlookup Hlookup0 H7.
  unfold gep, genericvalues.LLVMgv.GEP.
  destruct (GV2ptr (CurTargetData cfg1) (getPointerSize (CurTargetData cfg1)) mp0); [|done].
  assert (vidxs = vidxs0); [|by subst].
  clear -H8 H12.
  generalize dependent vidxss0.
  generalize dependent vidxs0.
  generalize dependent vidxs.
  intro l1; induction l1; intros [|i2 l2] L Hv1 Hv2; inv Hv1; inv Hv2; try done.
  inv H1. inv H4. f_equal.
  by eapply IHl1; eauto.
Qed.
Hint Resolve infrule_correct_inbound_remove: InfRuleDb.

(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
