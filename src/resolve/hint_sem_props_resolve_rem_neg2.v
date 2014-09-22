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
Require Import hint_sem_props_resolve_integers.

Lemma infrule_correct_rem_neg2:
  forall m1 m2 z sz x c1 c2, infrule_prop m1 m2 (rule_rem_neg2 z sz x c1 c2).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; constructor.
  generalize dependent H5.
  clear -H0 Hlookup.

  unfold cond_minus in H0; arith_tac; inv H0.  
  rewrite Int.sub_zero_r in e.

  unfold BOPEXT; simpl.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  - rewrite e, e1, Int.neg_zero in n.
    by contradict n.
  - rewrite e2 in e.
    contradict n.
    by exploit Int_neg_eq; eauto.
  - rewrite e.
    by apply Int_mods_neg.
Qed.
Hint Resolve infrule_correct_rem_neg2: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
