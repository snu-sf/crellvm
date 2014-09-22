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

Lemma infrule_correct_add_const_not:
  forall m1 m2 z y s x c1 c2, infrule_prop m1 m2 (rule_add_const_not z y s x c1 c2).
Proof.
  repeat intro; infrule_tac.
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
    infrule_tac; repeat arith_tac.
  unfold cond_minus in H1; arith_tac; inv H1.
  rewrite e3.
  rewrite Int_sub_add_not.
  rewrite Int.add_assoc, Int.add_permut; f_equal.
  rewrite Int.sub_add_opp, Int.add_assoc.
  rewrite <- Int.add_zero; f_equal.
  by rewrite Int.add_commut, Int.add_neg_zero.
Qed.
Hint Resolve infrule_correct_add_const_not: InfRuleDb.

(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
