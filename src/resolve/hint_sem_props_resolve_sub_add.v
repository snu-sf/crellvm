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

Lemma infrule_correct_sub_add:
  forall m1 m2 z minusy s x y, infrule_prop m1 m2 (rule_sub_add z minusy s x y).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  generalize dependent H4.
  generalize dependent H5.
  
  unfold BOPEXT; simpl.
  rewrite Hlookup0.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    destruct (getOperandValueExt (CurTargetData cfg1) y olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  - rewrite Int.sub_add_opp; f_equal.
    rewrite Int.sub_zero_r.
    by rewrite Int.neg_involutive.
  - by contradict n; omega.
  - by rewrite <- e in n; contradict n; omega.
Qed.
Hint Resolve infrule_correct_sub_add: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
