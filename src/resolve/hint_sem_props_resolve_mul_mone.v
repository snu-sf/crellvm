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
Require Import hint_sem_props_resolve_integers.

Lemma infrule_correct_mul_mone:
  forall m1 m2 z sz x, infrule_prop m1 m2 (rule_mul_mone z sz x).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; constructor.
  generalize dependent H4.
  unfold BOPEXT; simpl.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  rewrite Int.sub_add_opp.
  rewrite Int.add_commut.
  rewrite Int.add_zero.
  rewrite <- Int.neg_involutive; f_equal.
  rewrite Int.neg_mul_distr_r.
  rewrite <- (Int.mul_one _ i0); f_equal.
  - by rewrite (Int.mul_one _ i0).
  - rewrite <- (Int.neg_involutive _ (Int.one _)); repeat f_equal.
    by rewrite Int_neg_one.
Qed.
Hint Resolve infrule_correct_mul_mone: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
