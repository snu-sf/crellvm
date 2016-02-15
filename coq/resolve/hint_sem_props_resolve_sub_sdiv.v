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

Lemma infrule_correct_sub_sdiv:
  forall m1 m2 z y sz x c c', infrule_prop m1 m2 (rule_sub_sdiv z y sz x c c').
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  generalize dependent H6.
  generalize dependent H5.
  clear -H1 Hlookup Hlookup0.
  
  unfold BOPEXT; simpl.
  rewrite Hlookup0.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  - unfold cond_minus in H1; arith_tac; inv H1.
    rewrite e1 in e3.
    rewrite Int.sub_zero_l in e3.
    by rewrite e3 in n.
  - unfold cond_minus in H1; arith_tac; inv H1.
    rewrite e2 in e3.
    rewrite Int.sub_zero_r in e3.
    generalize (Int.neg_involutive _ (Int.repr (Size.to_nat sz0 - 1) (INTEGER.to_Z c))); intro Hneg.
    rewrite <- e3 in Hneg.
    rewrite Int.neg_zero in Hneg.
    rewrite <- Hneg.
    by contradict n.
  - rewrite Int.sub_add_opp.
    rewrite <- (Int.add_zero _ (Int.divs (Size.to_nat sz0 - 1) i1 (Int.repr (Size.to_nat sz0 - 1) (INTEGER.to_Z c')))).
    rewrite Int.add_commut; f_equal.
    unfold cond_minus in H1; arith_tac; inv H1.
    rewrite e2, Int.sub_zero_r.
    by apply Int_divs_neg.
Qed.
Hint Resolve infrule_correct_sub_sdiv: InfRuleDb.
