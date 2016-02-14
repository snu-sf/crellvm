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

Lemma infrule_correct_sub_onebit:
  forall m1 m2 z x y, infrule_prop m1 m2 (rule_sub_onebit z x y).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; constructor.
  generalize dependent H4.
  clear.
  
  unfold BOPEXT; simpl.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    destruct (getOperandValueExt (CurTargetData cfg1) y olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  unfold Size.to_nat, Size.One in e.
  assert (wz0 = 0%nat); [omega|subst].
  arith_tac.    
  by apply Int_0_xor_sub.
Qed.
Hint Resolve infrule_correct_sub_onebit: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
