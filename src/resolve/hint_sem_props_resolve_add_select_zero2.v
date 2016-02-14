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

Lemma infrule_correct_add_select_zero2:
  forall m1 m2 z x y c s n a, infrule_prop m1 m2 (rule_add_select_zero2 z x y c s n a).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; inv Hrhs1; infrule_tac.
  - eapply rhs_ext_select_true_sem; eauto.
    inv H7.
    generalize dependent H5.
    generalize dependent H4.
    unfold BOPEXT; simpl.
    rewrite Hlookup1.
    destruct (getOperandValueExt (CurTargetData cfg1) a olc1 lc1 (Globals cfg1));
      destruct (getOperandValueExt (CurTargetData cfg1) n olc1 lc1 (Globals cfg1));
      infrule_tac.
    admit. (* NOTE: impossible to prove due to incorrect semantics of undef in Vellvm *)
  - eapply rhs_ext_select_false_sem; eauto.
    inv H7.
    rewrite Hlookup0 in H0; inv H0.
    generalize dependent H5.
    generalize dependent H4.
    unfold BOPEXT; simpl.
    rewrite Hlookup1.
    destruct (getOperandValueExt (CurTargetData cfg1) a olc1 lc1 (Globals cfg1));
      destruct (getOperandValueExt (CurTargetData cfg1) n olc1 lc1 (Globals cfg1));
      infrule_tac.
    admit. (* NOTE: impossible to prove due to incorrect semantics of undef in Vellvm *)
Qed.
Hint Resolve infrule_correct_add_select_zero2: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
