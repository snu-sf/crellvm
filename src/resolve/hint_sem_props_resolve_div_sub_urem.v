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

Lemma infrule_correct_div_sub_urem:
  forall m1 m2 z b a sz x y, infrule_prop m1 m2 (rule_div_sub_urem z b a sz x y).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; inv Hrhs1; constructor.
  generalize dependent H6.
  generalize dependent H5.
  generalize dependent H4.
  unfold BOPEXT; simpl.
  rewrite Hlookup0, Hlookup1.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    destruct (getOperandValueExt (CurTargetData cfg1) y olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  by apply Int_divu_modu.
Qed.
Hint Resolve infrule_correct_div_sub_urem: InfRuleDb.

(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
