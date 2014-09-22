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

Lemma infrule_correct_div_mone:
  forall m1 m2 z sz x, infrule_prop m1 m2 (rule_div_mone z sz x).
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
    infrule_tac; arith_tac.
  - unfold Int.zero, INTEGER.to_Z, INTEGER.of_Z in e1; inv e1.
    rewrite (Zmod_small 0) in H0.
    + rewrite <- (Zdiv.Zmod_unique (-1) (Int.modulus (Size.to_nat sz0 - 1)) (-1) (Int.modulus (Size.to_nat sz0 - 1) - 1)) in H0; try omega; try done.
      split; [done|].
      destruct (two_p_bytesize_chunk__ge__modulus (Size.to_nat sz0 - 1)).
      by destruct (Int.modulus (Size.to_nat sz0 - 1)); try omega.
    + split; [done|].
      by destruct (two_p_bytesize_chunk__ge__modulus (Size.to_nat sz0 - 1)).
  - rewrite Int.sub_zero_r, Int_mone.
    by apply Int_neg_divs.
Qed.
Hint Resolve infrule_correct_div_mone: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
