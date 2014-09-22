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

Lemma infrule_correct_add_signbit:
  forall m1 m2 x sz e s, infrule_prop m1 m2 (rule_add_signbit x sz e s).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; constructor.
  generalize dependent H5.
  clear -H0.
  unfold cond_signbit in H0.
  destruct sz0; simpl in H0; [done|].
  destruct s; simpl in H0; [done|].
  destruct c; simpl in H0; try done.
  infrule_tac.
  destruct sz5; simpl in H; [done|].
  destruct Int5; inv H0.
  unfold sumbool_rec in *.
  unfold sumbool_rect in *.
  destruct (sz_dec sz0 sz5); [subst|]; inv H.
  destruct (positive_eq_dec (basic_aux.power_sz sz5) p); [subst|]; inv H2.
  unfold BOPEXT; simpl.
  destruct (getOperandValueExt (CurTargetData cfg1) e olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  assert ((basic_aux.power_sz (sz5 - 0)%nat) = (basic_aux.power_sz (sz5)%nat)).
  + by rewrite <- (minus_n_O sz5).
  + rewrite <- H.
    by apply Int_xor_add.
Qed.
Hint Resolve infrule_correct_add_signbit: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
