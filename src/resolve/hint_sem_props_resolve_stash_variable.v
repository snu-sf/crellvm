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
Require Import hint_sem_props_resolve_cond.

Lemma infrule_correct_stash_variable:
  forall m1 m2 z t, infrule_prop m1 m2 (rule_stash_variable z t).
Proof.
  repeat intro; infrule_tac.
  unfold mem_md in H.
  generalize (Hmd z).
  infrule_tac.
  destruct (IdExtSetImpl.mem z (hint_maydiff h)); [done|].
  clear H; intro H.
  exploit H; eauto; clear H; intro H.

  unfold cond_fresh in H2; infrule_tac.
  unfold cond_fresh_md in H2; infrule_tac.
  unfold cond_fresh_inv in H3; infrule_tac.
  apply IdExtSetFacts.for_all_iff in H2; [|by repeat intro; subst].
  unfold cond_fresh_eqs in H3, H4; infrule_tac.
  unfold variable_equivalent in H.
  remember (lookupALExt olc1 lc1 z) as z1; destruct z1.
  - remember (lookupALExt olc2 lc2 z) as z2; destruct z2; [|done].
    exists (updateAddAL _ olc1 t g).
    exists (updateAddAL _ olc2 t g0).
    infrule_tac; split.
    + apply fresh_maydiff_updateAddAL_prop; auto.
    + constructor; simpl.
      * repeat split; infrule_tac.
        by apply eqs_sem_reg_updateAddAL_prop.
        by eapply eqs_sem_heap_updateAddAL_prop; eauto.
        by eapply neqs_sem_reg_updateAddAL_prop; eauto.
      * repeat split; infrule_tac.
        by apply eqs_sem_reg_updateAddAL_prop.
        by eapply eqs_sem_heap_updateAddAL_prop; eauto.
        by eapply neqs_sem_reg_updateAddAL_prop; eauto.
        admit. (* TODO: t should not be in iso *)
        admit. (* TODO: t should not be in iso *)
  - exploit cond_is_defined_prop; eauto; [|done].
    by destruct (lookupALExt olc2 lc2 z).
Qed.
Hint Resolve infrule_correct_stash_variable: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
