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

Lemma infrule_correct_eq_generate_same_heap_value:
  forall m1 m2 x p v t a, infrule_prop m1 m2 (rule_eq_generate_same_heap_value x p v t a).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Heq; infrule_tac.
  destruct Heq; infrule_tac.
  generalize dependent H.
  generalize dependent H0.
  unfold eq_heap_sem.
  remember (getOperandValueExt (CurTargetData cfg1) p olc1 lc1 (Globals cfg1)) as gp; destruct gp as [gp|]; [|done].
  simpl.
  remember (getOperandValueExt (CurTargetData cfg1) v olc1 lc1 (Globals cfg1)) as gv; destruct gv as [gv|]; [|done].
  remember (lookupALExt olc1 lc1 lhs) as glhs; destruct glhs as [glhs|]; [|done].
  intros Hv Hlhs.
  exploit (Hlhs gp); eauto.
  exploit (Hv gp); eauto.
  destruct (mload (CurTargetData cfg1) mem1 gp t a); [|done].
  intros; infrule_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  by constructor; symmetry.
Qed.
Hint Resolve infrule_correct_eq_generate_same_heap_value: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
