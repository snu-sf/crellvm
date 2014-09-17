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

Lemma infrule_correct_select_const_gt:
  forall m1 m2 z b s x c1 c2, infrule_prop m1 m2 (rule_select_const_gt z b s x c1 c2).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intro var; infrule_tac.
  intro HH; destruct HH as [HH|HH]; [by apply Hmd|]; infrule_tac.
  inv H; inv H0; infrule_tac.
  unfold variable_equivalent.
  arith_tac.
  inv Hrhs. inv Hrhs2.
  admit. (* NOTE: impossible to prove due to incorrect semantics of undef in Vellvm *)
Qed.
Hint Resolve infrule_correct_select_const_gt: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
