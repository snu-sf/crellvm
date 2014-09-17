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

Lemma infrule_correct_eq_generate_same_heap:
  forall m1 m2 x y p t a, infrule_prop m1 m2 (rule_eq_generate_same_heap x y p t a).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Heq; infrule_tac.
  destruct Heq; infrule_tac.
  generalize dependent H.
  generalize dependent H0.
  unfold eq_heap_sem.
  remember (getOperandValueExt (CurTargetData cfg1) p olc1 lc1 (Globals cfg1)) as gp; destruct gp as [gp|]; [|done].
  remember (getOperandValueExt (CurTargetData cfg1) (value_ext_id y) olc1 lc1 (Globals cfg1)) as gy; destruct gy as [gy|]; [|done].
  remember (getOperandValueExt (CurTargetData cfg1) (value_ext_id lhs) olc1 lc1 (Globals cfg1)) as glhs; destruct glhs as [glhs|]; [|done].
  intros Hy Hlhs.
  exploit (Hlhs gp); eauto.
  exploit (Hy gp); eauto.
  destruct (mload (CurTargetData cfg1) mem1 gp t a); [|done].
  intros; infrule_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  by constructor; symmetry.
Qed.
Hint Resolve infrule_correct_eq_generate_same_heap: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
