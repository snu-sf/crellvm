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

Lemma infrule_correct_rem_neg:
  forall m1 m2 z my sz x y, infrule_prop m1 m2 (rule_rem_neg z my sz x y).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  generalize dependent H5.
  generalize dependent H4.
  clear -Hlookup Hlookup0.

  unfold BOPEXT; simpl.
  rewrite Hlookup0.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    destruct (getOperandValueExt (CurTargetData cfg1) y olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  - by contradict n; omega.
  - rewrite Int.sub_zero_r in e1.
    symmetry in e1.
    exploit Int_neg_eq; eauto.
    intro H; rewrite Int.neg_zero in H.
    by contradict n; rewrite <- H.
  - rewrite Int.sub_zero_r.
    by rewrite Int_mods_neg.
  - destruct sz0; [by destruct wz0|].
    by contradict n; omega.
Qed.
Hint Resolve infrule_correct_rem_neg: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
