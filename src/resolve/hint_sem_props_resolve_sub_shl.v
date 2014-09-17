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

Lemma infrule_correct_sub_shl:
  forall m1 m2 z x y sz mx a, infrule_prop m1 m2 (rule_sub_shl z x y sz mx a).
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
  destruct (getOperandValueExt (CurTargetData cfg1) mx olc1 lc1 (Globals cfg1));
    destruct (getOperandValueExt (CurTargetData cfg1) a olc1 lc1 (Globals cfg1));
    infrule_tac.
  repeat
    (arith_tac;
      try match goal with
            | [|- context[Int.ltu ?s ?a ?b]] =>
              destruct (Int.ltu s a b); [|done]
            | [H: context[GV2val _ (val2GV _ _ _)] |- _] =>
              rewrite GV2val_val2GV' in H; [|done]
          end).
  - by contradict n; omega.
  - by apply Int_shl_neg.
  - by contradict n; omega.  
Qed.
Hint Resolve infrule_correct_sub_shl: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
