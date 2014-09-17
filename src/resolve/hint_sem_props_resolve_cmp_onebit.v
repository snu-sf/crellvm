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
Require Import hint_sem_props_resolve_integers.

Lemma infrule_correct_cmp_onebit:
  forall m1 m2 z x y, infrule_prop m1 m2 (rule_cmp_onebit z x y).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; constructor.
  generalize dependent H4.
  clear.

  unfold ICMPEXT, BOPEXT; simpl.
  destruct (getOperandValueExt (CurTargetData cfg1) x olc1 lc1 (Globals cfg1));
    destruct (getOperandValueExt (CurTargetData cfg1) y olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac;
    intros;
    repeat
      (try
        match goal with
          | [H: ?a = ?b |- context[?b]] =>
            rewrite <- H
          | [|- context[flatten_typ ?td (typ_int _)]] =>
            destruct td
        end; unfold micmp_int, gundef in *; simpl; auto).

  - idtac.
    assert (wz0 = 0%nat); [|subst].
    + unfold Size.to_nat, Size.One in e.
      omega.
    unfold Val.cmp_obligation_3, Val.cmp_obligation_2, Val.cmp_obligation_1.
    arith_tac.
    + rewrite Int_0_xor_sub.
      by rewrite Int.sub_idem.
    + destruct i0, i1.
      unfold Int.modulus, two_power_nat, shift_nat, iter_nat in intrange, intrange0; simpl in *.
      assert (intval = 0 \/ intval = 1); [omega|].
      assert (intval0 = 0 \/ intval0 = 1); [omega|].
      destruct H, H0; subst; try done.
      * by contradict n; apply Int.mkint_eq.
      * by contradict n; apply Int.mkint_eq.
  - unfold Val.cmp_obligation_3, Val.cmp_obligation_2, Val.cmp_obligation_1.
    by arith_tac.
  - unfold Val.cmp_obligation_3, Val.cmp_obligation_2, Val.cmp_obligation_1.
    arith_tac.
    + rewrite <- Heqgg in H4.
      rewrite <- Heqgg0 in H4.
      unfold val2GV.
      admit. (* NOTE: impossible to prove due to lack of type check *)
    + rewrite <- Heqgg in H4.
      rewrite <- Heqgg0 in H4.
      unfold val2GV.
      admit. (* NOTE: impossible to prove due to lack of type check *)
Qed.
Hint Resolve infrule_correct_cmp_onebit: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
