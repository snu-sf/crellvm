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

Lemma infrule_correct_cmp_eq:
  forall m1 m2 z y a b, infrule_prop m1 m2 (rule_cmp_eq z y a b).
Proof.
  repeat intro; infrule_tac.
  infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  generalize dependent H4.
  generalize dependent H5.
  clear -Hlookup Hlookup0.
  
  unfold BOPEXT, ICMPEXT; simpl.
  rewrite Hlookup0.
  destruct (getOperandValueExt (CurTargetData cfg2) a olc2 lc2 (Globals cfg2));
    destruct (getOperandValueExt (CurTargetData cfg2) b olc2 lc2 (Globals cfg2));
    infrule_tac.
    arith_tac;
      repeat
        ((try unfold micmp_int in *);
         (try match goal with
               | [H: ret _ = ?a |- match ?a with ret _ => _ | merror => _ end = ret _] =>
                 rewrite <- H
             end)).
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - f_equal. f_equal.
    simpl. unfold Val.cmp_obligation_1. arith_tac.
    + rewrite Int.xor_idem, Int.xor_commut, Int.xor_zero.
      unfold INTEGER.to_Z, INTEGER.of_Z.
      unfold Vtrue, Vone, Values.one, Int.one.
      f_equal. apply Int.eqm_samerepr.
      unfold Int.eqm, Int.eqmod. unfold Int.modulus, two_power_nat, shift_nat; simpl.
      exists 1. omega.
    + destruct i0, i1.
      unfold Int.modulus, two_power_nat, shift_nat in intrange, intrange0; simpl in *.
      assert (intval = 0 \/ intval = 1); [omega|].
      assert (intval0 = 0 \/ intval0 = 1); [omega|].
      unfold Int.xor, Int.sub.
      unfold Int.bitwise_binop, xorb; simpl.
      destruct H; destruct H0; subst; simpl in *; try done.
      * by contradict n; apply Int.mkint_eq.
      * by contradict n; apply Int.mkint_eq.
  - elim n. unfold Size.to_nat, Size.One in e0. omega.
  - unfold Val.cmp.
    unfold Val.cmp_obligation_19.
    unfold Val.cmp_obligation_10.
    unfold Val.cmp_obligation_3.
    unfold Val.cmp_obligation_2.
    unfold Val.cmp_obligation_1.
    arith_tac.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - admit. (* NOTE: impossible to prove due to lack of type check *)
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
  - unfold gundef. unfold flatten_typ.
    by destruct cfg2; destruct CurTargetData0.
Qed.
Hint Resolve infrule_correct_cmp_eq: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
