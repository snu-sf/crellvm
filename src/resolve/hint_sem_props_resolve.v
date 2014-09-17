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

Require Import hint_sem_props_resolve_add_assoc.
Require Import hint_sem_props_resolve_replace_rhs.
Require Import hint_sem_props_resolve_replace_rhs_opt.
Require Import hint_sem_props_resolve_replace_lhs.
Require Import hint_sem_props_resolve_remove_maydiff.
Require Import hint_sem_props_resolve_remove_maydiff_rhs.
Require Import hint_sem_props_resolve_eq_generate_same.
Require Import hint_sem_props_resolve_eq_generate_same_heap.
Require Import hint_sem_props_resolve_add_signbit.
Require Import hint_sem_props_resolve_add_zext_bool.
Require Import hint_sem_props_resolve_ptr_trans.
Require Import hint_sem_props_resolve_add_onebit.
Require Import hint_sem_props_resolve_stash_variable.
Require Import hint_sem_props_resolve_add_shift.
Require Import hint_sem_props_resolve_add_sub.
Require Import hint_sem_props_resolve_add_commutative.
Require Import hint_sem_props_resolve_sub_add.
Require Import hint_sem_props_resolve_sub_onebit.
Require Import hint_sem_props_resolve_sub_mone.
Require Import hint_sem_props_resolve_sub_const_not.
Require Import hint_sem_props_resolve_add_mul_fold.
Require Import hint_sem_props_resolve_add_const_not.
Require Import hint_sem_props_resolve_add_select_zero.
Require Import hint_sem_props_resolve_add_select_zero2.
Require Import hint_sem_props_resolve_sub_zext_bool.
Require Import hint_sem_props_resolve_sub_const_add.
Require Import hint_sem_props_resolve_sub_remove.
Require Import hint_sem_props_resolve_sub_remove2.
Require Import hint_sem_props_resolve_sub_sdiv.
Require Import hint_sem_props_resolve_sub_shl.
Require Import hint_sem_props_resolve_sub_mul.
Require Import hint_sem_props_resolve_sub_mul2.
Require Import hint_sem_props_resolve_mul_mone.
Require Import hint_sem_props_resolve_mul_neg.
Require Import hint_sem_props_resolve_mul_bool.
Require Import hint_sem_props_resolve_mul_commutative.
Require Import hint_sem_props_resolve_mul_shl.
Require Import hint_sem_props_resolve_div_sub_srem.
Require Import hint_sem_props_resolve_div_sub_urem.
Require Import hint_sem_props_resolve_div_zext.
Require Import hint_sem_props_resolve_div_mone.
Require Import hint_sem_props_resolve_rem_zext.
Require Import hint_sem_props_resolve_rem_neg.
Require Import hint_sem_props_resolve_rem_neg2.
Require Import hint_sem_props_resolve_select_trunc.
Require Import hint_sem_props_resolve_select_add.
Require Import hint_sem_props_resolve_select_const_gt.
Require Import hint_sem_props_resolve_or_xor.
Require Import hint_sem_props_resolve_or_commutative.
Require Import hint_sem_props_resolve_trunc_onebit.
Require Import hint_sem_props_resolve_cmp_onebit.
Require Import hint_sem_props_resolve_shift_undef.
Require Import hint_sem_props_resolve_and_same.
Require Import hint_sem_props_resolve_and_zero.
Require Import hint_sem_props_resolve_and_mone.
Require Import hint_sem_props_resolve_inbound_remove.
Require Import hint_sem_props_resolve_inbound_remove2.
Require Import hint_sem_props_resolve_eq_generate_same_heap_value.
Require Import hint_sem_props_resolve_add_mask.
Require Import hint_sem_props_resolve_cmp_ult.
Require Import hint_sem_props_resolve_cmp_eq.
Require Import hint_sem_props_resolve_neq_generate_gm.

Lemma infrules_correct: forall m1 m2 ir, infrule_prop m1 m2 ir.
Proof.
  i; destruct ir; try done; eauto with InfRuleDb.
Admitted.

Lemma infrule_resolve_preserves_hint_sem_fdef :
  forall hint infrule pecs1 pecs2 ptns1 ptns2 pi1 li1 pi2 li2
    maxb alpha cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2
    m1 m2 (Hmatch: matched_module_cfg m1 m2 cfg1 cfg2)
    (Hrule: forall m1 m2 ir, infrule_prop m1 m2 ir)
    (Hsim: hint_sem_insn hint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha maxb cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2),
    hint_sem_insn (infrule_resolve m1 m2 hint infrule) pecs1 pecs2 ptns1 ptns2
    pi1 pi2 li1 li2 alpha maxb cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2.
Proof.
  intros.
  unfold infrule_resolve.
  generalize (Hrule m1 m2 infrule); clear Hrule; intro Hrule.
  inv Hsim. constructor; auto.
  exploit Hrule; eauto.
  - by inv Hvmem; eauto.
  - by inv Hgequiv.
  - inv Hgequiv.
    by rewrite <- Hgl2.
Qed.

Lemma infrules_resolve_preserves_hint_sem_fdef :
  forall hint pecs1 pecs2 ptns1 ptns2 pi1 li1 pi2 li2
    alpha z cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2
    m1 m2 (Hmatch: matched_module_cfg m1 m2 cfg1 cfg2)
    (Hrule: forall ir, infrule_prop m1 m2 ir)
    (Hsim: hint_sem_insn hint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha z cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2),
    hint_sem_insn (infrules_resolve m1 m2 hint) pecs1 pecs2 ptns1 ptns2
    pi1 pi2 li1 li2 alpha z cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2.
Proof.
  intros.
  unfold infrules_resolve.
  rewrite <- fold_left_rev_right.
  induction (rev (hint_infrules hint)); [done|]; simpl.
  apply infrule_resolve_preserves_hint_sem_fdef; auto.
  by apply infrules_correct.
Qed.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
