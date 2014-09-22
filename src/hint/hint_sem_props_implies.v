Require Import vgtac.

Require Import vellvm.
Require Import program_sim.

Require Import syntax_ext.
Require Import validator_aux.
Require Import validator_props.
Require Import logical_step.
Require Import state_props.
Require Import hints.
Require Import hint_sem.
Require Import syntax_ext.

Import Opsem.

Lemma eqs_implies_prop
  cfg olc lc mem gmax eqs1 eqs2
  (H1: eqs_sem cfg olc lc mem gmax eqs1)
  (Himplies: eqs_implies eqs1 eqs2) :
  eqs_sem cfg olc lc mem gmax eqs2.
Proof.
  unfold eqs_implies in Himplies; infrule_tac.
  destruct H1 as [H11 [H12 H13]].
  apply EqRegSetFacts.subset_iff in H.
  apply EqHeapSetFacts.subset_iff in H2.
  apply NeqRegSetFacts.subset_iff in H0.
  unfold eqs_sem; repeat split.
  - intros lhs rhs Heq.
    apply EqRegSetFacts.mem_iff in Heq.
    apply H in Heq.
    apply H11.
    by apply EqRegSetFacts.mem_iff in Heq.
  - intros lhs tt aa rhs Heq.
    apply EqHeapSetFacts.mem_iff in Heq.
    apply H2 in Heq.
    apply H12.
    by apply EqHeapSetFacts.mem_iff in Heq.
  - intros lhs rhs Heq.
    apply NeqRegSetFacts.mem_iff in Heq.
    apply H0 in Heq.
    apply H13.
    by apply NeqRegSetFacts.mem_iff in Heq.
Qed.

Lemma iso_implies_prop
  td olc lc li iso iso'
  (H1: isolated_sem td olc lc li iso)
  (Himplies: iso_implies iso iso') :
  isolated_sem td olc lc li iso'.
Proof.
  unfold iso_implies in Himplies; infrule_tac.
  unfold isolated_sem, IdExtSetImpl.For_all in *; intros.
  exploit H1; eauto.
  apply IdExtSetFacts.subset_iff in Himplies.
  apply Himplies; eauto.
Qed.

Lemma invariant_implies_preserves_hint_sem_fdef :
  forall hint nhint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
    alpha z cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2
    (Hsim: hint_sem_insn hint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha z cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2)
    (Himp: invariant_implies hint nhint),
    hint_sem_insn nhint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
    alpha z cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2.
Proof.
  intros.
  unfold invariant_implies in Himp; infrule_tac.
  unfold maydiff_implies in H.
  inv Hsim.
  destruct Hsem as [olc1 [olc2 [Hmd Hsem]]].
  constructor; auto.
  exists olc1; exists olc2; split.
  - intro var.
    generalize (Hmd var); clear Hmd; intros Hmd Hvar.
    apply Hmd.
    apply IdExtSetFacts.not_mem_iff in Hvar.
    apply IdExtSetFacts.not_mem_iff.
    intro Hvar2; apply Hvar.
    apply IdExtSetFacts.subset_iff in H.
    by apply H.
  - unfold hint_invariant_implies in H0; infrule_tac.
    destruct Hsem as [Hinv1 [Hinv2 [Hiso1 Hiso2]]]; rr; splits.
    by eapply eqs_implies_prop; eauto.
    by eapply eqs_implies_prop; eauto.
    by eapply iso_implies_prop; eauto.
    by eapply iso_implies_prop; eauto.
Qed.

(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
