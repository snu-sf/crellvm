Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.
Require Import opsem.

Require Import sflib.
Require Import paco.
Import Opsem.

Require Import TODO.
Require Import Validator.
Require Import GenericValues.
Require AssnMem.
Require AssnState.
Require Import SoundBase.
Require Import TODOProof.
Require Import SoundInfruleIntroGhost.
Require Import SoundInfruleSubstitute.
Require Import SoundInfruleTransitivity.
Require Import SoundInfruleReduceMaydiff.
Require Import Exprs.

Set Implicit Arguments.

Lemma apply_not_interesting_infrule_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 assnmem0 inv0
      infrule
      (INTEREST: Hints.Infrule.is_of_interest infrule = false)
      (CONF: AssnState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 assnmem0 inv0)
      (MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem0):
  exists invst1 assnmem1,
    <<STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 assnmem1
                              (Infrules.apply_infrule m_src m_tgt infrule inv0)>> /\
    <<MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem1>> /\
    <<MEMLE: AssnMem.Rel.le assnmem0 assnmem1>>.
Proof.
  ADMIT "We will not prove the soundness of arithmetic infrules as Alive (SMT solver) can prove them.
Also, we will not prove the soundness of infrules that are only used inside instcombine pass.".
Qed.

Lemma apply_interesting_infrule_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 assnmem0 inv0
      infrule
      (INTEREST: Hints.Infrule.is_of_interest infrule = true)
      (CONF: AssnState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 assnmem0 inv0)
      (MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem0):
  exists invst1 assnmem1,
    <<STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 assnmem1
                              (Infrules.apply_infrule m_src m_tgt infrule inv0)>> /\
    <<MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem1>> /\
    <<MEMLE: AssnMem.Rel.le assnmem0 assnmem1>>.
Proof.
  destruct infrule; compute in INTEREST; try (by contradict INTEREST).
  - (* transitivity *)
    exists invst0, assnmem0. splits; eauto; [|reflexivity].
    ss.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c eqn:C
    end; ss.
    inv STATE. econs; eauto. ss. clear TGT MAYDIFF ALLOCAS.
    econs; try apply SRC; eauto; ss.
    red. i. apply Exprs.ExprPairSetFacts.add_iff in H.
    des; cycle 1.
    { eapply SRC; eauto. }
    destruct x; ss. clarify.
    rename t into __e0__.
    rename e2 into __e1__.
    rename t0 into __e2__.
    des_bool; des.
    abstr (AssnState.Rel.src invst0) invst.
    clear MEM CONF. clear_tac.
    solve_leibniz. clarify.
    assert(LD01: AssnState.Unary.sem_lessdef conf_src st_src invst (__e0__, __e1__)).
    { clear C0. repeat (des_bool; des).
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
    }
    assert(LD12: AssnState.Unary.sem_lessdef conf_src st_src invst (__e1__, __e2__)).
    { clear C. repeat (des_bool; des).
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
    }
    eapply AssnState.Unary.sem_lessdef_trans; eauto.
  - (* transitivity_tgt *)
    exists invst0, assnmem0.
    esplits; eauto; [ | reflexivity ].
    ss.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c eqn:C
    end; ss.
    econs; eauto; try apply STATE. ss.
    inv STATE. clear - TGT C.
    des_bool; des.
    abstr (AssnState.Rel.tgt invst0) invst.
    econs; try apply TGT; eauto; ss.
    red. i. apply Exprs.ExprPairSetFacts.add_iff in H.
    des; cycle 1.
    { eapply TGT; eauto. }
    destruct x; ss. clarify.
    rename t into __e0__.
    rename e2 into __e1__.
    rename t0 into __e2__.
    solve_leibniz. clarify.
    assert(LD01: AssnState.Unary.sem_lessdef conf_tgt st_tgt invst (__e0__, __e1__)).
    { clear C0. repeat (des_bool; des).
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
    }
    assert(LD12: AssnState.Unary.sem_lessdef conf_tgt st_tgt invst (__e1__, __e2__)).
    { clear C. repeat (des_bool; des).
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply AssnState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
    }
    eapply AssnState.Unary.sem_lessdef_trans; eauto.
  - (* substitute *)
    exists invst0, assnmem0.
    esplits; eauto; [ | reflexivity ].
    ss. des_ifs.
    econs; eauto; try apply STATE.
    hexploit AssnState.Rel.lessdef_expr_spec2; eauto; try apply STATE.
    intro LD; des. clear Heq.
    inv STATE. clear - SRC LD.
    eapply substitute_spec_unary; eauto.
  - (* substitute_rev *)
    exists invst0, assnmem0.
    esplits; eauto; [ | reflexivity ].
    ss. des_ifs.
    econs; eauto; try apply STATE.
    hexploit AssnState.Rel.lessdef_expr_spec2; eauto; try apply STATE.
    intro LD; des. clear Heq.
    inv STATE. clear - SRC LD.
    eapply substitute_spec_unary_rev; eauto.
  - (* substitute_tgt *)
    exists invst0, assnmem0.
    esplits; eauto; [ | reflexivity ].
    ss. des_ifs.
    econs; eauto; try apply STATE.
    hexploit AssnState.Rel.lessdef_expr_spec2; eauto; try apply STATE.
    intro LD; des. clear Heq.
    inv STATE. clear - TGT LD.
    eapply substitute_spec_unary; eauto.
  - (* intro_ghost *)
    ss. des_ifs; cycle 1.
    { esplits; eauto. reflexivity. }
    repeat (des_bool; des).
    rename g into i0.
    rename x into x0.
    Local Opaque AssnState.Unary.clear_idt.
    destruct (AssnState.Unary.sem_expr conf_src st_src
                                      (AssnState.Rel.clear_idt (Exprs.Tag.ghost, i0) invst0).(AssnState.Rel.src) x0) eqn:T0; cycle 1.
    {
      exists (AssnState.Rel.clear_idt (Exprs.Tag.ghost, i0) invst0), assnmem0.
      splits; ss; eauto; [|reflexivity].
      exploit clear_idt_ghost_spec; eauto.
      { instantiate (1:= (Exprs.Tag.ghost, i0)). ss. }
      intro STATE_CLEAR; des.
      clear - STATE_CLEAR T0.
      unfold Hints.Assertion.update_tgt, Hints.Assertion.update_src, Hints.Assertion.update_lessdef. ss.
      econs; eauto; try apply STATE_CLEAR.
      + ss.
        inv STATE_CLEAR. clear - SRC T0.

        econs; eauto; try apply SRC.
        ss.
        inv SRC. clear - LESSDEF T0.

        ii.
        apply Exprs.ExprPairSetFacts.add_iff in H. des.
        * solve_leibniz. clarify. ss. rewrite T0 in *. clarify.
        * eapply LESSDEF; eauto.
      + ss.
        inv STATE_CLEAR. clear - TGT T0.

        econs; eauto; try apply TGT.
        ss.
        inv TGT. clear - LESSDEF T0.

        ii.
        apply Exprs.ExprPairSetFacts.add_iff in H. des.
        * clarify. ss.
          assert(NONE: AssnState.Unary.sem_idT
                         st_tgt (AssnState.Rel.tgt
                                   (AssnState.Rel.clear_idt
                                      (Exprs.Tag.ghost, i0) invst0)) (Exprs.Tag.ghost, i0) = None).
          { clear - i0.
            unfold AssnState.Unary.sem_idT. ss.
            ss.
            Local Transparent AssnState.Unary.clear_idt. ss.
            rewrite lookup_AL_filter_spec. des_ifs. des_bool; des_sumbool. ss.
            Local Opaque AssnState.Unary.clear_idt.
          }
          unfold AssnState.Rel.clear_idt in *. ss.
          solve_leibniz. clarify. ss.
          rewrite NONE in *. clarify.
        * ss. eapply LESSDEF; eauto.
    }
    rename T0 into GV_SRC.
    rename g into gv_src.
    assert(GV_TGT: exists gv_tgt,
              AssnState.Unary.sem_expr conf_tgt st_tgt
                                      (AssnState.Rel.clear_idt (Exprs.Tag.ghost, i0) invst0).(AssnState.Rel.tgt) x0
              = Some gv_tgt
              /\ genericvalues_inject.gv_inject assnmem0.(AssnMem.Rel.inject) gv_src gv_tgt).
    {
      hexploit AssnState.Rel.not_in_maydiff_expr_spec; try apply GV_SRC; try apply STATE; eauto.
      { ii.
        assert(id0 <> (Exprs.Tag.ghost, i0)).
        {
          ii. clarify. ss.
          exploit clear_idt_inv_spec_id; try eassumption; ss.
          i. unfold proj_sumbool in *. des_ifs.
        }
        ss.
        erewrite <- clear_idt_spec_id; ss; cycle 1.
        { unfold proj_sumbool. des_ifs. }
        inv STATE.
        eapply MAYDIFF; ss.
        erewrite clear_idt_spec_id; try eassumption; cycle 1.
        unfold proj_sumbool. des_ifs.
      }
    }
    des. rename GV_TGT0 into GV_INJ.
    des.

    exploit clear_idt_ghost_spec; eauto.
    { instantiate (1:= (Exprs.Tag.ghost, i0)). ss. }
    intro STATE_CLEAR; des.
    clear - STATE_CLEAR GV_SRC GV_TGT GV_INJ MEM.

    exists (cons_idt (Exprs.Tag.ghost, i0) gv_src gv_tgt
                 (AssnState.Rel.clear_idt (Exprs.Tag.ghost, i0) invst0)), assnmem0.
    splits; ss; eauto; [|reflexivity].
    {
      econs; eauto; try apply STATE_CLEAR.
      - ss.
        eapply Subset_unary_sem; eauto.
        eapply cons_ghost_unary_spec; try apply STATE_CLEAR; eauto.
        { eapply sem_expr_preserves_valid_ptr; try apply STATE_CLEAR; try apply MEM; eauto. }
        unfold compose.
        econs; ss; eauto.
        + ii. apply Exprs.ExprPairSetFacts.add_iff. right. ss.
        + split; ss.
      - ss.
        eapply Subset_unary_sem; eauto.
        eapply cons_ghost_unary_spec; try apply STATE_CLEAR; eauto.
        { eapply sem_expr_preserves_valid_ptr; try apply STATE_CLEAR; try apply MEM; eauto. }
        unfold compose.
        econs; ss; eauto.
        + ii.
          apply Exprs.ExprPairSetFacts.add_iff in H. des.
          { apply Exprs.ExprPairSetFacts.add_iff. left. ss. }
          apply Exprs.ExprPairSetFacts.add_iff. right.
          apply Exprs.ExprPairSetFacts.add_iff. right. ss.
        + split; ss.
      - i.
        unfold Hints.Assertion.update_lessdef in NOTIN. ss.
        inv STATE_CLEAR.
        clear SRC TGT TGT_NOUNIQ ALLOCAS.
        ii. ss.
        destruct (Exprs.IdT.eq_dec id0 (Exprs.Tag.ghost, i0)).
        { clarify.
          unfold AssnState.Unary.sem_idT in *. ss. des_ifs.
          esplits; eauto.
        }
        erewrite <- cons_idt_spec_id in VAL_SRC; cycle 1.
        { unfold proj_sumbool; des_ifs. }
        erewrite <- cons_idt_spec_id; cycle 1.
        { unfold proj_sumbool; des_ifs. }
        eapply MAYDIFF; eauto.
    }
  - (* intro_eq_tgt *)
    exists invst0, assnmem0. splits; eauto; [|reflexivity].
    inv STATE. econs; eauto. ss.
    inv TGT. econs; eauto. ss.
    ii. apply Exprs.ExprPairSetFacts.add_iff in H. des.
    + subst. solve_leibniz. clarify. esplits; eauto. apply GVs.lessdef_refl.
    + eapply LESSDEF; eauto.
  - exploit reduce_maydiff_lessdef_sound; eauto. i.
    esplits; eauto. reflexivity.
  - exploit reduce_maydiff_non_physical_sound; eauto. i. des.
    esplits; eauto. reflexivity.
Qed.


Lemma apply_infrule_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 assnmem0 inv0
      infrule
      (CONF: AssnState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 assnmem0 inv0)
      (MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem0):
  exists invst1 assnmem1,
    <<STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 assnmem1
                              (Infrules.apply_infrule m_src m_tgt infrule inv0)>> /\
    <<MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem1>> /\
    <<MEMLE: AssnMem.Rel.le assnmem0 assnmem1>>.
Proof.
  destruct (Hints.Infrule.is_of_interest infrule) eqn:T; ss.
  - eapply apply_interesting_infrule_sound; eauto.
  - eapply apply_not_interesting_infrule_sound; eauto.
Qed.

Lemma apply_infrules_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 assnmem0 inv0
      infrules
      (CONF: AssnState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 assnmem0 inv0)
      (MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem0):
  exists invst1 assnmem1,
    <<STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 assnmem1
                              (Infrules.apply_infrules m_src m_tgt infrules inv0)>> /\
    <<MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem1>> /\
    <<MEMLE: AssnMem.Rel.le assnmem0 assnmem1>>.
Proof.
  unfold Infrules.apply_infrules. rewrite <- fold_left_rev_right.
  move infrules at top. revert_until infrules. induction (rev infrules); i.
  - esplits; eauto. reflexivity.
  - exploit IHl0; eauto. i. des.
    exploit apply_infrule_sound; eauto. i. des.
    esplits; eauto.
    etransitivity; eauto.
Qed.
