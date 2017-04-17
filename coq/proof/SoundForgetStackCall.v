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
Require Import TODOProof.
Require Import Hints.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.
Require Import SoundForgetStack.

Set Implicit Arguments.


Lemma forget_stack_call_Subset inv defs_src defs_tgt
  : Hints.Invariant.Subset (ForgetStackCall.t defs_src defs_tgt inv) inv.
Proof.
  unfold ForgetStackCall.t.
  apply forget_stack_Subset.
Qed.

Lemma invst_sem_eq_locals_mem
      st0_src st1_src conf_src
      st0_tgt st1_tgt conf_tgt
      invst invmem inv
      (MEM_SRC: st0_src.(Mem) = st1_src.(Mem))
      (MEM_TGT: st0_tgt.(Mem) = st1_tgt.(Mem))
      (LOCAL_SRC: st0_src.(EC).(Locals) = st1_src.(EC).(Locals))
      (LOCAL_TGT: st0_tgt.(EC).(Locals) = st1_tgt.(EC).(Locals))
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst invmem inv)
      (EQ_BB_SRC: st0_src.(EC).(CurBB) = st1_src.(EC).(CurBB))
      (EQ_BB_TGT: st0_tgt.(EC).(CurBB) = st1_tgt.(EC).(CurBB))
      (EQ_FUNC_SRC: st0_src.(EC).(CurFunction) = st1_src.(EC).(CurFunction))
      (EQ_FUNC_TGT: st0_tgt.(EC).(CurFunction) = st1_tgt.(EC).(CurFunction))
  : InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst invmem inv.
Proof.
  inv STATE.
  econs.
  - eapply unary_sem_eq_locals_mem; eauto.
  - eapply unary_sem_eq_locals_mem; eauto.
  - i. hexploit MAYDIFF; eauto. i.
    ii. exploit H.
    { erewrite sem_idT_eq_locals; eauto. }
    i. erewrite sem_idT_eq_locals; eauto.
Qed.

Lemma genericvalues_inject_simulation__GV2ptr_tgt:
  forall (mi : Values.meminj) (TD : TargetData) (gv1 gv1' : GenericValue) (v' : Values.val),
    genericvalues_inject.gv_inject mi gv1 gv1' ->
    GV2ptr TD (getPointerSize TD) gv1' = Some v' ->
    exists v : Values.val, GV2ptr TD (getPointerSize TD) gv1 = Some v /\ memory_sim.MoreMem.val_inject mi v v'.
Proof.
  i. exploit external_intrinsics.GV2ptr_inv; eauto. i. des.
  subst. inv H. inv H4. ss.
  inv H6. esplits; eauto.
Qed.

Lemma genericvalues_inject_wf_valid_ptrs_src
      invmem
      mem_src gv_src
      mem_tgt gv_tgt
      (INJ_FIT : genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gv_src gv_tgt)
      (WF : genericvalues_inject.wf_sb_mi invmem.(InvMem.Rel.gmax) invmem.(InvMem.Rel.inject) mem_src mem_tgt)
  : memory_props.MemProps.valid_ptrs (Memory.Mem.nextblock mem_src) gv_src.
Proof.
  generalize dependent gv_tgt.
  inv WF.
  induction gv_src; i; ss.
  des_ifs; inv INJ_FIT;
    try by eapply IHgv_src; eauto.
  inv H3.
  split; eauto.
  destruct (dom_libs.PositiveSet.MSet.Raw.MX.lt_dec b (Memory.Mem.nextblock mem_src)); ss.
  rewrite <- Pos.le_nlt in n.
  exploit Hmap1.
  { apply Pos.le_ge. eauto. }
  i. congruence.
Qed.

Lemma genericvalues_inject_wf_valid_ptrs_tgt
      invmem
      mem_src gv_src
      mem_tgt gv_tgt
      (INJ_FIT : genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gv_src gv_tgt)
      (WF : genericvalues_inject.wf_sb_mi invmem.(InvMem.Rel.gmax) invmem.(InvMem.Rel.inject) mem_src mem_tgt)
  : memory_props.MemProps.valid_ptrs (Memory.Mem.nextblock mem_tgt) gv_tgt.
Proof.
  generalize dependent gv_src.
  inv WF.
  induction gv_tgt; i; ss.
  des_ifs; inv INJ_FIT;
    try by eapply IHgv_tgt; eauto.
  inv H2.
  split; eauto.
Qed.

Lemma gv_inject_public_src
      gv_src gv_tgt meminj b
          (INJECT: genericvalues_inject.gv_inject meminj gv_src gv_tgt)
          (IN: In b (GV2blocks gv_src))
      :
        <<PUBLIC: InvMem.Rel.public_src meminj b>>
.
Proof.
  induction INJECT; ii; ss; des; ss.
  - eapply GV2blocks_In_cons in IN.
    des.
    + destruct v1; ss. des; ss. subst.
      inv H.
      clarify.
    + exploit IHINJECT; eauto.
Qed.

Lemma gv_inject_public_tgt
      gv_src gv_tgt meminj b
          (INJECT: genericvalues_inject.gv_inject meminj gv_src gv_tgt)
          (IN: In b (GV2blocks gv_tgt))
      :
        <<PUBLIC: InvMem.Rel.public_tgt meminj b>>
.
Proof.
  induction INJECT; ii; ss; des; ss.
  - eapply GV2blocks_In_cons in IN.
    des.
    + destruct v2; ss. des; ss. subst.
      inv H.
      unfold InvMem.Rel.public_tgt.
      esplits; eauto.
    + exploit IHINJECT; eauto.
Qed.


(* TODO: position *)
Lemma gv_inject_no_private
      conf_src st_src gv_src
      conf_tgt st_tgt gv_tgt
      invst invmem inv
      (STATE : InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM : InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
      (INJECT: genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) gv_src gv_tgt)
  : <<DIFF_FROM_PRIVATE_SRC:
    forall p_src gv_p_src
      (PRIVATE_SRC: Exprs.IdTSet.mem p_src inv.(Invariant.src).(Invariant.private) = true)
      (P_SRC_SEM: InvState.Unary.sem_idT st_src invst.(InvState.Rel.src) p_src = Some gv_p_src),
      InvState.Unary.sem_diffblock conf_src gv_p_src gv_src>> /\
    <<DIFF_FROM_PRIVATE_TGT:
    forall p_tgt gv_p_tgt
      (PRIVATE_TGT: Exprs.IdTSet.mem p_tgt inv.(Invariant.tgt).(Invariant.private) = true)
      (P_TGT_SEM: InvState.Unary.sem_idT st_tgt invst.(InvState.Rel.tgt) p_tgt = Some gv_p_tgt),
      InvState.Unary.sem_diffblock conf_tgt gv_p_tgt gv_tgt>>.
Proof.
  inv STATE. rename SRC into STATE_SRC. rename TGT into STATE_TGT. clear MAYDIFF.
  clear MEM.
  split; ii.
  - clear STATE_TGT.
    inv STATE_SRC.
    clear LESSDEF NOALIAS UNIQUE
          WF_LOCAL WF_PREVIOUS WF_GHOST UNIQUE_PARENT_LOCAL.

    exploit PRIVATE; eauto.
    { apply Exprs.IdTSetFacts.mem_iff. eauto. }
    intro PRIV_IN_MEM. des. (* clear PARENT_DISJOINT. *)
    {
      eapply PRIVATE; eauto.
      eapply Exprs.IdTSetFacts.mem_iff; eauto.
      unfold InvMem.private_block in *. des.
      hexploit gv_inject_public_src; eauto; []; intro PUB; des.
      clear - PUB PRIVATE_BLOCK. ss.
    }
  - clear STATE_SRC.
    inv STATE_TGT.
    clear LESSDEF NOALIAS UNIQUE
          WF_LOCAL WF_PREVIOUS WF_GHOST UNIQUE_PARENT_LOCAL.

    exploit PRIVATE; eauto.
    { apply Exprs.IdTSetFacts.mem_iff. eauto. }
    intro PRIV_IN_MEM. des. clear PARENT_DISJOINT.
    {
      eapply PRIVATE; eauto.
      eapply Exprs.IdTSetFacts.mem_iff; eauto.
      unfold InvMem.private_block in *. des.
      hexploit gv_inject_public_tgt; eauto; []; intro PUB; des.
      clear - PUB PRIVATE_BLOCK. ss.
    }
Qed.

(* we need additional condition: all unique in inv1 is private, so not in inject: not in return value *)
Lemma forget_stack_call_sound
      invst2 invmem2 inv1 noret typ
      mem1_src conf_src retval1_src st0_src id_src cmds_src locals1_src
      mem1_tgt conf_tgt retval1_tgt st0_tgt id_tgt cmds_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (STATE:
         InvState.Rel.sem
           conf_src conf_tgt
           (mkState st0_src.(EC) st0_src.(ECS) mem1_src)
           (mkState st0_tgt.(EC) st0_tgt.(ECS) mem1_tgt)
           invst2 invmem2 inv1)
      (UNIQUE_PRIVATE_SRC: unique_is_private_unary inv1.(Invariant.src))
      (UNIQUE_PRIVATE_TGT: unique_is_private_unary inv1.(Invariant.tgt))
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem2)
      (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject invmem2.(InvMem.Rel.inject)) retval1_src retval1_tgt)
      (RETURN_SRC: return_locals
                     conf_src.(CurTargetData)
                                retval1_src id_src noret typ
                                st0_src.(EC).(Locals)
                   = Some locals1_src)
  : exists locals2_tgt,
        <<RETURN_TGT: return_locals
                        conf_tgt.(CurTargetData)
                        retval1_tgt id_tgt noret typ
                        st0_tgt.(EC).(Locals)
                      = Some locals2_tgt>> /\
        <<STATE:
          InvState.Rel.sem
            conf_src conf_tgt
            (mkState (mkEC st0_src.(EC).(CurFunction)
                           st0_src.(EC).(CurBB)
                           cmds_src
                           st0_src.(EC).(Terminator)
                           locals1_src
                           st0_src.(EC).(Allocas))
                     st0_src.(ECS) mem1_src)
            (mkState (mkEC st0_tgt.(EC).(CurFunction)
                           st0_tgt.(EC).(CurBB)
                           cmds_tgt
                           st0_tgt.(EC).(Terminator)
                           locals2_tgt
                           st0_tgt.(EC).(Allocas))
                     st0_tgt.(ECS) mem1_tgt)
            invst2 invmem2 (ForgetStackCall.t
                              (AtomSetImpl_from_list (ite noret None (Some id_src)))
                              (AtomSetImpl_from_list (ite noret None (Some id_tgt)))
                              inv1)>>.
Proof.
  unfold return_locals in *.
  destruct retval1_src; destruct retval1_tgt; ss.
  rename g into rgv_src. rename g0 into rgv_tgt.
  { (* some - some *)
    destruct noret.
    { esplits; eauto. clarify. ss.
      eapply Subset_sem.
      eapply invst_sem_eq_locals_mem; try exact STATE; eauto.
      apply forget_stack_call_Subset.
    }
    des_ifs.
    - rename g0 into rgv_fit_src. rename g into rgv_fit_tgt.
      hexploit genericvalues_inject.simulation__fit_gv; eauto.
      { inv MEM. eauto. }
      intro FIT_GV. destruct FIT_GV as [rgv_fit_tgt' [FIT_GV_TGT INJ_FIT]].
      inv CONF. rewrite TARGETDATA in *.
      clarify.
      esplits; eauto.

      exploit gv_inject_no_private; eauto. intros DIFF_FROM_PRIVATE. des.

      unfold ForgetStackCall.t.
      eapply forget_stack_sound; eauto.
      { econs; eauto.
        ss. ii.
        apply AtomSetImpl_singleton_mem_false in NOT_MEM.
        erewrite <- lookupAL_updateAddAL_neq; eauto.
      }
      { econs; eauto.
        ss. ii.
        apply AtomSetImpl_singleton_mem_false in NOT_MEM.
        erewrite <- lookupAL_updateAddAL_neq; eauto.
      }

      { inv STATE. inv SRC.
        inv MEM. inv SRC.
        econs; eauto; ss.
        - i.
          rewrite AtomSetProperties.empty_union_2 in *; ss.
          apply AtomSetImpl_singleton_mem_false in NO_LEAK.
          exploit UNIQUE.
          { apply AtomSetFacts.mem_iff; eauto. }
          intro UNIQUE_PREV. inv UNIQUE_PREV.
          econs; eauto; ss.
          + rewrite <- lookupAL_updateAddAL_neq; eauto.
          + i.
            destruct (id_dec reg id_src); cycle 1.
            * rewrite <- lookupAL_updateAddAL_neq in VAL'; eauto.
            * subst.
              rewrite lookupAL_updateAddAL_eq in VAL'. clarify.
              eapply DIFF_FROM_PRIVATE_SRC; eauto.
        - ii.
          destruct (id_dec id_src x).
          { subst.
            rewrite lookupAL_updateAddAL_eq in PTR. clarify.
            des.
            eapply sublist_In in UNIQUE_PRIVATE_PARENT; eauto.
            exploit PRIVATE_PARENT; eauto. intros [NOT_PUBLIC _].
            apply NOT_PUBLIC.
            eapply gv_inject_public_src; eauto.
          }
          { erewrite <- lookupAL_updateAddAL_neq in PTR; eauto.
            exploit UNIQUE_PARENT_LOCAL; eauto. }
      }
      { inv STATE. inv TGT.
        inv MEM. inv TGT.
              
        econs; eauto; ss.
        - i.
          rewrite AtomSetProperties.empty_union_2 in *; ss.
          apply AtomSetImpl_singleton_mem_false in NO_LEAK.
          exploit UNIQUE.
          { apply AtomSetFacts.mem_iff; eauto. }
          intro UNIQUE_PREV. inv UNIQUE_PREV.
          econs; eauto; ss.
          + rewrite <- lookupAL_updateAddAL_neq; eauto.
          + i.
            destruct (id_dec reg id_tgt); cycle 1.
            * rewrite <- lookupAL_updateAddAL_neq in VAL'; eauto.
            * subst.
              rewrite lookupAL_updateAddAL_eq in VAL'. clarify.
              eapply DIFF_FROM_PRIVATE_TGT; eauto.
        - ii.
          destruct (id_dec id_tgt x).
          { subst.
            rewrite lookupAL_updateAddAL_eq in PTR. clarify.
            des.
            eapply sublist_In in UNIQUE_PRIVATE_PARENT; eauto.
            exploit PRIVATE_PARENT; eauto. intros [NOT_PUBLIC _].
            apply NOT_PUBLIC.
            eapply gv_inject_public_tgt; eauto.
          }
          { erewrite <- lookupAL_updateAddAL_neq in PTR; eauto.
            exploit UNIQUE_PARENT_LOCAL; eauto. }
      }
      { ss. inv STATE. inv SRC. ss.
        apply memory_props.MemProps.updateAddAL__wf_lc; eauto.
        inv MEM.
        exploit genericvalues_inject_wf_valid_ptrs_src; eauto.
      }
      { ss. inv STATE. inv TGT. ss.
        apply memory_props.MemProps.updateAddAL__wf_lc; eauto.
        inv MEM.
        exploit genericvalues_inject_wf_valid_ptrs_tgt; eauto.
      }
    - hexploit genericvalues_inject.simulation__fit_gv; eauto.
      { inv MEM. eauto. }
      i. des.
      inv CONF. rewrite TARGETDATA in *.
      congruence.
  }
  { (* none - none *)
    esplits; des_ifs; ss.
    unfold AtomSetImpl_from_list. ss.
    eapply Subset_sem; cycle 1.
    { unfold ForgetStackCall.t.
      apply forget_stack_Subset. }
    eapply invst_sem_eq_locals_mem; try exact STATE; eauto.
  }
Qed.
