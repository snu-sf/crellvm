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
Require Import Decs.
Require Import Hints.
Require Import Validator.
Require Import GenericValues.
Require Import TODOProof.
Require Import OpsemAux.
Require Import SimulationLocal.
Require Import Simulation.
Require Import Inject.
Require InvMem.
Require InvState.
Require Import ValidAux.
Require Import SoundBase.
Require Import SoundImplies.
Require Import SoundPostcondCmd.
Require Import SoundPostcondCall.
Require Import SoundPostcondPhinodes.
Require Import SoundInfrules.
Require Import SoundReduceMaydiff.
Require Import opsem_wf.

Set Implicit Arguments.

Inductive valid_state_sim
          (conf_src conf_tgt:Config)
          (stack0_src stack0_tgt:ECStack)
          (invmem:InvMem.Rel.t)
          (idx:nat)
          (st_src st_tgt:State): Prop :=
| valid_state_sim_intro
    m_src m_tgt
    fdef_hint cmds_hint
    inv
    invst
    (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
    (ECS_SRC: st_src.(ECS) = stack0_src)
    (ECS_TGT: st_tgt.(ECS) = stack0_tgt)
    (FDEF: valid_fdef m_src m_tgt st_src.(EC).(CurFunction) st_tgt.(EC).(CurFunction) fdef_hint)
    (LABEL: st_src.(EC).(CurBB).(fst) = st_tgt.(EC).(CurBB).(fst))
    inv_term
    (CMDS: valid_cmds m_src m_tgt st_src.(EC).(CurCmds) st_tgt.(EC).(CurCmds) cmds_hint inv = Some inv_term)
    (TERM: exists infrules,
        valid_terminator fdef_hint (Infrules.apply_infrules m_src m_tgt infrules inv_term) m_src m_tgt
                         (st_src.(EC).(CurFunction).(get_blocks))
                         (st_tgt.(EC).(CurFunction).(get_blocks))
                         (st_src.(EC).(CurBB).(fst))
                         (st_src.(EC).(Terminator))
                         (st_tgt.(EC).(Terminator)))
    (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
    (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
    (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src st_src)
    (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt st_tgt)
.

Lemma decide_nonzero_inject
      TD conds_src conds_tgt decision meminj
      (NONZERO: decide_nonzero TD conds_src decision)
      (INJECT: genericvalues_inject.gv_inject meminj conds_src conds_tgt)
  :
    <<NONZERO: decide_nonzero TD conds_tgt decision>>
.
Proof.
  inv NONZERO.
  red. econs; eauto. rewrite <- INT.
  symmetry.
  eapply genericvalues_inject.simulation__eq__GV2int; eauto.
Qed.

Lemma valid_sim_term
      conf_src conf_tgt inv0 idx0
      CurFunction0 CurBB0 Terminator0 Locals0 Allocas0
      ECS0 Mem0 CurFunction1 CurBB1 Terminator1 Locals1 Allocas1 ECS1 Mem1
      (ERROR_SRC : ~ error_state conf_src
                     (mkState (mkEC CurFunction0 CurBB0 [] Terminator0 Locals0 Allocas0) ECS0 Mem0))
      (m_src m_tgt : module)
      fdef_hint inv_term invst
      (CONF : InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (FDEF : valid_fdef m_src m_tgt CurFunction0 CurFunction1 fdef_hint)
      (LABEL : fst CurBB0 = fst CurBB1)
      (* (ALLOCAS: inject_allocas inv0 Allocas0 Allocas1) *)
      (TERM: exists infrules,
          valid_terminator fdef_hint (Infrules.apply_infrules m_src m_tgt infrules inv_term)
                           m_src m_tgt (get_blocks CurFunction0)
                           (get_blocks CurFunction1) (fst CurBB0) Terminator0 Terminator1)
      (MEM : InvMem.Rel.sem conf_src conf_tgt Mem0 Mem1 inv0)
      (STATE : InvState.Rel.sem conf_src conf_tgt
                                (mkState (mkEC CurFunction0 CurBB0 [] Terminator0 Locals0 Allocas0) ECS0 Mem0)
                                (mkState (mkEC CurFunction1 CurBB1 [] Terminator1 Locals1 Allocas1) ECS1 Mem1)
                                invst inv0 inv_term)
      (WF_SRC: wf_ConfigI conf_src /\
               wf_StateI conf_src (mkState (mkEC CurFunction0 CurBB0 [] Terminator0 Locals0 Allocas0)
                                           ECS0 Mem0))
      (WF_TGT: wf_ConfigI conf_tgt /\
               wf_StateI conf_tgt (mkState (mkEC CurFunction1 CurBB1 [] Terminator1 Locals1 Allocas1)
                                           ECS1 Mem1))
  :
    <<SIM_TERM: _sim_local conf_src conf_tgt
                           (valid_state_sim conf_src conf_tgt)
                           ECS0 ECS1 inv0 idx0
                           (mkState (mkEC CurFunction0 CurBB0 [] Terminator0 Locals0 Allocas0) ECS0 Mem0)
                           (mkState (mkEC CurFunction1 CurBB1 [] Terminator1 Locals1 Allocas1) ECS1 Mem1)
                           >>
.
Proof.
  des.
  unfold valid_terminator in TERM.
  expl apply_infrules_sound. cbn in *.
  simtac;
    (try by exfalso; eapply has_false_False; eauto).
  destruct Terminator0, Terminator1; simtac.
  + (* return *)
    move inv0 at bottom.
    move invmem1 at bottom.
    eapply _sim_local_return; eauto; ss.
    { apply STATE0. }
    { eapply Forall_harder; [apply STATE0|].
      s. i.
      rpapply H. symmetry. apply MEM0. }
    { eapply Forall_harder; [apply STATE0|].
      s. i.
      rpapply H. symmetry. apply MEM0. }
    { apply STATE0. }
    { apply STATE0. }
    i.
    exploit InvState.Rel.inject_value_spec; try exact COND0; eauto.
    { rewrite InvState.Unary.sem_valueT_physical. eauto. }
    i. des. rewrite InvState.Unary.sem_valueT_physical in VAL_TGT. ss.
    esplits; eauto.
  + (* return_void *)
    eapply _sim_local_return_void; eauto; ss.
    { apply STATE. }
    { eapply Forall_harder; [apply STATE|].
      s. i.
      rpapply H. symmetry. apply MEM. }
    { eapply Forall_harder; [apply STATE|].
      s. i.
      rpapply H. symmetry. apply MEM. }
    { apply STATE. }
    { apply STATE. }
  + (* br *)
    clears invst.
    rename STATE0 into STATE1.
    exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
    rewrite <- (ite_spec decision l0 l3) in *. simtac.
    exploit InvState.Rel.inject_value_spec; eauto.
    { rewrite InvState.Unary.sem_valueT_physical. eauto. }
    rewrite InvState.Unary.sem_valueT_physical. s. i. des.
    eapply _sim_local_step; swap 2 4. (* move 2 to the end *)
    {
      expl progress.
      - ss.
      - unfold OpsemPP.undefined_state in *.
        des_ifs; des; ss.
      - ii. ss.
    }
    { splits; ss. }
    { splits; ss. }
    i.
    expl preservation (try exact WF_TGT0; eauto). rename preservation into WF_TGT_NEXT.
    clear ERROR_SRC.
    inv STEP. unfold valid_phinodes in *.
    do 12 simtac0. rewrite <- (ite_spec decision0 l0 l3) in *.
    {
      inv CONF. inv INJECT0. ss. clarify.
      expl decide_nonzero_inject_aux. clarify.
      expl valid_fdef_valid_stmts (try exact COND3; eauto).
      expl valid_fdef_valid_stmts (try exact COND7; eauto).
      move COND1 at bottom.
      move COND2 at bottom.
      rename s0 into __s0__.
      rename s into __s__.

      Ltac hide_goal := (* for readability *)
        match goal with
        | [ |- ?g: ?G ] => remember g as Goal eqn: HeqGoal; move HeqGoal at top
        end.
      hide_goal.
      abstr (gen_infrules_next_inv
                           (Postcond.reduce_maydiff
                              (Infrules.apply_infrules m_src m_tgt
                                 (lookup_phinodes_infrules __s0__ (fst CurBB0)) t0))
                           (ValidationHint.invariant_after_phinodes __s0__)) infrulesA0.
      abstr (gen_infrules_next_inv
                           (Postcond.reduce_maydiff
                              (Infrules.apply_infrules m_src m_tgt
                                 (lookup_phinodes_infrules __s__ (fst CurBB0)) t))
                           (ValidationHint.invariant_after_phinodes __s__)) infrulesB0.
      unfold l in *.

      abstr (lookup_phinodes_infrules __s0__ (@fst atom stmts CurBB0)) infrulesA2.
      abstr (ValidationHint.invariant_after_phinodes __s0__) inv_afterA.
      assert(exists infrulesA1,
                (Invariant.implies
                  (Postcond.reduce_maydiff
                     (Infrules.apply_infrules m_src m_tgt infrulesA1
                        (Postcond.reduce_maydiff
                           (Infrules.apply_infrules m_src m_tgt infrulesA2 t0)))) inv_afterA)).
      { des_ifsH COND1; des_bool.
        - esplits; ss. eassumption.
        - exists nil. ss. etransitivity; eauto.
          eapply implies_reduce_maydiff; eauto. }
      clear COND1.

      abstr (lookup_phinodes_infrules __s__ (@fst atom stmts CurBB0)) infrulesB2.
      abstr (ValidationHint.invariant_after_phinodes __s__) inv_afterB.
      abstr (ValidationHint.cmds __s__) cmdsB.
      assert(exists infrulesB1,
                (Invariant.implies
                  (Postcond.reduce_maydiff
                     (Infrules.apply_infrules m_src m_tgt infrulesB1
                        (Postcond.reduce_maydiff
                           (Infrules.apply_infrules m_src m_tgt infrulesB2 t)))) inv_afterB)).
      { des_ifsH COND2; des_bool.
        - esplits; ss. eassumption.
        - exists nil. ss. etransitivity; eauto.
          eapply implies_reduce_maydiff; eauto. }
      clear COND2.

      des. clarify.
      (* expl add_terminator_cond_br. *)
      rewrite lookupBlockViaLabelFromFdef_spec in *.
      (* expl (lookupAL_ite fdef_hint decision0 l0 l3). *) (* TODO: Fix expl to pass thi *)
      exploit (lookupAL_ite fdef_hint decision0 l0 l3); eauto. clear COND7 COND3. i.
      exploit (lookupAL_ite CurFunction0.(get_blocks) decision0 l0 l3); eauto. clear COND8 COND4. i.
      exploit (lookupAL_ite CurFunction1.(get_blocks) decision0 l0 l3); eauto. clear COND9 COND5. i.
      (* TODO: apply & clear ? *)
      rewrite x1 in *. clarify.
      rewrite x2 in *. clarify.


      expl add_terminator_cond_br.
      destruct decision0; ss; clarify.
      -
        exploit postcond_phinodes_sound;
          try exact add_terminator_cond_br; try exact COND10; try eassumption; eauto; ss; []; intro STATE2.
        destruct STATE2 as [invst2 STATE2].
        clears add_terminator_cond_br invst1.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE3.
        destruct STATE3 as [invst3 [invmem3 [STATE3 [MEM3 MEMLE3]]]]; des.
        clears invst2.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE4.
        destruct STATE4 as [invst4 STATE4]; des.
        clears invst3.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE5.
        destruct STATE5 as [invst5 [invmem5 [STATE5 [MEM5 MEMLE5]]]]; des.
        clears invst4.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE6.
        destruct STATE6 as [invst6 STATE6]; des.
        clears invst5.

        assert(InvMem.Rel.le inv0 invmem5).
        { etransitivity; eauto. etransitivity; eauto. }


        esplits; eauto.
        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        {
          econs; eauto; ss.
          - eapply implies_sound; eauto.
            { ss. }
          - split; ss.
            eapply preservation; eauto.
            rpapply sBranch; eauto. ss.
            rewrite lookupBlockViaLabelFromFdef_spec. ss.
            (* Are we lucky? Will there be no siuation that forces us to get wf_src before esplits? *)
            (* Will we always be able to (easy to) re-construct sInsn like this? *)
        }
      -
        exploit postcond_phinodes_sound;
          try exact add_terminator_cond_br; try exact COND6; try eassumption; eauto; ss; []; intro STATE2.
        destruct STATE2 as [invst2 STATE2].
        clears add_terminator_cond_br invst1.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE3.
        destruct STATE3 as [invst3 [invmem3 [STATE3 [MEM3 MEMLE3]]]]; des.
        clears invst2.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE4.
        destruct STATE4 as [invst4 STATE4]; des.
        clears invst3.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE5.
        destruct STATE5 as [invst5 [invmem5 [STATE5 [MEM5 MEMLE5]]]]; des.
        clears invst4.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE6.
        destruct STATE6 as [invst6 STATE6]; des.
        clears invst5.

        assert(InvMem.Rel.le inv0 invmem5).
        { etransitivity; eauto. etransitivity; eauto. }
        esplits; eauto.
        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        {
          econs; eauto; ss.
          (* - eapply inject_allocas_inj_incr; eauto. *)
          - eapply implies_sound; eauto.
            { ss. }
          - split; ss.
            eapply preservation; eauto.
            rpapply sBranch; eauto. ss.
            rewrite lookupBlockViaLabelFromFdef_spec. ss.
        }
    }
  + (* br_uncond *)
    clears invst.
    rename STATE0 into STATE1.
    exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
    eapply _sim_local_step; swap 2 4. (* move 2 to the end *)
    {
      expl progress.
      - ss.
      - unfold OpsemPP.undefined_state in *.
        des_ifs; des; ss.
      - ii. ss.
    }
    { split; ss. }
    { split; ss. }
    i.
    expl preservation. rename preservation into WF_TGT_NEXT.
    clear ERROR_SRC.
    inv STEP. unfold valid_phinodes in *.
    {
      inv CONF. inv INJECT. ss. clarify.
      repeat (simtac0; []).
      expl valid_fdef_valid_stmts.
      hide_goal.
      abstr (gen_infrules_next_inv
                           (Postcond.reduce_maydiff
                              (Infrules.apply_infrules m_src m_tgt (lookup_phinodes_infrules s (fst CurBB0))
                                 t)) (ValidationHint.invariant_after_phinodes s)) infrulesA0.
      unfold l in *.

      abstr (lookup_phinodes_infrules s (@fst atom stmts CurBB0)) infrulesA2.
      abstr (ValidationHint.invariant_after_phinodes s) inv_afterA.
      assert(exists infrulesA1,
                (Invariant.implies
                  (Postcond.reduce_maydiff
                     (Infrules.apply_infrules m_src m_tgt infrulesA1
                        (Postcond.reduce_maydiff
                           (Infrules.apply_infrules m_src m_tgt infrulesA2 t)))) inv_afterA)).
      { des_ifsH COND0; des_bool.
        - esplits; ss. eassumption.
        - exists nil. ss. etransitivity; eauto.
          eapply implies_reduce_maydiff; eauto. }
      clear COND0.

      des. clarify.
      rewrite lookupBlockViaLabelFromFdef_spec in *.
      rewrite COND2 in *. rewrite COND3 in *. clarify.
      rewrite add_terminator_cond_br_uncond in *.

      -
        exploit postcond_phinodes_sound;
          try eassumption; eauto; ss; []; intro STATE2.
        destruct STATE2 as [invst2 STATE2].
        clears invst1.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE3.
        destruct STATE3 as [invst3 [invmem3 [STATE3 [MEM3 MEMLE3]]]]; des.
        clears invst2.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE4.
        destruct STATE4 as [invst4 STATE4]; des.
        clears invst3.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE5.
        destruct STATE5 as [invst5 [invmem5 [STATE5 [MEM5 MEMLE5]]]]; des.
        clears invst4.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE6.
        destruct STATE6 as [invst6 STATE6]; des.
        clears invst5.

        assert(InvMem.Rel.le inv0 invmem5).
        { etransitivity; eauto. etransitivity; eauto. }
        esplits; eauto.
        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        {
          econs; eauto; ss.
          (* - eapply inject_allocas_inj_incr; eauto. *)
          - eapply implies_sound; eauto.
            { ss. }
          - split; ss.
            eapply preservation; eauto.
            econs; eauto.
            rewrite lookupBlockViaLabelFromFdef_spec. ss.
        }
    }
  + (* switch *)
    clears invst.
    rename STATE0 into STATE1.
    exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
    eapply _sim_local_step; swap 2 4. (* move 2 to the end *)
    {
      expl progress.
      - ss.
      - unfold OpsemPP.undefined_state in *.
        des_ifs; des; ss.
      - ii. ss.
    }
    { split; ss. }
    { split; ss. }
    i.
    expl preservation. rename preservation into WF_TGT_NEXT.
    clear ERROR_SRC.
    inv STEP. unfold valid_phinodes in *.
    {
      inv CONF. inv INJECT. ss. clarify.
      des_sumbool. subst. (* list_const_l_dec *)
      rename l_0 into dflt.
      rename l1 into cases.
      rename COND3 into COND_DFLT.
      rename COND2 into COND_CASES.
      repeat (simtac0; []).
      rename COND4 into PCOND_DFLT.
      hexploit InvState.Rel.inject_value_spec; try exact STATE1; ss; eauto.
      { rewrite InvState.Unary.sem_valueT_physical. eauto. }
      i; des.
      rewrite InvState.Unary.sem_valueT_physical in *. ss. clarify.
      expl get_switch_branch_inject. clarify.
      hide_goal.

      expl add_terminator_cond_switch.

      expl get_switch_branch_in_successors.
      unfold successors_terminator in *.
      apply nodup_In in get_switch_branch_in_successors0. ss. des.
      { (* default *)
        expl valid_fdef_valid_stmts.
        clear COND_CASES.
        subst dflt.
        rewrite lookupBlockViaLabelFromFdef_spec in *.

        move H19 at bottom.
        move COND3 at bottom.
        move get_switch_branch_inject at bottom.

        eq_closure_tac. clarify.

        abstr (gen_infrules_next_inv
                 (Postcond.reduce_maydiff
                    (Infrules.apply_infrules m_src m_tgt
                                             (lookup_phinodes_infrules s (fst CurBB0)) t))
                 (ValidationHint.invariant_after_phinodes s)) infrulesA0.
        unfold l in *.


        abstr (lookup_phinodes_infrules s (@fst atom stmts CurBB0)) infrulesA2.
        abstr (ValidationHint.invariant_after_phinodes s) inv_afterA.
        assert(exists infrulesA1,
                  (Invariant.implies
                     (Postcond.reduce_maydiff
                        (Infrules.apply_infrules
                           m_src m_tgt infrulesA1
                           (Postcond.reduce_maydiff
                              (Infrules.apply_infrules m_src m_tgt infrulesA2 t)))) inv_afterA)).
        { des_ifsH COND_DFLT; des_bool.
          - esplits; ss. eassumption.
          - exists nil. ss. etransitivity; eauto.
            eapply implies_reduce_maydiff; eauto. }
        clear COND_DFLT.
        des.



        exploit postcond_phinodes_sound; try exact PCOND_DFLT; try exact add_terminator_cond_switch;
          ss; eauto; []; intro STATE2. destruct STATE2 as [invst2 STATE2].
        clears invst1.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE3.
        destruct STATE3 as [invst3 [invmem3 [STATE3 [MEM3 MEMLE3]]]]; des.
        clears invst2.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE4.
        destruct STATE4 as [invst4 STATE4]; des.
        clears invst3.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE5.
        destruct STATE5 as [invst5 [invmem5 [STATE5 [MEM5 MEMLE5]]]]; des.
        clears invst4.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE6.
        destruct STATE6 as [invst6 STATE6]; des.
        clears invst5.


        assert(InvMem.Rel.le inv0 invmem5).
        { etransitivity; eauto. etransitivity; eauto. }
        esplits; eauto.
        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        {
          econs; eauto; ss.
          (* - eapply inject_allocas_inj_incr; eauto. *)
          - eapply implies_sound; eauto.
            { ss. }
          - split; ss.
            eapply preservation; eauto.
            econs; eauto.
            rewrite lookupBlockViaLabelFromFdef_spec. ss.
        }
      }
      { (* cases *)
        (* clears dflt. *)
        clear COND_DFLT PCOND_DFLT COND1 COND2 COND3.
        apply list_prj2_inv in get_switch_branch_in_successors0. des.
        rewrite forallb_forall in COND_CASES.
        specialize (COND_CASES (x, tgt0) get_switch_branch_in_successors0).
        clear get_switch_branch_in_successors0.
        des_bool. des_ifs_safe. des_bool.
        clear_tac. rename Heq into COND_CASES. rename Heq3 into PCOND_CASES.
        rewrite lookupBlockViaLabelFromFdef_spec in *.
        ss. eq_closure_tac. clarify.
        expl valid_fdef_valid_stmts. ss.

        abstr (gen_infrules_next_inv
                 (Postcond.reduce_maydiff
                    (Infrules.apply_infrules m_src m_tgt
                                             (lookup_phinodes_infrules s0 (fst CurBB0)) t0))
                 (ValidationHint.invariant_after_phinodes s0)) infrulesA0.
        unfold l in *.


        abstr (lookup_phinodes_infrules s0 (@fst atom stmts CurBB0)) infrulesA2.
        abstr (ValidationHint.invariant_after_phinodes s0) inv_afterA.
        assert(exists infrulesA1,
                  (Invariant.implies
                     (Postcond.reduce_maydiff
                        (Infrules.apply_infrules
                           m_src m_tgt infrulesA1
                           (Postcond.reduce_maydiff
                              (Infrules.apply_infrules m_src m_tgt infrulesA2 t0)))) inv_afterA)).
        { des_ifsH COND_CASES; des_bool.
          - esplits; ss. eassumption.
          - exists nil. ss. etransitivity; eauto.
            eapply implies_reduce_maydiff; eauto. }
        clear COND_CASES.
        des.


        exploit postcond_phinodes_sound; try exact PCOND_CASES; try exact add_terminator_cond_switch;
          ss; eauto; []; intro STATE2. destruct STATE2 as [invst2 STATE2].
        clears invst1.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE3.
        destruct STATE3 as [invst3 [invmem3 [STATE3 [MEM3 MEMLE3]]]]; des.
        clears invst2.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE4.
        destruct STATE4 as [invst4 STATE4]; des.
        clears invst3.

        exploit apply_infrules_sound; eauto; ss; []; intro STATE5.
        destruct STATE5 as [invst5 [invmem5 [STATE5 [MEM5 MEMLE5]]]]; des.
        clears invst4.

        exploit reduce_maydiff_sound; eauto; ss; []; intro STATE6.
        destruct STATE6 as [invst6 STATE6]; des.
        clears invst5.


        assert(InvMem.Rel.le inv0 invmem5).
        { etransitivity; eauto. etransitivity; eauto. }
        esplits; eauto.
        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        {
          econs; eauto; ss.
          (* - eapply inject_allocas_inj_incr; eauto. *)
          - eapply implies_sound; eauto.
            { ss. }
          - split; ss.
            eapply preservation; eauto.
            econs; eauto.
            rewrite lookupBlockViaLabelFromFdef_spec. ss.
        }
      }
    }
  + (* unreachable *)
    exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
Unshelve.
all: try destruct CONF; subst; ss.
Qed.
(* TODO: Pull out same pattern as lemma or tac *)

(* TODO: move to postcond.v? SoundBase? Maybe this is proper position.. *)
Lemma postcond_cmd_implies_inject_event
      c0 c1 inv t
      (POSTCOND: Postcond.postcond_cmd c0 c1 inv = Some t)
  :
    <<INJECT_EVENT: Postcond.postcond_cmd_inject_event
                      c0 c1
                      (if Instruction.isCallInst c0
                       then
                         Postcond.ForgetStackCall.t (AtomSetImpl_from_list (Postcond.Cmd.get_def c0))
                                                    (AtomSetImpl_from_list (Postcond.Cmd.get_def c1))
                                                    (Postcond.ForgetMemoryCall.t inv)
                       else
                         Postcond.ForgetStack.t
                           (AtomSetImpl_from_list (Postcond.Cmd.get_def c0))
                           (AtomSetImpl_from_list (Postcond.Cmd.get_def c1))
                           (AtomSetImpl_from_list (Postcond.Cmd.get_leaked_ids c0))
                           (AtomSetImpl_from_list (Postcond.Cmd.get_leaked_ids c1))
                           (Postcond.ForgetMemory.t (Postcond.Cmd.get_def_memory c0)
                                                    (Postcond.Cmd.get_def_memory c1)
                                                    (Postcond.Cmd.get_leaked_ids_to_memory c0)
                                                    (Postcond.Cmd.get_leaked_ids_to_memory c1) inv))
                    = true>>
.
Proof.
  unfold Postcond.postcond_cmd in *.
  unfold Postcond.postcond_cmd_check in *.
  des_ifs; ss; des_bool; ss.
Qed.

Lemma valid_progress
      conf_src conf_tgt stack0_src stack0_tgt inv0 idx0 st_src st_tgt
      (VALID: valid_state_sim conf_src conf_tgt stack0_src stack0_tgt inv0 idx0 st_src st_tgt)
      (ERROR_SRC: ~ error_state conf_src st_src)
      (* (NOTCALL: option_Forall (fun c => Instruction.isCallInst c = false ) (hd_error st_src.(EC).(CurCmds))) *)
      c_src cs_src
      (CMDSRC: st_src.(EC).(CurCmds) = c_src :: cs_src)
      (NOTCALL: Instruction.isCallInst c_src = false)
      c_tgt cs_tgt
      (CMDTGT: st_tgt.(EC).(CurCmds) = c_tgt :: cs_tgt)
      (NOTFINAL: s_isFinialState conf_tgt st_tgt = None)
  :
    <<PROGRESS: ~stuck_state conf_tgt st_tgt>>
.
Proof.
  inv VALID.
  des.
  expl progress; ss. clear WF_TGT WF_TGT0.
  destruct st_src, st_tgt; ss.
  destruct EC0, EC1; ss.
  destruct CurCmds0, CurCmds1; ss. clarify; clear_tac.
  des_ifs_safe.
  unfold OpsemPP.undefined_state in *.
  des_ifs_safe.
  des; ss.
  - des_ifs; ss.
  - des_ifsH IS_UNDEFINED; ss.
    unfold Debug.debug_print_auto in *.
    unfold Debug.failwith_None in *.
    des_ifs_safe.
Abort.


Lemma valid_sim
      conf_src conf_tgt:
  (valid_state_sim conf_src conf_tgt) <6= (sim_local conf_src conf_tgt).
Proof.
  pcofix CIH.
  intros stack0_src stack0_tgt inv0 idx0 st_src st_tgt SIM. pfold.
  apply _sim_local_src_error. i.
  destruct st_src, st_tgt. destruct EC0, EC1.
  inv SIM. ss.
  destruct CurCmds0; simtac;
    (try by exfalso; eapply has_false_False; eauto).
  - (* term *)
    des.
    expl valid_sim_term.
    eapply _sim_local_mon; eauto.
  - (* cmd *)
    destruct (Instruction.isCallInst c) eqn:CALL.
    + (* call *)
      exploit postcond_cmd_is_call; eauto. i.
      destruct c; ss. destruct c0; ss.
      hexploit postcond_call_sound; try exact COND; eauto;
        (try instantiate (2 := (mkState (mkEC _ _ _ _ _ _) _ _))); ss; eauto; ss.
      i. des. subst. do 24 simtac0. des.
      eapply _sim_local_call with
      (uniqs_src:= (memory_blocks_of conf_src Locals0 (Invariant.unique (Invariant.src inv))))
        (uniqs_tgt:= (memory_blocks_of conf_tgt Locals1 (Invariant.unique (Invariant.tgt inv))))
        (privs_src:= (memory_blocks_of_t conf_src _ _ (Invariant.private (Invariant.src inv))))
        (privs_tgt:= (memory_blocks_of_t conf_tgt _ _ (Invariant.private (Invariant.tgt inv))));
        ss; eauto; ss.
      { inv STATE. inv SRC.
        unfold memory_blocks_of. ii.
        des.
        match goal with [ H: In _ (flat_map _ _) |- _ ] => eapply in_flat_map in H; eauto end.
        des.
        des_ifs.
        exploit UNIQUE.
        { apply AtomSetFacts.elements_iff, InA_iff_In. eauto. }
        intro UNIQUE_A. inv UNIQUE_A. ss. clarify.
        exploit MEM0; eauto.
      }
      { inv STATE. inv SRC.
        unfold memory_blocks_of. ii.
        des.
        match goal with [ H: In _ (flat_map _ _) |- _ ] => eapply in_flat_map in H; eauto end.
        des.
        des_ifs.
        exploit UNIQUE.
        { apply AtomSetFacts.elements_iff, InA_iff_In. eauto. }
        intro UNIQUE_A. inv UNIQUE_A. ss. clarify.
        exploit GLOBALS; eauto.
        (* NEED TO STRENGTHEN GLOBALS *)
      }

      { inv STATE. inv TGT.
        unfold memory_blocks_of. ii.
        des.
        match goal with [ H: In _ (flat_map _ _) |- _ ] => eapply in_flat_map in H; eauto end.
        des.
        des_ifs.
        exploit UNIQUE.
        { apply AtomSetFacts.elements_iff, InA_iff_In. eauto. }
        intro UNIQUE_A. inv UNIQUE_A. ss. clarify.
        exploit MEM0; eauto.
      }
      { inv STATE. inv TGT.
        unfold memory_blocks_of. ii.
        des.
        match goal with [ H: In _ (flat_map _ _) |- _ ] => eapply in_flat_map in H; eauto end.
        des.
        des_ifs.
        exploit UNIQUE.
        { apply AtomSetFacts.elements_iff, InA_iff_In. eauto. }
        intro UNIQUE_A. inv UNIQUE_A. ss. clarify.
        exploit GLOBALS; eauto.
      }
      { inv STATE. inv SRC. ss.
        i. unfold memory_blocks_of_t in IN.
        des.
        match goal with [ H: In _ (flat_map _ _) |- _ ] => eapply in_flat_map in H; eauto end.
        des.
        des_ifs.
        exploit PRIVATE; eauto.
        { apply Exprs.IdTSetFacts.elements_iff.
          apply In_InA; eauto. }
        ss. i. des. clarify.
      }
      { inv STATE. inv TGT. ss.
        i. unfold memory_blocks_of_t in IN.
        des.
        match goal with [ H: In _ (flat_map _ _) |- _ ] => eapply in_flat_map in H; eauto end.
        des.
        des_ifs.
        exploit PRIVATE; eauto.
        { apply Exprs.IdTSetFacts.elements_iff.
          apply In_InA; eauto. }
        ss. i. des. clarify.
      }
      i. exploit RETURN; eauto. i. des.
      exploit apply_infrules_sound; eauto; ss. i. des.
      exploit reduce_maydiff_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      exists locals2_tgt, 0%nat, invmem1. splits; ss.
      * etransitivity; eauto.
      * right. apply CIH. econs; eauto.
        (* { ss. *)
        (*   eapply inject_allocas_inj_incr; eauto. *)
        (*   etransitivity; eauto. } *)
    + (* non-call *)
      des.
      eapply _sim_local_step; swap 2 4. (* move 2 to the end *)
      {
        expl progress.
        - ss.
        - move ERROR_SRC at bottom.
          apply error_state_neg in ERROR_SRC. des; ss. apply NNPP in ERROR_SRC. des.
          rename ERROR_SRC into SRC_STEP.
          rename COND0 into POSTCOND.
          rename inv0 into invmem.
          rename inv into inv0.
          move POSTCOND at bottom.
          destruct conf_src; ss.
          inv CONF. inv INJECT. ss. clarify.
          eapply postcond_cmd_implies_inject_event in POSTCOND; des. rewrite CALL in *.

          unfold OpsemPP.undefined_state in *.
          des_ifs_safe. des; ss; des_ifs_safe; ss.
          + des_ifs; ss.
          + exfalso.
            destruct c; des_ifs. ss. des_bool; des. des_sumbool. clarify.
            inv SRC_STEP.
            assert(INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) mptr0 g).
            {
              eapply InvState.Subset.inject_value_Subset in POSTCOND0; cycle 1.
              { instantiate (1:= inv0).
                etransitivity; eauto.
                { eapply SoundForgetStack.forget_stack_Subset; eauto. }
                etransitivity; eauto.
                { eapply SoundForgetMemory.forget_memory_Subset; eauto. }
                reflexivity.
              }
              exploit InvState.Rel.inject_value_spec; try exact POSTCOND0; eauto.
              { ss. }
              { rewrite InvState.Unary.sem_valueT_physical. ss. rewrite <- H17. ss. }
              i; des.
              rewrite InvState.Unary.sem_valueT_physical in *. ss. rewrite Heq in *. clarify.
            }
            {
              (* free inject. easy *)
              unfold free in *. des_ifs_safe.
              unfold GV2ptr in *. des_ifs_safe.
              repeat all_with_term ltac:(fun H => inv H) genericvalues_inject.gv_inject.
              repeat all_with_term ltac:(fun H => inv H) memory_sim.MoreMem.val_inject.
              exploit genericvalues_inject.mem_inj__free; eauto; try apply MEM; i; des.
              assert(delta = 0).
              { inv MEM. ss. inv WF. expl mi_bounds. }
              clarify.
              repeat rewrite Z.add_0_r in *.
              rewrite <- int_add_0 in *. clarify.

              des_ifs.
              exploit genericvalues_inject.mi_bounds.
              { apply MEM. }
              { eauto. }
              i; des.

              eq_closure_tac.
              clarify.
            }
          +
            destruct c; des_ifs; ss; repeat (des_bool; des; des_sumbool; clarify).
            * (* nop case *)
              exfalso.
              rewrite SoundSnapshot.ExprPairSet_exists_filter in POSTCOND.
              apply Exprs.ExprPairSetFacts.exists_iff in POSTCOND; [|solve_compat_bool].
              unfold Exprs.ExprPairSet.Exists in *. des.
              des_ifs. des_bool. des. unfold compose in *. des_bool.
              apply Exprs.ExprPairSetFacts.mem_iff in POSTCOND.
              {
                des. des_sumbool. clarify.
                assert(NOT_IN_MD: Invariant.not_in_maydiff inv0
                                            (Exprs.ValueT.lift Exprs.Tag.physical value1)).
                {
                  expl SoundForgetStack.forget_stack_Subset.
                  eapply InvState.Subset.not_in_maydiff_Subset; eauto.
                } clear POSTCOND0.


                assert(DEFINED: exists val, const2GV CurTargetData0 Globals0 (const_undef typ5) =
                                            Some val).
                { admit. }
                des.
                exploit InvState.Rel.lessdef_expr_spec; eauto.
                { apply STATE. }
                { unfold InvState.Unary.sem_expr. ss. eauto. }
                i; des. ss. rewrite InvState.Unary.sem_valueT_physical in *. ss. des_ifs.

                exploit InvState.Rel.not_in_maydiff_value_spec; try apply STATE; eauto.
                { ss.  }
                { rewrite InvState.Unary.sem_valueT_physical. ss. eauto. }
                i; des.
                rewrite InvState.Unary.sem_valueT_physical in *. ss.

                {
                  (* load inject. easy *)
                  unfold mload in *. des_ifs_safe.
                  unfold GV2ptr in *. des_ifs_safe.
                  rename g into __g__.
                  repeat all_with_term ltac:(fun H => inv H) genericvalues_inject.gv_inject.
                  repeat all_with_term ltac:(fun H => inv H) memory_sim.MoreMem.val_inject.
                  exploit genericvalues_inject.simulation_mload_aux; eauto; try apply MEM; i; des.
                  assert(delta = 0).
                  { inv MEM. ss. inv WF. expl mi_bounds. }
                  clarify.
                  rewrite Z.add_0_r in *.
                  rewrite <- int_add_0 in *. clarify.
                }
              }
            * exfalso.
              inv SRC_STEP.
              assert(INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) mp g).
              {
                eapply InvState.Subset.inject_value_Subset in POSTCOND0; cycle 1.
                { instantiate (1:= inv0).
                  etransitivity; eauto.
                  { eapply SoundForgetStack.forget_stack_Subset; eauto. }
                  etransitivity; eauto.
                  { eapply SoundForgetMemory.forget_memory_Subset; eauto. }
                  reflexivity.
                }
                exploit InvState.Rel.inject_value_spec; try exact POSTCOND0; eauto.
                { ss. }
                { rewrite InvState.Unary.sem_valueT_physical. ss. rewrite <- H18. ss. }
                i; des.
                rewrite InvState.Unary.sem_valueT_physical in *. ss. rewrite Heq in *. clarify.
              }
              {
                (* load inject. easy *)
                unfold mload in *. des_ifs_safe.
                unfold GV2ptr in *. des_ifs_safe.
                repeat all_with_term ltac:(fun H => inv H) genericvalues_inject.gv_inject.
                repeat all_with_term ltac:(fun H => inv H) memory_sim.MoreMem.val_inject.
                exploit genericvalues_inject.simulation_mload_aux; eauto; try apply MEM; i; des.
                assert(delta = 0).
                { inv MEM. ss. inv WF. expl mi_bounds. }
                clarify.
                rewrite Z.add_0_r in *.
                rewrite <- int_add_0 in *. clarify.
              }
          + exfalso.
            destruct c; des_ifs; ss; repeat (des_bool; des; des_sumbool; clarify).
            inv SRC_STEP.
            assert(INJECT1 : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) gv1 g).
            {
              eapply InvState.Subset.inject_value_Subset in POSTCOND1; cycle 1.
              { instantiate (1:= inv0).
                etransitivity; eauto.
                { eapply SoundForgetStack.forget_stack_Subset; eauto. }
                etransitivity; eauto.
                { eapply SoundForgetMemory.forget_memory_Subset; eauto. }
                reflexivity.
              }
              exploit InvState.Rel.inject_value_spec; try exact POSTCOND1; eauto.
              { ss. }
              { rewrite InvState.Unary.sem_valueT_physical. ss. rewrite <- H19. ss. }
              i; des.
              rewrite InvState.Unary.sem_valueT_physical in *. ss. rewrite Heq in *. clarify.
            }
            assert(INJECT2 : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) mp2 g0).
            {
              eapply InvState.Subset.inject_value_Subset in POSTCOND0; cycle 1.
              { instantiate (1:= inv0).
                etransitivity; eauto.
                { eapply SoundForgetStack.forget_stack_Subset; eauto. }
                etransitivity; eauto.
                { eapply SoundForgetMemory.forget_memory_Subset; eauto. }
                reflexivity.
              }
              exploit InvState.Rel.inject_value_spec; try exact POSTCOND0; eauto.
              { ss. }
              { rewrite InvState.Unary.sem_valueT_physical. ss. rewrite <- H20. ss. }
              i; des.
              rewrite InvState.Unary.sem_valueT_physical in *. ss. rewrite Heq0 in *. clarify.
            }
            {
              (* mstore inject. easy *)
              unfold mstore in *. des_ifs_safe.
              unfold GV2ptr in *. des_ifs_safe.
              inv INJECT2. inv H4.
              repeat all_with_term ltac:(fun H => inv H) memory_sim.MoreMem.val_inject.
              exploit genericvalues_inject.mem_inj_mstore_aux; eauto; try apply MEM; i; des.
              assert(delta = 0).
              { inv MEM. ss. inv WF. expl mi_bounds. }
              clarify.
              rewrite Z.add_0_r in *.
              rewrite <- int_add_0 in *. clarify.
            }
          + destruct c; ss.
        - i; ss.
      }
      { split; ss. }
      { split; ss. }
      i.
      expl preservation. rename preservation into WF_TGT_NEXT.
      exploit postcond_cmd_is_call; eauto. i. rewrite CALL in x0.
      exploit sInsn_non_call; eauto; try congruence. i. des. subst. ss.
      exploit postcond_cmd_sound; eauto; ss; try congruence. i. des.
      exploit sInsn_non_call; eauto; try congruence. i. des. subst. ss.
      exploit apply_infrules_sound; eauto; ss. i. des.
      exploit reduce_maydiff_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      esplits; (try by etransitivity; eauto); eauto.
      { econs 1. eauto. }
      right. apply CIH. econs; try exact x1; eauto.
Unshelve.
all: try ss.
Admitted.


(* TODO: move to better position? with init_invvmem in SimModule *)
(* I think the laziest point (here) may make sense in this case .. *)
Definition init_invst: InvState.Rel.t :=
  (InvState.Rel.mk (InvState.Unary.mk [] []) (InvState.Unary.mk [] [])).

Lemma function_entry_inv_sound
      conf_src conf_tgt
      (CONF: inject_conf conf_src conf_tgt)
      invmem
      st_src st_tgt
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
      (INITST: st_src.(EC).(Allocas) = [] /\ st_tgt.(EC).(Allocas) = [])
      args args_src args_tgt
      (INJECT_ARGS: list_forall2 (genericvalues_inject.gv_inject
                                    (InvMem.Rel.inject invmem)) args_src args_tgt)
      (INITLOCALS_SRC: initLocals (CurTargetData conf_src) args args_src =
                       Some st_src.(EC).(Locals))
      (INITLOCALS_TGT: initLocals (CurTargetData conf_tgt) args args_tgt =
                       Some st_tgt.(EC).(Locals))
      (INJECT_LOCALS: inject_locals invmem st_src.(EC).(Locals) st_tgt.(EC).(Locals))
      (WF_SRC: wf_EC st_src.(EC) /\ wf_fdef conf_src.(CurSystem) conf_src st_src.(EC).(CurFunction))
      (WF_TGT: wf_EC st_tgt.(EC) /\ wf_fdef conf_tgt.(CurSystem) conf_tgt st_tgt.(EC).(CurFunction))
      (* TODO: conf_src.(CurSystem) != [(module_of_conf conf_src)] *)
      (* WF condition for this? which is conceptually right? *)
      (* Anyway, let's do this lazy.. *)
      prods_src prods_tgt
  :
    (* TODO: prods_src/prods_tgt are not bound. is it ok? *)
  <<SEM: InvState.Rel.sem conf_src conf_tgt
                          st_src st_tgt init_invst invmem
                          (Invariant.function_entry_inv args args prods_src prods_tgt)>>
.
Proof.
  (* inject_locals is reduced from below *)
  (* LLVMBerry.proof.Inject.locals_init *)
  destruct st_src, st_tgt; ss.
  destruct EC0, EC1; ss.
  des; clarify.
  econs; ss; eauto.
  - econs; ss; eauto.
    + admit. (* function_entry_inv *)
    + econs; ss; eauto.
      * ii. clarify.
        eapply Exprs.ValueTPairSetFacts.empty_iff; eauto.
        eapply Exprs.ValueTPairSetFacts.mem_iff; eauto.
      * ii. clarify.
        eapply Exprs.PtrPairSetFacts.empty_iff; eauto.
        eapply Exprs.PtrPairSetFacts.mem_iff; eauto.
    + ii. exfalso. eapply AtomSetFacts.empty_iff; eauto.
    + ii. exfalso. eapply Exprs.IdTSetFacts.empty_iff; eauto.
    + (* wf_lc *)
      inv MEM.
      clear SRC TGT INJECT FUNTABLE.
      inv WF.
      clear Hno_overlap Hmap1 Hmap2
            (* mi_freeblocks *)
            mi_mappedblocks mi_range_block mi_bounds mi_globals.
      clear_tac. unfold initLocals in *.
      {
        ii.
        expl INJECT_LOCALS.
        clear - INJECT mi_freeblocks.
        ginduction gvs; ii; ss.
        - inv INJECT.
          expl IHgvs.
          des_ifs; eauto.
          split; ss.
          inv H1.
          reductio_ad_absurdum.
          expl mi_freeblocks.
          clarify.
      }
    + (* diffblock unique parent *)
      inv MEM. clear TGT INJECT FUNTABLE.
      inv SRC.
      clear MEM_PARENT UNIQUE_PARENT_MEM UNIQUE_PARENT_GLOBALS NEXTBLOCK NEXTBLOCK_PARENT.
      ii.
      eapply sublist_In in UNIQUE_PRIVATE_PARENT; eauto.
      expl PRIVATE_PARENT.
      expl INJECT_LOCALS.
      unfold InvMem.private_block in *. des.
      clear - PRIVATE_PARENT0 ING INJECT.
      ginduction INJECT; ii; ss.
      rewrite GV2blocks_cons in ING.
      apply in_app in ING. des.
      { destruct v1; ss. des; ss. clarify.
        apply PRIVATE_PARENT0; eauto.
        ii. inv H; clarify.
      }
      eapply IHINJECT; eauto.
  - (* tgt. same with src *) admit.
  - ii. clear NOTIN.
    destruct id0; ss.
    destruct t; ss.
    unfold InvState.Unary.sem_idT in *. ss.
    eapply INJECT_LOCALS; eauto.
  - econs; eauto.
Admitted.

Lemma init_fdef_wf_EC
      conf fdef args ec
      (INIT: init_fdef conf fdef args ec)
  :
    <<WF: wf_EC ec>>
.
Proof.
  inv INIT; ss.
  des_ifs.
  econs; ss; eauto.
  - apply orb_true_iff. left. unfold blockEqB. unfold sumbool2bool. des_ifs.
  - unfold get_cmds_from_block. ss. apply sublist_refl.
  - unfold terminatorEqB. unfold sumbool2bool. des_ifs.
Qed.

Lemma valid_init
      m_src m_tgt
      conf_src conf_tgt
      stack0_src stack0_tgt
      fdef_src fdef_tgt
      fdef_hint
      args_src args_tgt
      mem_src mem_tgt
      inv idx
      ec_src
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint)
      (ARGS: list_forall2 (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) args_src args_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (INIT_SRC: init_fdef conf_src fdef_src args_src ec_src)
  :
  exists ec_tgt,
    (<<INIT_TGT: init_fdef conf_tgt fdef_tgt args_tgt ec_tgt>>) /\
    (forall (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src (mkState ec_src stack0_src mem_src))
            (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt (mkState ec_tgt stack0_tgt mem_tgt))
            (WF_FDEF_SRC: wf_fdef conf_src.(CurSystem) conf_src ec_src.(CurFunction))
            (WF_FDEF_TGT: wf_fdef conf_tgt.(CurSystem) conf_tgt ec_tgt.(CurFunction))
      ,
        <<SIM:
          valid_state_sim
            conf_src conf_tgt
            stack0_src stack0_tgt
            inv idx
            (mkState ec_src stack0_src mem_src)
            (mkState ec_tgt stack0_tgt mem_tgt)>>).
Proof.
  expl init_fdef_wf_EC. rename init_fdef_wf_EC0 into WF_EC_SRC. (* TODO: make "expl into" *)
  inv INIT_SRC. unfold valid_fdef in FDEF. simtac.
  exploit locals_init; eauto; [by apply CONF|apply MEM|]. i. des.
  generalize FDEF. i.
  unfold forallb2AL in FDEF0. ss. apply andb_true_iff in FDEF0. des.
  do 10 simtac0.
  unfold proj_sumbool in *. des_ifs_safe ss. clarify.
  assert(VALID_TERM_INFRULES: exists infrules,
            valid_terminator fdef_hint
                             (Infrules.apply_infrules
                                (module_intro layouts5 namedts5 products5)
                                (module_intro layouts0 namedts0 products0)
                                infrules t)
                             (module_intro layouts5 namedts5 products5)
                             (module_intro layouts0 namedts0 products0)
                             ((l0, stmts_intro ps' cs' tmn') :: b0)
                             ((l0, stmts_intro phinodes5 cmds5 terminator5) :: b1)
                             l0 tmn' terminator5).
  { simtac.
    - exists nil. assumption.
    - eexists; eassumption.
  }
  clear COND4. des.

  i. des.

  eexists.
  apply dependent_split.
  - econs; eauto; ss.
  - intros INIT_TGT ? ? ? ? . des.
    expl init_fdef_wf_EC. rename init_fdef_wf_EC0 into WF_EC_TGT. clear INIT_TGT.
    econs; eauto.
  (* esplits. *)
  (* - econs; eauto; ss. *)
  (* - econs; eauto. *)
    { ss.
      repeat
        (try match goal with
             | [|- is_true (if ?c then _ else _)] =>
               let COND := fresh "COND" in
               destruct c eqn:COND
             end;
         simtac).
      { match goal with
        | [H: proj_sumbool (fheader_dec ?a ?a) = false |- _] => destruct (fheader_dec a a); ss
        end.
      }
      apply andb_true_iff. splits; [|by eauto].
      repeat
        (try match goal with
             | [|- (if ?c then _ else _) = true] =>
               let COND := fresh "COND" in
               destruct c eqn:COND
             end;
         simtac).
      { match goal with
        | [H: proj_sumbool (id_dec ?a ?a) = false |- _] => destruct (id_dec a a); ss
        end.
      }
      des_ifs_safe ss. clarify.
    }
    {
      eapply implies_sound; eauto.
      clear FDEF FDEF1. clear_tac.
      clear COND VALID_TERM_INFRULES. clear_tac.
      inv CONF. unfold is_empty in *. des_ifs.
      clear COND0 COND3. clear_tac.
      eapply function_entry_inv_sound; eauto.
    }
Qed.

Lemma valid_sim_fdef
      m_src m_tgt
      conf_src conf_tgt
      fdef_src fdef_tgt
      fdef_hint
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint)
      (WF_SRC: wf_ConfigI conf_src)
      (WF_TGT: wf_ConfigI conf_tgt)
      (WF_FDEF_SRC: wf_fdef conf_src.(CurSystem) conf_src fdef_src)
      (WF_FDEF_TGT: wf_fdef conf_tgt.(CurSystem) conf_tgt fdef_tgt)
  :
  sim_fdef conf_src conf_tgt fdef_src fdef_tgt.
Proof.
  ii.
  assert(WF: wf_EC ec0_src).
  { inv SRC. ss.
    des_ifs.
    econs; ss; eauto.
    - apply orb_true_iff. left. unfold blockEqB. unfold sumbool2bool. des_ifs.
    - unfold get_cmds_from_block. ss. apply sublist_refl.
    - unfold terminatorEqB. unfold sumbool2bool. des_ifs.
  }
  exploit valid_init; eauto.
  intro VALID_INIT. des.
  esplits; eauto. i.
  specialize (VALID_INIT0 WF_SRC0).
  specialize (VALID_INIT0 WF_TGT0).
  exploit VALID_INIT0.
  { rpapply WF_FDEF_SRC. inv SRC. ss. }
  { rpapply WF_FDEF_TGT. inv INIT_TGT. ss. }
  intro VALID_INIT; des.
  apply valid_sim; eauto.
Grab Existential Variables.
  { exact 0%nat. }
Qed.
