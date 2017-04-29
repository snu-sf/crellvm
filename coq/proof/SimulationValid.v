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
Require Import PropOpsem.
Require Import SimulationLocal.
Require Import Simulation.
Require Import Inject.
Require InvMem.
Require InvState.
Require Import PropValid.
Require Import SoundBase.
Require Import SoundImplies.
Require Import SoundPostcondCmd.
Require Import SoundPostcondCall.
Require Import SoundPostcondPhinodes.
Require Import SoundInfrules.
Require Import SoundReduceMaydiff.
Require Import opsem_wf.

Set Implicit Arguments.

(* TODO: Move to definition point. Why error_state is defined in GenericValues? *)
Lemma error_state_neg conf st
      (NERROR_SRC: ~error_state conf st)
  :
    <<NERROR_SRC: ~(stuck_state conf st) \/ exists gv, s_isFinialState conf st = Some gv>>
.
Proof.
  red. unfold not in NERROR_SRC.
  apply imply_to_or.
  i.
  destruct (s_isFinialState conf st) eqn:T.
  { esplits; eauto. }
  exploit NERROR_SRC; eauto.
  { econs; eauto. }
  i; ss.
Qed.

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
    (ALLOCAS: inject_allocas invmem st_src.(EC).(Allocas) st_tgt.(EC).(Allocas))
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
      (ALLOCAS: inject_allocas inv0 Allocas0 Allocas1)
      (TERM: exists infrules,
          valid_terminator fdef_hint (Infrules.apply_infrules m_src m_tgt infrules inv_term)
                           m_src m_tgt (get_blocks CurFunction0)
                           (get_blocks CurFunction1) (fst CurBB0) Terminator0 Terminator1)
      (MEM : InvMem.Rel.sem conf_src conf_tgt Mem0 Mem1 inv0)
      (STATE : InvState.Rel.sem conf_src conf_tgt
                                (mkState (mkEC CurFunction0 CurBB0 [] Terminator0 Locals0 Allocas0) ECS0 Mem0)
                                (mkState (mkEC CurFunction1 CurBB1 [] Terminator1 Locals1 Allocas1) ECS1 Mem1)
                                invst inv0 inv_term)
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
    { apply STATE. }
    { apply STATE. }
    i.
    exploit InvState.Rel.inject_value_spec; try exact COND0; eauto.
    { rewrite InvState.Unary.sem_valueT_physical. eauto. }
    i. des. rewrite InvState.Unary.sem_valueT_physical in VAL_TGT. ss.
    esplits; eauto.
  + (* return_void *)
    eapply _sim_local_return_void; eauto; ss.
    { apply STATE. }
    { apply STATE. }
  + (* br *)
    exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
    rewrite <- (ite_spec decision l0 l3) in *. simtac.
    exploit InvState.Rel.inject_value_spec; eauto.
    { rewrite InvState.Unary.sem_valueT_physical. eauto. }
    rewrite InvState.Unary.sem_valueT_physical. s. i. des.
    eapply _sim_local_step.
    {
      expl progress.
      - ss.
      - unfold OpsemPP.undefined_state in *.
        des_ifs; des; ss.
      - ii. ss.

      (* clear STATE MEM CIH. *)

      (* unfold not. ii. unfold stuck_state in H. apply H. clear H. *)
      (* destruct conf_tgt. *)
      (* move decision at bottom. *)
      (* inv H13. *)
      (* unfold switchToNewBasicBlock in H15. *)
      (* des_ifs. *)
      (* unfold getPHINodesFromBlock in *. *)
      (* inv CONF. *)
      (* inv INJECT0. ss. clarify. *)
      (* destruct CurBB0 as [label_src [phi_src cmds_src term_src]]. *)
      (* destruct CurBB1 as [label_tgt [phi_tgt cmds_tgt term_tgt]]. *)
      (* ss. clarify. *)
      (* destruct CurFunction0 as [fheader_src blocks_src]; ss. *)
      (* destruct CurFunction1 as [fheader_tgt blocks_tgt]; ss. *)
      (* destruct blocks_src as [|[label_src2 stmts_src2] blocks_src]; *)
      (*   destruct blocks_tgt as [|[label_tgt2 stmts_tgt2] blocks_tgt]; ss. *)
      (* { des_ifs. } *)
      (* destruct stmts_src2, stmts_tgt2; ss. *)



      (* repeat eexists. *)
      (* econs; eauto; cycle 2. *)
      (* - *)
      (*   unfold switchToNewBasicBlock in *. *)
      (*   (* instantiate (5:= (negb (zeq z 0))). *) *)
      (*   unfold getPHINodesFromBlock in *. *)
      (*   instantiate (2:= phinodes0). *)
      (*   exploit opsem_props.OpsemProps.getIncomingValuesForBlockFromPHINodes_eq; eauto; []; *)
      (*     intros INCOMING_EQ; des. *)
      (*   (* evar bindings look dirty, but hoisting it above the econs *) *)
      (*   (* will make below proofs to include "clear INCOMING_EQ", which is also dirty *) *)
      (*   rewrite INCOMING_EQ. *)
      (*   move Locals0 at bottom. *)
      (*   move Locals1 at bottom. *)
      (*   clear INCOMING_EQ. *)
      (*   cbn in *. *)
      (*   ad-mit. *)
      (* - *)
      (*   instantiate (1:= (negb (zeq z 0))). *)
      (*   econs; eauto. *)
      (*   move INT at bottom. *)
      (*   move INJECT at bottom. *)
      (*   move conds at bottom. *)
      (*   erewrite genericvalues_inject.simulation__eq__GV2int in INT; eauto. *)
      (* - *)
      (*   unfold valid_fdef in FDEF. *)
      (*   move FDEF at bottom. *)
      (*   move H14 at bottom. *)
      (*   replace (if negb (zeq z 0) then l0 else l3) with (ite (negb (zeq z 0)) l0 l3) by ss. *)
      (*   ss. *)
      (*   (* rewrite H14. clear H14. *) *)
      (*   (* des_if already exists *) *)
      (*   Ltac des_if_ H := *)
      (*     clarify; *)
      (*     repeat *)
      (*       match goal with *)
      (*       | H': context [match ?x with | _ => _ end] |- _ => *)
      (*         check_equal H' H; *)
      (*         match type of x with *)
      (*         | {_} + {_} => destruct x; clarify *)
      (*         | _ => let Heq := fresh "Heq" in *)
      (*                destruct x as () eqn:Heq; clarify *)
      (*         end *)
      (*       end *)
      (*   . *)
      (*   des_if_ FDEF. *)
      (*   apply andb_true_iff in FDEF. des. *)
      (*   des_bool. *)
      (*   des_sumbool; clarify. *)
      (*   move H14 at bottom. *)
      (*   unfold valid_phinodes in *. *)
      (*   des_if_ COND1. *)
      (*   des_if_ COND2. *)
      (*   des_bool; des_sumbool; clarify. *)
      (*   Ltac clear_true := *)
      (*     repeat match goal with *)
      (*            | [ H: is_true true |- _ ] => clear H *)
      (*            | [ H: True |- _ ] => clear H *)
      (*            | [ H: ?x = ?x |- _ ] => clear H *)
      (*            end. *)
      (*   clear_true. *)
      (*   unfold Debug.debug_print in *. *)

      (*   cbn in FDEF0. *)
      (*   des_if_ FDEF0; repeat (des_bool; des); des_sumbool; clarify; ss. *)
      (*   clear_true. *)

      (*   destruct (negb (zeq z 0)) eqn:T; ss. *)
      (*   { *)
      (*     destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l0 label_tgt2) eqn:T2; *)
      (*     (* destruct (l0 == label_tgt2) eqn:T2. <-- This does NOT work !! *) *)
      (*     clarify; des_sumbool; ss. *)
      (*     rewrite Heq4. *)
      (*     ad-mit. *)
      (*   } *)
      (*   { *)
      (*     destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l3 label_tgt2) eqn:T3; *)
      (*     clarify; des_sumbool; ss. *)
      (*     ad-mit. *)
      (*   } *)
    }
    i.
    expl preservation.
    inv STEP. unfold valid_phinodes in *.
    do 12 simtac0. rewrite <- (ite_spec decision0 l0 l3) in *.
    {
      move COND1 at bottom.
      move COND2 at bottom.
      rename s0 into __s0__.
      rename s into __s__.
      rewrite VAL_TGT in *. clarify.
      exploit decide_nonzero_inject_aux; eauto.
      { inv CONF. inv INJECT0. ss. subst. eauto. }
      i. subst.
      expl add_terminator_cond_br.
      rewrite lookupBlockViaLabelFromFdef_spec in *.
      exploit (lookupAL_ite fdef_hint decision0 l0 l3); eauto. clear COND7 COND3. i.
      exploit (lookupAL_ite CurFunction0.(get_blocks) decision0 l0 l3); eauto. clear COND8 COND4. i.
      exploit (lookupAL_ite CurFunction1.(get_blocks) decision0 l0 l3); eauto. clear COND9 COND5. i.
      idtac.
      unfold l in *.
      rewrite x1 in *. clarify.
      rewrite x2 in *. clarify.
      destruct decision0; inv H0; inv H1; ss.
      * exploit postcond_phinodes_sound;
          (try instantiate (1 := (mkState (mkEC _ _ _ _ _ _) _ _))); s;
            (try eexact x0; try eexact MEM0);
            (try eexact H19; try eexact H15); ss; eauto; [].
        i. des.
        exploit apply_infrules_sound; try exact STATE0; eauto; ss; []. i. des.
        exploit reduce_maydiff_sound; eauto; ss; []. i. des.
        (* exploit implies_sound; try exact COND2; eauto; ss. i. des. *)
        exploit valid_fdef_valid_stmts; eauto; []. i. des.
        esplits; eauto.


        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        { econs; ss; eauto.
          - eapply inject_allocas_inj_incr; eauto.
          - exploit implies_sound; eauto. }
      * exploit postcond_phinodes_sound;
          (try instantiate (1 := (mkState (mkEC _ _ _ _ _ _) _ _))); s;
            (try eexact x0; try eexact MEM0);
            (try eexact H19; try eexact H15); ss; eauto; [].
        i. des.
        exploit apply_infrules_sound; try exact STATE0; eauto; ss; []. i. des.
        exploit reduce_maydiff_sound; eauto; ss; []. i. des.
        (* exploit implies_sound; try exact COND11; eauto; ss. i. des. *)
        exploit valid_fdef_valid_stmts; eauto; []. i. des.
        esplits; eauto.
        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        { econs; ss; eauto.
          - eapply inject_allocas_inj_incr; eauto.
          - exploit implies_sound; eauto. }
    }
  + (* br_uncond *)
    exploit nerror_nfinal_nstuck; eauto. i. des. inv x0. simtac.
    eapply _sim_local_step.
    {
      expl progress.
      - ss.
      - unfold OpsemPP.undefined_state in *.
        des_ifs; des; ss.
      - ii. ss.
    }
    i.
    expl preservation.
    inv STEP. unfold valid_phinodes in *.
    rewrite add_terminator_cond_br_uncond in *.
    rewrite lookupBlockViaLabelFromFdef_spec in *.
    des_ifs_safe (clarify; ss).
    (* do 6 des_outest_ifs COND0. *)
    unfold Debug.debug_print in *. unfold l in *.
    rewrite Heq0 in *. clarify.
    rewrite Heq1 in *. clarify.
    exploit postcond_phinodes_sound;
      (try instantiate (1 := (mkState (mkEC _ _ _ _ _ _) _ _))); s;
        (try eexact COND4; try eexact MEM0);
        (try eexact H11; try eexact H13); ss; eauto; [] .
    i. des.
    exploit apply_infrules_sound; eauto; ss; []. i. des.
    exploit reduce_maydiff_sound; eauto; ss; []. i. des.
    exploit valid_fdef_valid_stmts; eauto; []. i. des.
    esplits; eauto.
    * econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss.
    * econs; ss; eauto; ss; eauto.
      - eapply inject_allocas_inj_incr; eauto.
      - exploit implies_sound; eauto.
  + (* switch *)
    destruct (list_const_l_dec l0 l1); ss. subst.
    exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
    exploit InvState.Rel.inject_value_spec; eauto.
    { rewrite InvState.Unary.sem_valueT_physical. eauto. }
    rewrite InvState.Unary.sem_valueT_physical. s. i. des.
    exploit get_switch_branch_inject; eauto. i.
    eapply _sim_local_step.
    {
      expl progress.
      - ss.
      - unfold OpsemPP.undefined_state in *.
        des_ifs; des; ss.
      - ii. ss.
    }
    i.
    expl preservation.
    inv STEP.
    assert (CONF_EQ: TD0 = TD /\ gl0 = gl).
    { inv CONF.
      match goal with
      | [INJ: inject_conf _ _ |- _] => inv INJ
      end. ss. }
    des. subst. ss. clarify.
    unfold valid_phinodes in *.
    unfold Debug.debug_print_validation_process in *. ss.
    unfold Debug.failwith_false in *. ss.
    unfold Debug.debug_print in *. ss.
    des_ifs_safe.
    exploit add_terminator_cond_switch; eauto. i. des.
    rewrite lookupBlockViaLabelFromFdef_spec in *.

    rewrite forallb_forall in COND2.
    exploit get_switch_branch_in_successors; eauto.
    i. unfold successors_terminator in *.
    apply nodup_In in x1. ss. des.
    { (* default *)
      subst.
      unfold l in *.
      progress all_with_term rewrite_everywhere lookupAL. clarify.
      exploit postcond_phinodes_sound; try exact x0; eauto.
      { rewrite <- LABEL. eauto. }
      i. des.
      exploit apply_infrules_sound; eauto; ss. i. des.
      exploit reduce_maydiff_sound; eauto; ss. i. des.
      exploit valid_fdef_valid_stmts; eauto. i. des.
      esplits; eauto.
      * econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss.
      * econs; ss; eauto; ss; eauto.
        - eapply inject_allocas_inj_incr; eauto.
        - exploit implies_sound; eauto.
    }
    { (* case *)
      apply list_prj2_inv in x1. des.
      expl COND2. clear COND2.
      des_ifs_safe ss. clear_tac. clarify.
      unfold l in *. cbn in *.
      clear dependent phinodes5.
      clear dependent phinodes0.
      exploit postcond_phinodes_sound; try exact x0; eauto.
      { rewrite <- LABEL. eauto. }
      i. des.
      expl apply_infrules_sound.
      expl reduce_maydiff_sound.
      expl valid_fdef_valid_stmts.
      esplits; eauto.
      * econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss.
      * econs; ss; eauto; ss; eauto.
        - eapply inject_allocas_inj_incr; eauto.
        - exploit implies_sound; eauto.
    }
  + (* unreachable *)
    exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
Unshelve.
all: destruct CONF; subst; ss.
{ clear - CMDS TERM.
  admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
{ admit. }
(* apply 0%nat. *)
(* apply 0%nat. *)
(* apply 0%nat. *)
(* ss. *)
(* apply value_id; ss. *)
(* apply 0%nat. *)
(* apply 0%nat. *)
(* Qed. *)
Admitted.

(* TODO: move to postcond.v *)
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
      eapply _sim_local_call; ss; eauto; ss.
      eexists (memory_blocks_of conf_src Locals0
                          (Invariant.unique (Invariant.src inv))),
        (memory_blocks_of conf_tgt Locals1
                          (Invariant.unique (Invariant.tgt inv))),
        (memory_blocks_of_t conf_src _ _
                          (Invariant.private (Invariant.src inv))),
        (memory_blocks_of_t conf_tgt _ _
                          (Invariant.private (Invariant.tgt inv)))
      .
      esplits.
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
        { ss.
          eapply inject_allocas_inj_incr; eauto.
          etransitivity; eauto. }
        { splits; ss.
          move WF_TGT0 at bottom.
          move RETURN_TGT at bottom.
          SearchAbout OpsemPP.wf_State.
          Lemma wf_state_mem
                conf EC ECS mem
                (WF: OpsemPP.wf_State conf (mkState EC ECS mem))
                mem'
            :
              OpsemPP.wf_State conf (mkState EC ECS mem')
          .
          Proof.
            i. ss.
          Qed.
          Lemma wf_stateI_mem
                conf EC ECS mem
                (WF: wf_StateI conf (mkState EC ECS mem))
                mem'
            :
              wf_StateI conf (mkState EC ECS mem')
          .
          Proof.
            apply wf_StateI_spec.
            apply wf_StateI_spec in WF.
            expl wf_state_mem.
          Qed.

          apply wf_StateI_spec.
          apply wf_StateI_spec in WF_TGT0.
          unfold return_locals in RETURN_TGT. des_ifs.
          - destruct conf_tgt.
            Fail eapply wf_state_mem with (mem' := Mem1). (* ERROR MESSAGE REALLY HARD TO READ *)
            eapply wf_state_mem with (mem0 := Mem1).
            (* eapply wf_stateI_mem with (mem0 := Mem1). *)
            Fail eapply OpsemPP.preservation_cmd_non_updated_case.
            (* ERROR MESSAGE REALLY HARD TO READ *)
            destruct CurTargetData0.
            eapply OpsemPP.preservation_cmd_non_updated_case; eauto.
            { reflexivity. }
            { apply wf_ConfigI_spec in WF_TGT. ss. }
          - destruct conf_tgt. destruct CurTargetData0.
            eapply OpsemPP.preservation_cmd_updated_case; [..|exact WF_TGT0]; eauto; try (by ss).
            { clear WF_TGT0. ss. rename g0 into __g0__. rename g into __g__.
              eapply OpsemPP.fit_gv_gv2gvs__wf_gvs_aux; eauto.
              Print OpsemPP.wf_ExecutionContext.
              Print OpsemPP.wf_defs.
              (* assert(OpsemPP.wf_GVs (l2, n) __g__ *)
              (* OpsemPP.lift_fit_gv__wf_gvs *)
              (* OpsemPP.fit_gv_gv2gvs__wf_gvs_aux *)
              admit. }
            { apply wf_ConfigI_spec in WF_TGT. ss. }
          - destruct conf_tgt.
            Fail eapply wf_state_mem with (mem' := Mem1). (* ERROR MESSAGE REALLY HARD TO READ *)
            eapply wf_state_mem with (mem0 := Mem1).
            (* eapply wf_stateI_mem with (mem0 := Mem1). *)
            Fail eapply OpsemPP.preservation_cmd_non_updated_case.
            (* ERROR MESSAGE REALLY HARD TO READ *)
            destruct CurTargetData0.
            eapply OpsemPP.preservation_cmd_non_updated_case; eauto.
            { reflexivity. }
            { apply wf_ConfigI_spec in WF_TGT. ss. }
        }
    + (* non-call *)
      des.
      eapply _sim_local_step.
      {
        expl progress.
        - ss.
        - move ERROR_SRC at bottom.
          apply error_state_neg in ERROR_SRC. des; ss. apply NNPP in ERROR_SRC. des.
          rename ERROR_SRC into SRC_STEP.
          rename COND0 into POSTCOND.
          move POSTCOND at bottom.
          (* inv SRC_STEP. destruct c0; ss. admit. *)
          (* exfalso. clear - COND0. unfold Postcond.postcond_cmd in COND0. des_ifs. *)
          (* cbn in COND0. *)
          destruct conf_src; ss.
          inv CONF. inv INJECT. ss. clarify.
          unfold OpsemPP.undefined_state in *.
          des_ifs_safe. des; ss; des_ifs_safe; ss.
          + des_ifs; ss.
          + exfalso.
            rename inv0 into invmem.
            rename inv into inv0.
            exploit postcond_cmd_implies_inject_event; eauto; []; intro POSTCOND_INJ; des.
            destruct c; des_ifs. ss. des_bool; des. des_sumbool. clarify.
            inv SRC_STEP.
            assert(INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) mptr0 g).
            {
              eapply InvState.Subset.inject_value_Subset in POSTCOND_INJ0; cycle 1.
              { instantiate (1:= inv0).
                etransitivity; eauto.
                { eapply SoundForgetStack.forget_stack_Subset; eauto. }
                etransitivity; eauto.
                { eapply SoundForgetMemory.forget_memory_Subset; eauto. }
                reflexivity.
              }
              exploit InvState.Rel.inject_value_spec; try exact POSTCOND_INJ0; eauto.
              { ss. }
              { rewrite InvState.Unary.sem_valueT_physical. ss. rewrite <- H17. ss. }
              i; des.
              rewrite InvState.Unary.sem_valueT_physical in *. ss. rewrite Heq in *. clarify.
            }
            admit. (* free inject. easy *)
          + admit.
          + admit.
          +
            exfalso.
            assert(SIM_PRODUCTS: AdequacyLocal.sim_products
                                   (mkCfg CurSystem0 CurTargetData0 CurProducts0 Globals0 FunTable0)
                                   (mkCfg CurSystem1 CurTargetData0 CurProducts1 Globals0 FunTable1)
                                   CurProducts0 CurProducts1).
            { admit. }
            inv SIM_PRODUCTS.
            move IS_UNDEFINED at bottom.
            rename Heq0 into LOOKUP_TGT.
            move LOOKUP_TGT at bottom.
            (* exploit AdequacyLocal.lookupExFdecViaPtr_inject; eauto. *)
            unfold lookupExFdecViaPtr, lookupFdefViaPtr in *. unfold monad.mbind in *. ss.
            des_ifs.
            admit.
            admit.
            admit.
            admit.
            (* des_ifsH LOOKUP_TGT. *)
            (* * rewrite LOOKUP_TGT in *. *)
            (*   { *)
            (*     destruct(lookupFdecViaIDFromProducts CurProducts1 i0) eqn:LOOKUP_FDEC; cycle 1. *)
            (*     { admit. (* both are None, src stuck *) } *)
            (*     destruct f; ss. *)
            (*     destruct fheader5; ss. *)
            (*     destruct (params2GVs CurTargetData0 params5 Locals1 Globals0) eqn: PARAMS_TGT; cycle 1. *)
            (*     { admit. (* Fdef none. Fdec is some, but params none *) } *)
            (*     destruct (external_intrinsics.callExternalOrIntrinsics *)
            (*                 CurTargetData0 Globals0 Mem1 id0 typ0 *)
            (*                 (args2Typs args5) deckind5 l2) eqn:EXT; cycle 1. *)
            (*     { admit. (* extcall *) } *)
            (*     des_ifs. *)
            (*     admit. (* locals *) *)
            (*   } *)
            (* * *)
        - ii. ss.
      }
      i.
      expl preservation.
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
{ admit. (* move inject_allocas to invmem? *) }
Admitted.

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
      (WF_TGT: wf_ConfigI conf_tgt)
  :
  exists ec_tgt,
    <<INIT_TGT: init_fdef conf_tgt fdef_tgt args_tgt ec_tgt>> /\
    <<SIM:
      valid_state_sim
        conf_src conf_tgt
        stack0_src stack0_tgt
        inv idx
        (mkState ec_src stack0_src mem_src)
        (mkState ec_tgt stack0_tgt mem_tgt)>>.
Proof.
  inv INIT_SRC. unfold valid_fdef in FDEF. simtac.
  exploit locals_init; eauto; [by apply CONF|apply MEM|]. i. des.
  generalize FDEF. i.
  unfold forallb2AL in FDEF0. ss. apply andb_true_iff in FDEF0. des.
  do 10 simtac0.
  assert(VALID_TERM_INFRULES: exists infrules,
            valid_terminator fdef_hint
                  (Infrules.apply_infrules m_src m_tgt infrules t) m_src m_tgt
                  ((l0, stmts_intro ps' cs' tmn') :: b0) ((l0, stmts_intro phinodes5 cmds5 terminator5) :: b1) l0 tmn'
                  terminator5).
  { simtac.
    - exists nil. assumption.
    - eexists; eassumption.
  }
  clear COND5. des.

  hexploit InvState.Rel.sem_empty; eauto.
  { instantiate (2 := mkEC _ _ _ _ _ _).
    instantiate (1 := mkEC _ _ _ _ _ _).
    s. eauto.
  }
  i. des.
  esplits.
  - econs; eauto. ss.
  - econs; eauto.
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
      rewrite COND0, COND1, COND2, COND3, COND4. ss.
    }
    {
      cbn in *.
      econs; eauto.
    }
    {
      splits; ss.
      admit.
    }
Admitted.

Lemma valid_sim_fdef
      m_src m_tgt
      conf_src conf_tgt
      fdef_src fdef_tgt
      fdef_hint
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint)
      (WF_TGT: wf_ConfigI conf_tgt)
  :
  sim_fdef conf_src conf_tgt fdef_src fdef_tgt.
Proof.
  ii.
  exploit valid_init; eauto. i. des.
  esplits; eauto.
  apply valid_sim; eauto.
Grab Existential Variables.
  { exact 0%nat. }
Qed.
