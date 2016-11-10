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
Require Import memory_props.

Require Import sflib.
Require Import paco.
Import Opsem.

Require Import TODO.
Require Import Exprs.
Require Import Hints.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.
Require Import SoundForgetStack.
Require Import SoundForgetMemory.
Require Import SoundPostcondCmdAdd.

Set Implicit Arguments.


Lemma postcond_cmd_is_call
      c_src c_tgt inv1 inv2
      (POSTCOND: Postcond.postcond_cmd c_src c_tgt inv1 = Some inv2):
  Instruction.isCallInst c_src = Instruction.isCallInst c_tgt.
Proof.
  unfold
    Postcond.postcond_cmd,
  Postcond.postcond_cmd_check in *.
  destruct c_src, c_tgt; ss; des_ifs.
Qed.

Lemma noncall_event
      conf st0 st1 evt cmd cmds
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd::cmds)
      (NONCALL: Instruction.isCallInst cmd = false):
  evt = events.E0.
Proof.
  inv STEP; ss. inv CMDS. ss.
Qed.

(* TODO: move this *)

Lemma postcond_cmd_check_forgets_Subset
      cmd_src cmd_tgt inv0
      (COND : postcond_cmd_check
                cmd_src cmd_tgt
                (AtomSetImpl_from_list (Cmd.get_def cmd_src))
                (AtomSetImpl_from_list (Cmd.get_def cmd_tgt))
                (AtomSetImpl_from_list (Cmd.get_ids cmd_src))
                (AtomSetImpl_from_list (Cmd.get_ids cmd_tgt))
                (ForgetStack.t
                   (AtomSetImpl_from_list (Cmd.get_def cmd_src))
                   (AtomSetImpl_from_list (Cmd.get_def cmd_tgt))
                   (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd_src))
                   (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd_tgt))
                   (ForgetMemory.t
                      (Cmd.get_def_memory cmd_src) (Cmd.get_def_memory cmd_tgt)
                      (Cmd.get_leaked_ids_to_memory cmd_src) (Cmd.get_leaked_ids_to_memory cmd_tgt)
                      inv0)) = true)
  : postcond_cmd_check
      cmd_src cmd_tgt
      (AtomSetImpl_from_list (Cmd.get_def cmd_src))
      (AtomSetImpl_from_list (Cmd.get_def cmd_tgt))
      (AtomSetImpl_from_list (Cmd.get_ids cmd_src))
      (AtomSetImpl_from_list (Cmd.get_ids cmd_tgt))
      inv0 = true.
Proof.
  unfold postcond_cmd_check in *.
  des_ifs.
  clear -Heq1 Heq2.
  rename Heq1 into INJECT_F. rename Heq2 into INJECT_T.
  apply negb_false_iff in INJECT_T.
  apply negb_true_iff in INJECT_F.
  exploit postcond_cmd_inject_event_Subset; eauto;
    (etransitivity; [apply forget_stack_Subset | apply forget_memory_Subset]).
Qed.

Lemma step_wf_lc
      gmax conf st0 st1 evt
      cmd cmds
      (WF_MEM: MemProps.wf_Mem gmax conf.(CurTargetData) st0.(Mem))
      (WF_LC: MemProps.wf_lc st0.(Mem) st0.(EC).(Locals))
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd :: cmds)
      (NONCALL_SRC: Instruction.isCallInst cmd = false)
  : <<WF_LOCAL: MemProps.wf_lc st1.(Mem) st1.(EC).(Locals)>> /\
    <<WF_MEM: MemProps.wf_Mem gmax conf.(CurTargetData) st1.(Mem)>>.
Proof.
  inv STEP; destruct cmd; ss;
    try (split; [apply MemProps.updateAddAL__wf_lc; eauto; [] | by auto]).
  - admit. (* bop *)
  - admit. (* fbop *)
  - admit. (* extractvalue *)
  - admit. (* insertvalue *)
  - admit. (* malloc *)
  - split. (* free *)
    + eapply MemProps.free_preserves_wf_lc; eauto.
    + eapply MemProps.free_preserves_wf_Mem; eauto.
  - split. (* alloca *)
    + exploit malloc_result; eauto. i. des.
      ii. destruct (id_dec id0 id1).
      * subst.
        rewrite lookupAL_updateAddAL_eq in *. clarify. ss.
        split; auto.
        rewrite NEXT_BLOCK. apply Plt_succ.
      * rewrite <- lookupAL_updateAddAL_neq in *; eauto.
        eapply MemProps.malloc_preserves_wf_lc_in_tail; eauto.
    + eapply MemProps.malloc_preserves_wf_Mem; eauto.
  - unfold MemProps.wf_Mem in *. des.
    eapply WF_MEM; eauto.
  - (* store *)
    split.
    + eapply MemProps.mstore_preserves_wf_lc; eauto.
    + admit. (* store preserves wf_Mem when stored value is from lc and wf_lc holds *)
  - admit. (* gep *)
  - admit. (* trunc *)
  - admit. (* extop *)
  - admit. (* cast *)
  - admit. (* icmp: always bool *)
  - admit. (* fcmp *)
  - destruct decision.
    + destruct v1.
      * eapply WF_LC; eauto.
      * admit. (* wf_const *)
    + destruct v2.
      * eapply WF_LC; eauto.
      * admit. (* wf_const *)
Admitted.

Lemma postcond_cmd_sound
      m_src conf_src st0_src cmd_src cmds_src
      m_tgt conf_tgt st0_tgt cmd_tgt cmds_tgt
      invst0 invmem0 inv0
      st1_tgt evt inv1
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (POSTCOND: Postcond.postcond_cmd cmd_src cmd_tgt inv0 = Some inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt)
      (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
      (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false)
      (NERROR_SRC: ~ error_state conf_src st0_src):
  exists st1_src invst1 invmem1,
    <<STEP_SRC: sInsn conf_src st0_src st1_src evt>> /\
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1 inv1>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  exploit postcond_cmd_is_call; eauto. i.
  unfold postcond_cmd in *. simtac.
  match goal with
  | [H: Instruction.isCallInst cmd_src = false |- _] =>
    rename H into NONCALL_SRC
  end.

  destruct (s_isFinialState conf_src st0_src) eqn:FINAL.
  { unfold s_isFinialState in FINAL. simtac. }
  exploit nerror_nfinal_nstuck; eauto. intros [st1_src]. intros [evt_src STEP_SRC].
  replace evt_src with evt in *; cycle 1.
  { unfold postcond_cmd_check in COND. simtac.
    exploit (@noncall_event conf_src); eauto. i.
    exploit (@noncall_event conf_tgt); eauto. i.
    subst. ss.
  }
  exploit postcond_cmd_check_forgets_Subset; eauto. intro COND_INIT.

  (* forget-memory *)
  exploit forget_memory_sound; eauto.
  { unfold postcond_cmd_check in COND_INIT.
    des_ifs. des_bool. eauto. }
  i. des.
  rename STATE0 into STATE_FORGET_MEMORY.
  rename MEM0 into MEM_FORGET_MEMORY.

  (* forget *)
  exploit forget_stack_sound; eauto.
  { hexploit step_state_equiv_except; try exact CMDS_SRC; eauto. }
  { hexploit step_state_equiv_except; try exact CMDS_TGT; eauto. }
  { ss. eapply step_unique_preserved_except; try exact CMDS_SRC; eauto.
    - inv STATE_FORGET_MEMORY. ss. inv SRC. ss.
    - inv STATE. inv SRC.
      i. hexploit UNIQUE_PARENT_LOCAL; eauto. i.
      inv MEMLE. inv SRC. rewrite <- UNIQUE_PARENT_EQ. eauto. }
  { eapply step_unique_preserved_except; try exact CMDS_TGT; eauto.
    - inv STATE_FORGET_MEMORY. inv TGT. eauto.
    - inv STATE. inv TGT.
      i. hexploit UNIQUE_PARENT_LOCAL; eauto. i.
      inv MEMLE. inv TGT. rewrite <- UNIQUE_PARENT_EQ. eauto. }
  { eapply step_wf_lc; try exact STEP_SRC; eauto.
    - inv MEM. inv SRC. eauto.
    - inv STATE. inv SRC. eauto. }
  { eapply step_wf_lc; try exact STEP_TGT; eauto.
    - inv MEM. inv TGT. eauto.
    - inv STATE. inv TGT. eauto. }
  i. des.

  hexploit postcond_cmd_add_sound; try apply CONF; try eapply STEP_SRC;
    try eapply STEP_TGT; try apply x1; (* needed to prohibit applying STATE *) eauto; []; ii; des.
  esplits; eauto.
  etransitivity; eauto.
Qed.
