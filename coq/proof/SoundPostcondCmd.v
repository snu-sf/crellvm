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
Require Import SoundForget.
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

Lemma AtomSetImpl_spec_aux x l s
  : x `in` fold_left (flip add) l s <-> In x l \/ x `in` s.
Proof.
  split.
  - revert x s.
    induction l; eauto.
    i. ss.
    exploit IHl; eauto. i.
    unfold flip in *.
    des; eauto.
    rewrite -> AtomSetFacts.add_iff in *. des; eauto.
  - revert x s.
    induction l; i.
    + ss. des; done.
    + ss. des; (exploit IHl; [|eauto]); eauto;
            right; apply AtomSetFacts.add_iff; eauto.
Qed.
  
Lemma AtomSetImpl_from_list_spec1 x l
  : AtomSetImpl.In x (AtomSetImpl_from_list l) <-> In x l.
Proof.
  assert (EQUIV: In x l <-> In x l \/ x `in` empty).
  { split; eauto.
    i. des; eauto.
    apply AtomSetFacts.empty_iff in H. done.
  }
  rewrite EQUIV.
  apply AtomSetImpl_spec_aux.
Qed.

Lemma AtomSetImpl_from_list_spec2 x l
  : ~ AtomSetImpl.In x (AtomSetImpl_from_list l) <-> ~ In x l.
Proof.
  split; ii; apply AtomSetImpl_from_list_spec1 in H0; done.
Qed.

Lemma AtomSetImpl_singleton_mem_false x y
  : AtomSetImpl.mem x (AtomSetImpl_from_list [y]) = false -> x <> y.
Proof.
  i.
  apply AtomSetFacts.not_mem_iff in H.
  apply AtomSetImpl_from_list_spec2 in H.
  apply elim_not_In_cons in H. eauto.
Qed.

Lemma step_state_equiv_except
      conf st0 st1 evt
      cmd cmds
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP: sInsn conf st0 st1 evt)
  : state_equiv_except (AtomSetImpl_from_list (Cmd.get_def cmd))
                       (mkState st0.(EC) st0.(ECS) st1.(Mem)) st1.
Proof.
  inv STEP; ss;
    inv CMDS; econs; ss; ii;
      hexploit AtomSetImpl_singleton_mem_false; eauto; i;
        eauto using lookupAL_updateAddAL_neq.
Qed.

Ltac specialize_unique :=
  match goal with
  | [H1: AtomSetImpl.For_all (InvState.Unary.sem_unique _ _) ?inv,
         H2: AtomSetImpl.mem ?x ?inv = true |- _] =>
    apply AtomSetFacts.mem_iff in H2;
    specialize (H1 _ H2)
  end.

Lemma postcond_cmd_check_forgets_Subset
      cmd_src cmd_tgt inv0
      (COND : postcond_cmd_check
                cmd_src cmd_tgt
                (AtomSetImpl_from_list (Cmd.get_def cmd_src))
                (AtomSetImpl_from_list (Cmd.get_def cmd_tgt))
                (AtomSetImpl_from_list (Cmd.get_ids cmd_src))
                (AtomSetImpl_from_list (Cmd.get_ids cmd_tgt))
                (Forget.t
                   (AtomSetImpl_from_list (Cmd.get_def cmd_src))
                   (AtomSetImpl_from_list (Cmd.get_def cmd_tgt))
                   (ForgetMemory.t
                      (Cmd.get_def_memory cmd_src) (Cmd.get_def_memory cmd_tgt)
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
    (etransitivity; [apply forget_Subset | apply forget_memory_Subset]).
Qed.

Lemma no_leaked_unique_val_preserved
      id0 leaked inv0
      u val lc gvs
      (NO_LEAK : forall x : atom,
          AtomSetImpl.mem x (union (AtomSetImpl_from_list [id0]) leaked) = true ->
          AtomSetImpl.mem x (Invariant.unique inv0) = false)
      (MEM : AtomSetImpl.mem u (Invariant.unique inv0))
      (VAL : lookupAL GenericValue lc u = Some val)
  : lookupAL GenericValue (updateAddAL GenericValue lc id0 gvs) u = Some val.
Proof.
  assert (implies_false: false = true -> False).
  { i. inv H. }
  rewrite <- lookupAL_updateAddAL_neq; eauto.
  ii. subst.
  apply implies_false. erewrite <- NO_LEAK; eauto.
  rewrite AtomSetFacts.union_b.
  apply orb_true_iff.
  left. apply AtomSetImpl_from_list_spec. ss. eauto.
Qed.

Lemma step_unique_holds
      conf invst0 invmem1 inv0
      st0 st1 cmd cmds evt
      (WF_LOCAL_BEFORE : memory_props.MemProps.wf_lc st0.(Mem) st0.(EC).(Locals))
      (STATE: InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem))
                                 invst0 invmem1 inv0)
      (CMDS: st0.(EC).(CurCmds) = cmd::cmds)
      (STEP: sInsn conf st0 st1 evt)
      (NO_LEAK: unary_no_leaks (AtomSetImpl_from_list (Cmd.get_def cmd))
                               (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd))
                               inv0)
  : unique_holds conf st1 inv0.
Proof.
  intros u MEM.
  assert (IN: AtomSetImpl.In u (Invariant.unique inv0)).
  { apply AtomSetFacts.mem_iff; eauto. }
  unfold unary_no_leaks in *.
  inv STATE.
  exploit UNIQUE; eauto. intro UNIQUE_BEF. inv UNIQUE_BEF.

  inv STEP; destruct cmd; ss;
    try by econs; eauto.
  - (* bop *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of bop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* fbop *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* extractvalue *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* insertvalue *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* malloc *)
    admit. (* no malloc *)
  - (* alloca *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * subst. rewrite lookupAL_updateAddAL_eq in *. clarify.
        exploit WF_LOCAL_BEFORE; eauto. i.
        unfold InvState.Unary.sem_diffblock.
        des_ifs. ii. ss. clarify.
        exploit external_intrinsics.GV2ptr_inv; eauto. i. des.
        clarify. ss. des.
        exploit MemProps.malloc_result; eauto. i. subst.
        eapply Pos.lt_irrefl; eauto.
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* load *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * subst.
        rewrite lookupAL_updateAddAL_eq in *. clarify.
        eapply MEM0; eauto.
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* gep *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* trunc *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* ext *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* cast *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* icmp *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* fcmp *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - (* select *)
    econs; eauto.
    + ss. inv CMDS. eapply no_leaked_unique_val_preserved; eauto.
    + i. ss.
      destruct (id_dec id0 reg).
      * admit. (* res of fbop not producing unique-ptr *)
      * eapply LOCALS; eauto.
        erewrite lookupAL_updateAddAL_neq; eauto.
  - admit. (* no call *)
  - admit. (* no call *)
Admitted.

Lemma step_wf_lc
      conf st0 st1 evt
      cmd cmds
      (WF_MEM: MemProps.wf_Mem conf.(CurTargetData) st0.(Mem))
      (WF_LC: MemProps.wf_lc st0.(Mem) st0.(EC).(Locals))
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd :: cmds)
      (NONCALL_SRC: Instruction.isCallInst cmd = false)
  : <<WF_LOCAL: MemProps.wf_lc st1.(Mem) st1.(EC).(Locals)>> /\
    <<WF_MEM: MemProps.wf_Mem conf.(CurTargetData) st1.(Mem)>>.
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
  - split; auto. (* load *)
    ii. destruct (id_dec id0 id1).
    + subst. rewrite lookupAL_updateAddAL_eq in *. clarify. ss. eauto.
    + rewrite <- lookupAL_updateAddAL_neq in *; eauto.
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

  (* forget-unique *)
  exploit forget_unique_sound; eauto. intro STATE_FORGET_UNIQUE. des.

  (* forget-memory *)
  exploit forget_memory_sound; eauto.
  { ss. apply forget_unique_unary_no_leaks. }
  { ss. apply forget_unique_unary_no_leaks. }
  { unfold postcond_cmd_check in COND_INIT.
    des_ifs. des_bool. eauto. }
  i. des.
  rename STATE0 into STATE_FORGET_MEMORY.
  rename MEM0 into MEM_FORGET_MEMORY.
  (* forget *)
  exploit forget_sound; eauto.
  { hexploit step_state_equiv_except; try exact CMDS_SRC; eauto. }
  { hexploit step_state_equiv_except; try exact CMDS_TGT; eauto. }
  { inv STATE_FORGET_MEMORY.
    hexploit step_unique_holds; try exact STEP_SRC; eauto.
    { inv STATE. inv SRC0. eauto. }
    eapply unary_no_leaks_Subset.
    - exploit forget_memory_Subset; eauto. intro SUBSET.
      inv SUBSET. apply SUBSET_SRC.
    - ss. apply forget_unique_unary_no_leaks.
  }
  { inv STATE_FORGET_MEMORY.
    hexploit step_unique_holds; try exact STEP_TGT; eauto.
    { inv STATE. inv TGT0. eauto. }
    eapply unary_no_leaks_Subset.
    - exploit forget_memory_Subset; eauto. intro SUBSET.
      inv SUBSET. apply SUBSET_TGT.
    - ss. apply forget_unique_unary_no_leaks.
  }
  { eapply step_wf_lc; try exact STEP_SRC; eauto.
    - inv MEM. inv SRC. eauto.
    - inv STATE. inv SRC. eauto. }
  { eapply step_wf_lc; try exact STEP_TGT; eauto.
    - inv MEM. inv TGT. eauto.
    - inv STATE. inv TGT. eauto. }
  i. des.
Admitted.
