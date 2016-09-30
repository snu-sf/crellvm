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
Lemma AtomSetImpl_from_list_spec1 x l
  : AtomSetImpl.In x (AtomSetImpl_from_list l) <-> In x l.
Proof.
Admitted.

Lemma AtomSetImpl_from_list_spec2 x l
  : ~ AtomSetImpl.In x (AtomSetImpl_from_list l) <-> ~ In x l.
Proof.
Admitted.

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
                       st0 (mkState st1.(EC) st1.(ECS) st0.(Mem)).
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

Lemma step_unique_preserved_except
      conf st0 st1 evt inv0
      cmd cmds
      (STATE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf st0)
                                  inv0.(Invariant.unique))
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : unique_preserved_except conf inv0 (mkState st1.(EC) st1.(ECS) st0.(Mem))
                            (AtomSetImpl_from_list (Cmd.get_def cmd))
                            (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd)).
Proof.
  inv STEP; ss.
  {
    inv CMDS.
    ii.

    apply AtomSetFacts.mem_iff in MEM.
    specialize (STATE _ MEM).

    inv STATE. ss.
    econs; ss; eauto.
  }
  {
    inv CMDS.
    ii.
    rewrite AtomSetFacts.union_b in NO_LEAK. ss.
    solve_des_bool.
    apply AtomSetImpl_singleton_mem_false in NO_LEAK.

    specialize_unique.
    inv STATE.

    econs; ss.
    - rewrite <- lookupAL_updateAddAL_neq; eauto.
    - i.
      destruct (id_dec id0 reg).
      + admit.
      + exploit LOCALS; eauto.
        rewrite <- lookupAL_updateAddAL_neq in *; eauto.
    - i. eauto.
  }
  (* TODO: result of inst not containing unique *)
Admitted.

Lemma step_equiv_except_mem
      conf st0 st1 evt
      cmd cmds invst
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS: CurCmds st0.(EC) = cmd :: cmds)
      (STEP: sInsn conf st0 st1 evt)
  : state_equiv_except_mem conf
                           (option_ptr_to_genericvalue conf (mkState st1.(EC) st1.(ECS) st0.(Mem))
                                                       invst (Cmd.get_def_memory cmd))
                           (mkState st1.(EC) st1.(ECS) st0.(Mem)) st1.
Proof.
    inv STEP; ss.
    { econs.
      - ss.
      - ss.
        i. (* TODO: malloc and mload *)
        admit.
    }
    { econs.
      - ss.
      - ss. i.
        unfold mload in *. des_ifs.
        (* mload after free: use Memory.Mem.load_alloc_other. *)
        admit.
    }
    { admit. (* mload after alloca *)
    }
    { admit. (* mload after store *) }
    { inv CMDS. ss. }
Admitted.

Lemma step_unique_preserved_mem
      conf st0 st1 evt
      cmd cmds inv0
      (STATE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf (mkState st1.(EC) st1.(ECS) st0.(Mem)))
                                  inv0.(Invariant.unique))
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS: CurCmds st0.(EC) = cmd :: cmds)
      (STEP: sInsn conf st0 st1 evt)
      (LEAKED_NOT_UNIQUE: AtomSetImpl.disjoint inv0.(Invariant.unique) (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd)))
  : unique_preserved_mem conf st1 inv0.
Proof.
  inv STEP; ss;
    try (inv CMDS; ss;
         ii; specialize_unique; eauto).
  { admit. (* load malloc -> undef *) }
  { admit. (* load after free: use Memory.Mem.load_free_2 maybe *) }
  { admit. (* load alloca *) }
  { admit. (* load after store *) }
Admitted.

Lemma postcond_cmd_sound
      conf_src st0_src cmd_src cmds_src
      conf_tgt st0_tgt cmd_tgt cmds_tgt
      invst0 invmem0 inv0
      st1_tgt evt inv1
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
  exploit nerror_nfinal_nstuck; eauto. intros [st1_src]. i. des.
  replace e with evt in *; cycle 1.
  { unfold postcond_cmd_check in COND. simtac.
    exploit (@noncall_event conf_src); eauto. i.
    exploit (@noncall_event conf_tgt); eauto. i.
    subst. ss.
  }
  exploit forget_sound; eauto.
  { hexploit step_state_equiv_except; try exact CMDS_SRC; eauto. }
  { hexploit step_state_equiv_except; try exact CMDS_TGT; eauto. }
  { inv STATE. inv SRC. hexploit step_unique_preserved_except; try exact CMDS_SRC; eauto. }
  { inv STATE. inv TGT. hexploit step_unique_preserved_except; try exact CMDS_TGT; eauto. }
  intro STATE_FORGET. des.
  exploit forget_memory_sound; try exact STATE_FORGET; eauto.
  { hexploit step_equiv_except_mem; try exact NONCALL_SRC; eauto. }
  { hexploit step_equiv_except_mem; try exact NONCALL_TGT; eauto. }
  { inv STATE_FORGET.
    hexploit step_unique_preserved_mem; try exact NONCALL_SRC; inv SRC; eauto.
    apply forget_unique_leak_disjoint.
  }
  { inv STATE_FORGET.
    hexploit step_unique_preserved_mem; try exact NONCALL_TGT; inv TGT; eauto.
    apply forget_unique_leak_disjoint.
  }
  i. des.
  (* TODO: add lessdef_add *)
Admitted.
