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
                            (AtomSetImpl.union (AtomSetImpl_from_list (Cmd.get_def cmd))
                                               (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd))).
Proof.
  inv STEP; ss.
  { inv CMDS.
    ii. apply AtomSetFacts.mem_iff in MEM.
    specialize (STATE _ MEM).
    inv STATE. ss.
    econs; ss; eauto.
  }
  { inv CMDS.
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
      + admit. (* bop: operand not unique => result not unique *)
        (* TODO: result of inst not containing unique *)
        (* can believe it even without proofs *)
      + exploit LOCALS; eauto.
        rewrite <- lookupAL_updateAddAL_neq in *; eauto.
    - i. eauto.
  }
Admitted.

Lemma postcond_cmd_check_forgets_Subset
      cmd_src cmd_tgt inv0
      (COND : postcond_cmd_check
                cmd_src cmd_tgt
                (AtomSetImpl_from_list (Cmd.get_def cmd_src))
                (AtomSetImpl_from_list (Cmd.get_def cmd_tgt))
                (AtomSetImpl_from_list (Cmd.get_ids cmd_src))
                (AtomSetImpl_from_list (Cmd.get_ids cmd_tgt))
                (ForgetMemory.t (Cmd.get_def_memory cmd_src) (Cmd.get_def_memory cmd_tgt)
                                (Forget.t (AtomSetImpl_from_list (Cmd.get_def cmd_src))
                                          (AtomSetImpl_from_list (Cmd.get_def cmd_tgt))
                                          (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd_src))
                                          (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd_tgt)) inv0)) = true)
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
    (etransitivity; [eapply forget_memory_Subset | eapply forget_Subset]).
Qed.

Lemma step_unique_preserved_mem
      conf st0 st1 evt
      cmd cmds inv0
      (STATE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf (mkState st1.(EC) st1.(ECS) st0.(Mem)))
                                  inv0.(Invariant.unique))
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS: CurCmds st0.(EC) = cmd :: cmds)
      (STEP: sInsn conf st0 st1 evt)
      (UNIQUE_NOT_LEAKED: forall x (MEM:AtomSetImpl.mem x inv0.(Invariant.unique) = true),
                                 AtomSetImpl.mem x (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd)) = false)
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
  i. des.
  (* forget-memory *)
  exploit postcond_cmd_check_forgets_Subset; eauto. intro CHECK_BEFORE_FORGET.
  unfold postcond_cmd_check in CHECK_BEFORE_FORGET. des_ifs.
  match goal with
  | [H: negb (postcond_cmd_inject_event _ _ _) = false |- _] =>
    rename H into INJECT_EVENT;
      apply negb_false_iff in INJECT_EVENT
  end.
  hexploit forget_memory_sound; try exact MEM; eauto; eauto.
  { hexploit step_state_equiv_except; try exact CMDS_SRC; eauto.
    intro ST_EQ. inv ST_EQ. ss. }
  { hexploit step_state_equiv_except; try exact CMDS_TGT; eauto.
    intro ST_EQ. inv ST_EQ. ss. }
  { ss. inv STATE_FORGET. inv SRC.
    eapply step_unique_preserved_mem; try exact NONCALL_SRC; eauto.
    i. exploit forget_unique_no_leaks; ss; eauto.
    i. des. eauto. }
  { ss. inv STATE_FORGET. inv TGT.
    eapply step_unique_preserved_mem; try exact NONCALL_TGT; eauto.
    i. exploit forget_unique_no_leaks; ss; eauto.
    i. des. eauto. }
  i. des.
  (* TODO: add lessdef_add *)
Admitted.
