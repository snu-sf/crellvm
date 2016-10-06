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
      + admit. (* bop: operand not unique => result not unique *)
        (* TODO: result of inst not containing unique *)
        (* can believe it even without proofs *)
      + exploit LOCALS; eauto.
        rewrite <- lookupAL_updateAddAL_neq in *; eauto.
    - i. eauto.
  }
Admitted.

Lemma step_equiv_except_mem
      conf st0 st1 evt
      cmd cmds
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS: CurCmds st0.(EC) = cmd :: cmds)
      (STEP: sInsn conf st0 st1 evt)
  : exists mc,
    <<MEM_CH_REL:mem_change_rel conf st0 mc cmd>> /\
    <<STATE_EQUIV: state_equiv_except_mem conf (mkState st1.(EC) st1.(ECS) st0.(Mem)) st1 mc>>.
Proof.
  inv STEP; destruct cmd; inv CMDS; ss;
    try by esplits; eauto; econs; eauto; econs; eauto.
Qed.

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

Lemma mem_change_rel_state_transition
      conf st0 st1 evt cmd cmds mc
      (CMD: CurCmds (EC st0) = cmd :: cmds)
      (NONCALL: Instruction.isCallInst cmd = false)
      (STEP: sInsn conf st0 st1 evt)
      (MEM_CH_rel: mem_change_rel conf st0 mc cmd)
  : mem_change_rel2 conf {| EC := EC st1; ECS := ECS st1; Mem := Mem st0 |} mc cmd.
Proof.
  destruct cmd; ss;
    inv STEP; ss;
      des; esplits; eauto.
Qed.

Ltac exploit_inject_value :=
  repeat (match goal with
       | [H1: Invariant.inject_value ?inv ?vt1 ?vt2 = true |- _] =>
         exploit InvState.Rel.inject_value_spec; try exact H1; eauto; clear H1
       end;
       (try by
           match goal with
           | [H: getOperandValue (CurTargetData ?conf) ?v (Locals (EC ?st)) (Globals ?conf) = Some ?gv1 |-
              InvState.Unary.sem_valueT ?conf ?st ?invst (ValueT.lift Tag.physical ?v) = Some ?gv2] =>
             destruct v; [ss; unfold IdT.lift; solve_sem_idT; eauto | ss]
           end); i; des).

Ltac inv_conf :=
  match goal with
  | [H: InvState.valid_conf ?m_src ?m_tgt ?conf_src ?conf_tgt |- _] =>
    let TD := fresh in
    let GL := fresh in
    destruct H as [[TD GL]]; rewrite TD in *; rewrite GL in *
  end.

Ltac inject_clarify :=
  repeat
    match goal with
    | [H1: getTypeAllocSize ?TD ?ty = Some ?tsz1,
           H2: getTypeAllocSize ?TD ?ty = Some ?tsz2 |- _] =>
      rewrite H1 in H2; inv H2
    | [H: proj_sumbool ?dec = true |- _] =>
      destruct dec; ss; subst
    | [H1: getOperandValue (CurTargetData ?conf) ?v (Locals (EC ?st)) ?GL = Some ?gv1,
           H2: InvState.Unary.sem_valueT ?conf ?st ?invst (ValueT.lift Tag.physical ?v) =
               Some ?gv2 |- _] =>
      let Hnew := fresh in
      assert (Hnew: InvState.Unary.sem_valueT conf st invst (ValueT.lift Tag.physical v) = Some gv1);
      [ destruct v; [ss; unfold IdT.lift; solve_sem_idT; eauto | ss] | ];
      rewrite Hnew in H2; clear Hnew; inv H2
    | [H1: getOperandValue (CurTargetData ?conf) (value_id ?x) (Locals (EC ?st)) ?GL = Some ?gv1 |-
       InvState.Unary.sem_idT ?st ?invst (Tag.physical, ?x) = Some ?gv2] =>
      let Hnew := fresh in
      assert (Hnew: InvState.Unary.sem_idT st invst (Tag.physical, x) = Some gv1); [ss|];
      apply Hnew; clear Hnew
    end.

Lemma inject_event_implies_mem_change_inject
      m_src conf_src st0_src mc_src cmd_src
      m_tgt conf_tgt st0_tgt mc_tgt cmd_tgt
      invst0 invmem0 inv0
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM : InvMem.Rel.sem conf_src conf_tgt (Mem st0_src) (Mem st0_tgt) invmem0)
      (INJECT: postcond_cmd_inject_event cmd_src cmd_tgt inv0 = true)
      (MEM_CH_REL_SRC: mem_change_rel conf_src st0_src mc_src cmd_src)
      (MEM_CH_REL_TGT: mem_change_rel conf_tgt st0_tgt mc_tgt cmd_tgt)
  : mem_change_inject conf_src conf_tgt invmem0 mc_src mc_tgt.
Proof.
  destruct cmd_src; destruct cmd_tgt; ss;
    (try by des; subst; econs); des; subst; simtac;
      (try by exploit_inject_value; inv_conf; inject_clarify; econs; eauto).
  unfold Invariant.is_private in *. des_ifs.
  destruct x as [t x]; unfold ValueT.lift in *. des_ifs.
  inv STATE. inv SRC.
  exploit PRIVATE.
  { apply IdTSet.mem_2; eauto. }
  { inv_conf.
    inject_clarify.
  }
  i. des_ifs.
  econs; eauto.
Qed.

(* TODO: move *)


Lemma inject_value_monotone
      v1 def_mem_src def_src use_src
      v2 def_mem_tgt def_tgt use_tgt
      inv0
      (INJECT: Invariant.inject_value
                 (ForgetMemory.t def_mem_src def_mem_tgt
                                 (Forget.t def_src def_tgt use_src use_tgt inv0)) v1 v2)
  : Invariant.inject_value inv0 v1 v2.
Proof.
  eapply inject_value_forget_monotone; eauto.
  eapply inject_value_forget_memory_monotone; eauto.
Qed.

Lemma postcond_cmd_check_monotone
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
  destruct cmd_src; destruct cmd_tgt; ss.
  - apply ExprPairSet.exists_2 in INJECT_T; try by solve_compat_bool.
    inv INJECT_T. des.
    apply ExprPairSet.filter_1 in H; try by solve_compat_bool.
    exploit ExprPairSet.exists_1; try by solve_compat_bool.
    unfold ExprPairSet.Exists.
    esplits; eauto.
  - simtac.
    inject_clarify.
    rewrite andb_true_r in *.
    exploit inject_value_forget_monotone; eauto.
  - simtac.
    exploit inject_value_monotone; eauto.
  - simtac.
    inject_clarify.
    rewrite andb_true_r in *.
    exploit inject_value_forget_monotone; eauto.
  - simtac.
    inject_clarify.
    rewrite andb_true_r in *.
    exploit inject_value_forget_monotone; eauto.
  - unfold Invariant.is_private in *. des_ifs.
    + ss. unfold ForgetMemory.unary in *.
      des_ifs; ss;
        unfold Forget.unary in *;
        rewrite IdTSetFacts.filter_b in INJECT_T; try by solve_compat_bool; clarify.
    + ss.
      rewrite IdTSetFacts.filter_b in INJECT_T; try by solve_compat_bool; clarify.
  - simtac.
    repeat solve_des_bool; clarify.
    + exploit inject_value_monotone; try exact H2; eauto.
    + exploit inject_value_monotone; try exact H0; eauto.
  - simtac.
    + solve_des_bool.
      * exploit inject_value_forget_monotone; eauto.
      * exploit list_forallb2_spec.
        { apply H0. }
        { instantiate
            (1:=(fun p1 p2 => let
                     '(_, attr1, v1) := p1 in
                   let
                     '(_, attr2, v2) := p2 in
                   attributes_dec attr1 attr2 &&
                   Invariant.inject_value inv0
                   (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))).
          i. ss.
          destruct a1. destruct a2.
          destruct p. destruct p0.
          simtac.
          exploit inject_value_forget_monotone; eauto. i.
          des_ifs.
        }
        i. clarify.
    + solve_des_bool.
      * exploit inject_value_forget_monotone; eauto.
      * exploit list_forallb2_spec.
        { apply H0. }
        { instantiate
            (1:=(fun p1 p2 => let
                     '(_, attr1, v1) := p1 in
                   let
                     '(_, attr2, v2) := p2 in
                   attributes_dec attr1 attr2 &&
                   Invariant.inject_value inv0
                   (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))).
          i. ss.
          destruct a1. destruct a2.
          destruct p. destruct p0.
          simtac.
          exploit inject_value_forget_monotone; eauto. i.
          des_ifs.
        }
        i. clarify.
Qed.

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
  intro STATE_FORGET. des.
  hexploit step_equiv_except_mem; try exact NONCALL_SRC; eauto. i. des.
  hexploit step_equiv_except_mem; try exact NONCALL_TGT; eauto. i. des.
  exploit forget_memory_sound; try exact STATE_FORGET; eauto.
  { eapply mem_change_rel_state_transition; eauto. }
  { eapply mem_change_rel_state_transition; eauto. }
  { exploit inject_event_implies_mem_change_inject; try exact STATE; eauto.
    exploit postcond_cmd_check_monotone; eauto. i.
    unfold postcond_cmd_check in *. des_ifs.
    apply negb_false_iff. eauto.
  }
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
