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
Require Import Hints.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.
Require Import SoundForgetStackCall.
Require Import SoundForgetMemoryCall.
Require Import SoundPostcondCmdAdd.
Require Import opsem_wf.
Require Import memory_props.
Import OpsemPP.

Set Implicit Arguments.


Lemma postcond_cmd_inject_event_call
      m_src conf_src st0_src cmds_src
      m_tgt conf_tgt st0_tgt cmds_tgt
      id_src fun_src args_src noret_src clattrs_src typ_src varg_src
      id_tgt fun_tgt args_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt
      invst0 invmem0 inv0
      (CONF : InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM : InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = (insn_call id_src noret_src clattrs_src typ_src varg_src fun_src args_src) :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = (insn_call id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt args_tgt) :: cmds_tgt)
      (INJECT_EVENT: postcond_cmd_inject_event
                       (insn_call id_src noret_src clattrs_src typ_src varg_src fun_src args_src)
                       (insn_call id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt args_tgt) inv0)
  : <<NORET: noret_src = noret_tgt>> /\
    <<CLATTRS: clattrs_src = clattrs_tgt>> /\
    <<TYP: typ_src = typ_tgt>> /\
    <<VARG: varg_src = varg_tgt>> /\
    <<FUN:
      forall funval2_src
        (FUN_SRC: getOperandValue conf_src.(CurTargetData) fun_src st0_src.(EC).(Locals) conf_src.(Globals) = Some funval2_src),
      exists funval1_tgt,
        <<FUN_TGT: getOperandValue conf_tgt.(CurTargetData) fun_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some funval1_tgt>> /\
        <<INJECT: genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject) funval2_src funval1_tgt>>>> /\
  <<ARGS:
    forall args2_src
      (ARGS_SRC: params2GVs (conf_src.(CurTargetData))
                            args_src st0_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
    exists args1_tgt,
      (<<ARGS_TGT: params2GVs (conf_tgt.(CurTargetData)) args_tgt
                             st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>>) /\
      (<<INJECT: list_forall2 (genericvalues_inject.gv_inject
                                 invmem0.(InvMem.Rel.inject)) args2_src args1_tgt>>) /\
      (<<VALID_SRC: List.Forall (MemProps.valid_ptrs (Memory.Mem.nextblock st0_src.(Mem))) args2_src>>) /\
      (<<VALID_TGT: List.Forall (MemProps.valid_ptrs (Memory.Mem.nextblock st0_tgt.(Mem))) args1_tgt>>)
        >>
.
Proof.
  ss. unfold is_true in *.
  repeat (des_bool; des).
  des_sumbool. subst.
  esplits; auto.
  { (* funval *)
    i.
    exploit InvState.Rel.inject_value_spec; eauto.
    { rewrite InvState.Unary.sem_valueT_physical. eauto. }
    i. des.
    esplits; eauto.
    erewrite <- InvState.Unary.sem_valueT_physical. eauto.
  }
  { (* args *)
    clear -CONF STATE MEM INJECT_EVENT0.
    revert dependent args_tgt.
    induction args_src.
    - i. ss. des_ifs.
      esplits; ss; econs.
    - i. destruct args_tgt; ss.
      destruct a as [[ty_s attr_s] val_s].
      destruct p as [[ty_t attr_t] val_t].
      repeat (des_bool; des).
      des_sumbool. subst.

      des_ifs; cycle 1.
      + exploit IHargs_src; eauto. i. des. congruence.
      + exploit InvState.Rel.inject_value_spec; eauto.
        { rewrite InvState.Unary.sem_valueT_physical. eauto. }
        rewrite InvState.Unary.sem_valueT_physical. i. des. congruence.
      + exploit IHargs_src; eauto. i. des.
        esplits; eauto.
        * clarify.
          econs; eauto.
          exploit InvState.Rel.inject_value_spec; eauto.
          { rewrite InvState.Unary.sem_valueT_physical. eauto. }
          rewrite InvState.Unary.sem_valueT_physical. i. des. clarify.
        * econs; eauto.
          eapply get_operand_valid_ptr; eauto; try apply STATE; try apply MEM.
        * rewrite Heq0 in *. clarify.
          econs; eauto.
          eapply get_operand_valid_ptr; eauto; try apply STATE; try apply MEM.
  }
Qed.

Lemma postcond_cmd_add_lessdef_call
      id noret clattrs typ varg funval args s
  : postcond_cmd_add_lessdef (insn_call id noret clattrs typ varg funval args) s =
    if noret then s else
      Exprs.ExprPairSet.add
        (Exprs.Expr.value (Exprs.ValueT.const (const_undef typ)),
         Exprs.Expr.value (Exprs.ValueT.id (Exprs.Tag.physical, id)))
        s
.
Proof.
  unfold postcond_cmd_add_lessdef, postcond_cmd_get_lessdef. ss.
  destruct noret; eauto.
Qed.

Lemma postcond_cmd_add_noret_call
      id_src fun_src args_src
      id_tgt fun_tgt args_tgt
      clattrs typ varg inv
  : postcond_cmd_add (insn_call id_src true clattrs typ varg fun_src args_src)
                     (insn_call id_tgt true clattrs typ varg fun_tgt args_tgt) inv =
    reduce_maydiff inv.
Proof.
  destruct inv. destruct src. destruct tgt. ss.
Qed.

Lemma postcond_cmd_add_ret_call
      id_src fun_src args_src
      id_tgt fun_tgt args_tgt
      clattrs typ varg inv
  : postcond_cmd_add (insn_call id_src false clattrs typ varg fun_src args_src)
                     (insn_call id_tgt false clattrs typ varg fun_tgt args_tgt) inv =
    reduce_maydiff
      (Invariant.update_tgt
         (Invariant.update_lessdef
            (Exprs.ExprPairSet.add
               (Exprs.Expr.value (Exprs.ValueT.const (const_undef typ)),
                Exprs.Expr.value (Exprs.ValueT.id (Exprs.Tag.physical, id_tgt)))))
         (Invariant.update_src
            (Invariant.update_lessdef
               (Exprs.ExprPairSet.add
                  (Exprs.Expr.value (Exprs.ValueT.const (const_undef typ)),
                   Exprs.Expr.value (Exprs.ValueT.id (Exprs.Tag.physical, id_src)))))
                                     (remove_def_from_maydiff id_src id_tgt inv))).
Proof. ss. Qed.

Lemma updateAddAL_lessdef_undef
      conf st invst invmem gmax public inv
      locals id gv typ
      (LOCALS : updateAddAL GenericValue locals id gv = Locals (EC st))
      (STATE : InvState.Unary.sem conf st invst invmem gmax public inv)
      (CHUNK: exists mcs, flatten_typ conf.(CurTargetData) typ = Some mcs /\ List.map snd gv = mcs)
      gv_
      (FIT: fit_gv conf.(CurTargetData) typ gv_ = Some gv)
  : InvState.Unary.sem conf st invst invmem gmax public
                       (Invariant.update_lessdef
                          (Exprs.ExprPairSet.add
                             (Exprs.Expr.value (Exprs.ValueT.const (const_undef typ)),
                              Exprs.Expr.value (Exprs.ValueT.id (Exprs.Tag.physical, id))))
                          inv).
Proof.
  inv STATE. econs; eauto.
  ii. ss. simpl_ep_set.
  - ss. esplits.
    { unfold InvState.Unary.sem_idT. ss.
      rewrite <- LOCALS. apply lookupAL_updateAddAL_eq. }
    exploit const2GV_undef; eauto. i. des.
    { clarify. apply all_undef_lessdef_aux; eauto.
      eapply fit_gv_undef_or_has_chunkb; eauto.
    }
  - apply LESSDEF; eauto.
Qed.

Lemma postcond_cmd_add_call
      m_src conf_src st0_src retval1_src id_src fun_src args_src locals0_src
      m_tgt conf_tgt st0_tgt retval1_tgt id_tgt fun_tgt args_tgt locals0_tgt
      invst0 invmem inv0
      noret clattrs typ varg
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem)
      (RETURN_SRC : return_locals (CurTargetData conf_src) retval1_src id_src noret typ locals0_src = Some st0_src.(EC).(Locals))
      (RETURN_TGT : return_locals (CurTargetData conf_tgt) retval1_tgt id_tgt noret typ locals0_tgt = Some st0_tgt.(EC).(Locals))
      (RETVAL : lift2_option (genericvalues_inject.gv_inject (InvMem.Rel.inject invmem)) retval1_src retval1_tgt)
  : exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst1 invmem
                              (postcond_cmd_add
                                 (insn_call id_src noret clattrs typ varg fun_src args_src)
                                 (insn_call id_tgt noret clattrs typ varg fun_tgt args_tgt) inv0)>>.
Proof.
  unfold return_locals in *. des_ifs; ss.
  - rewrite postcond_cmd_add_noret_call.
    exploit SoundReduceMaydiff.reduce_maydiff_sound; eauto.
  - rename H0 into LOCALS_TGT. rename H1 into LOCALS_SRC.
    rewrite postcond_cmd_add_ret_call.
    exploit SoundReduceMaydiff.reduce_maydiff_sound; try (by intro PR; exact PR); eauto.
    unfold remove_def_from_maydiff.
    des_ifs.
    + instantiate (1:=invst0).
      inv STATE.
      econs; try by (eapply updateAddAL_lessdef_undef; eauto);
        (eapply fit_gv_chunks_aux; eauto).
      { ss. }
      i. destruct id0 as []. ss.
      rewrite Exprs.IdTSetFacts.remove_b in *.
      des_bool. des.
      * eauto.
      * simtac. unfold Exprs.IdTSetFacts.eqb in *.
        des_ifs.
        unfold Exprs.IdT.lift in *. clarify.
        econs.
        esplits.
        { unfold InvState.Unary.sem_idT. ss.
          rewrite <- LOCALS_TGT.
          apply lookupAL_updateAddAL_eq. }
        { unfold InvState.Unary.sem_idT in *. ss.
          exploit genericvalues_inject.simulation__fit_gv; eauto.
          { inv MEM. eauto. }
          i. des.
          inv CONF. inv INJECT.
          rewrite TARGETDATA in *.
          rewrite <- LOCALS_SRC in VAL_SRC.
          rewrite lookupAL_updateAddAL_eq in VAL_SRC.
          clarify.
      }
      * ss.
    + inv STATE.
      econs; [ | | | by eauto|];
        ss; try by (eapply updateAddAL_lessdef_undef; eauto);
        (eapply fit_gv_chunks_aux; eauto).
  - rewrite postcond_cmd_add_noret_call.
    exploit SoundReduceMaydiff.reduce_maydiff_sound; eauto.
Qed.

Lemma postcond_call_sound
      m_src conf_src st0_src id_src noret_src clattrs_src typ_src varg_src fun_src args_src cmds_src
      m_tgt conf_tgt st0_tgt id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt args_tgt cmds_tgt
      invst0 invmem0 inv0 inv1
      (CONF : InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = (insn_call id_src noret_src clattrs_src typ_src varg_src fun_src args_src) :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = (insn_call id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt args_tgt) :: cmds_tgt)
      (POSTCOND:
         postcond_cmd
           (insn_call id_src noret_src clattrs_src typ_src varg_src fun_src args_src)
           (insn_call id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt args_tgt)
           inv0 = Some inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (WF_SRC: wf_State conf_src st0_src)
      (WF_TGT: wf_State conf_tgt st0_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
  :
  <<NORET: noret_src = noret_tgt>> /\
  <<CLATTRS: clattrs_src = clattrs_tgt>> /\
  <<TYP: typ_src = typ_tgt>> /\
  <<VARG: varg_src = varg_tgt>> /\
  <<FUN:
    forall funval2_src
      (FUN_SRC: getOperandValue conf_src.(CurTargetData) fun_src st0_src.(EC).(Locals) conf_src.(Globals) = Some funval2_src),
    exists funval1_tgt,
      <<FUN_TGT: getOperandValue conf_tgt.(CurTargetData) fun_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some funval1_tgt>> /\
      <<INJECT: genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject) funval2_src funval1_tgt>>>> /\
  <<ARGS:
    forall args2_src
      (ARGS_SRC: params2GVs (conf_src.(CurTargetData))
                            args_src st0_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
    exists args1_tgt,
      (<<ARGS_TGT: params2GVs (conf_tgt.(CurTargetData)) args_tgt
                             st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>>) /\
      (<<INJECT: list_forall2 (genericvalues_inject.gv_inject
                                 invmem0.(InvMem.Rel.inject)) args2_src args1_tgt>>) /\
      (<<VALID_SRC: List.Forall (MemProps.valid_ptrs (Memory.Mem.nextblock st0_src.(Mem))) args2_src>>) /\
      (<<VALID_TGT: List.Forall (MemProps.valid_ptrs (Memory.Mem.nextblock st0_tgt.(Mem))) args1_tgt>>)
        >> /\
  <<RETURN:
    forall invmem1 mem1_src mem1_tgt retval1_src retval1_tgt locals1_src
      (INCR: InvMem.Rel.le (InvMem.Rel.lift st0_src.(Mem) st0_tgt.(Mem)
                                            (memory_blocks_of conf_src st0_src.(EC).(Locals) inv0.(Invariant.src).(Invariant.unique))
                                            (memory_blocks_of conf_tgt st0_tgt.(EC).(Locals) inv0.(Invariant.tgt).(Invariant.unique))
                                            (memory_blocks_of_t conf_src st0_src invst0.(InvState.Rel.src) inv0.(Invariant.src).(Invariant.private))
                                            (memory_blocks_of_t conf_tgt st0_tgt invst0.(InvState.Rel.tgt) inv0.(Invariant.tgt).(Invariant.private))
                                            invmem0) invmem1)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem1)
      (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject invmem1.(InvMem.Rel.inject)) retval1_src retval1_tgt)
      (VALID: valid_retvals mem1_src mem1_tgt retval1_src retval1_tgt)
      (RETURN_SRC: return_locals
                     conf_src.(CurTargetData)
                     retval1_src id_src noret_src typ_src
                     st0_src.(EC).(Locals)
                   = Some locals1_src),
    exists locals2_tgt invst2 invmem2,
      <<RETURN_TGT: return_locals
                      conf_tgt.(CurTargetData)
                      retval1_tgt id_tgt noret_tgt typ_tgt
                      st0_tgt.(EC).(Locals)
                    = Some locals2_tgt>> /\
      <<INCR: InvMem.Rel.le invmem0 invmem2>> /\
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
          invst2 invmem2 inv1>> /\
      <<MEM: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem2>>>>.
Proof.
  Local Opaque postcond_cmd_inject_event.
  unfold postcond_cmd, postcond_cmd_check in *. ss.
  rewrite <- (ite_spec noret_src None (Some id_src)) in *.
  rewrite <- (ite_spec noret_tgt None (Some id_tgt)) in *.
  des_ifs.
  rewrite negb_false_iff in *.

  exploit postcond_cmd_inject_event_Subset; eauto.
  { etransitivity; [apply forget_stack_call_Subset|apply forget_memory_call_Subset]. }
  i. des.

  exploit postcond_cmd_inject_event_call; eauto. i. des. subst.
  esplits; eauto. i.

  exploit forget_memory_call_sound; try exact STATE; eauto.
  i. des.

  exploit forget_stack_call_sound; eauto.
  { inv CONF. eauto. }
  { rewrite CMDS_SRC. instantiate (1:= cmds_src). econs. apply sublist_refl. }
  { rewrite CMDS_TGT. instantiate (1:= cmds_tgt). econs. apply sublist_refl. }
  { apply forget_memory_call_unique_implies_private. }
  { apply forget_memory_call_unique_implies_private. }
  { rewrite MEM_INJ. eauto. }
  i. des.

  exploit postcond_cmd_add_call; eauto.
  { rewrite MEM_INJ. eauto. }
  i. des.

  esplits; eauto.
Qed.
