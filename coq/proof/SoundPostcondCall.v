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
        (ARGS_SRC: params2GVs conf_src.(CurTargetData) args_src st0_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
      exists args1_tgt,
        <<ARGS_TGT: params2GVs conf_tgt.(CurTargetData) args_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>> /\
        <<INJECT: list_forall2 (genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject)) args2_src args1_tgt>>>>.
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
        clarify.
        econs; eauto.
        exploit InvState.Rel.inject_value_spec; eauto.
        { rewrite InvState.Unary.sem_valueT_physical. eauto. }
        rewrite InvState.Unary.sem_valueT_physical. i. des. clarify.
  }
Qed.

(* TODO: free allocas *)
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
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0):
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
      (ARGS_SRC: params2GVs conf_src.(CurTargetData) args_src st0_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
    exists args1_tgt,
      <<ARGS_TGT: params2GVs conf_tgt.(CurTargetData) args_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>> /\
      <<INJECT: list_forall2 (genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject)) args2_src args1_tgt>>>> /\
  <<RETURN:
    forall invmem1 mem1_src mem1_tgt retval1_src retval1_tgt locals1_src
      (INCR: InvMem.Rel.le (InvMem.Rel.lift st0_src.(Mem) st0_tgt.(Mem) invmem0) invmem1)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem1)
      (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject invmem1.(InvMem.Rel.inject)) retval1_src retval1_tgt)
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
  { etransitivity.
    - apply forget_stack_call_Subset.
    - apply forget_memory_call_Subset. }
  i. des.

  exploit postcond_cmd_inject_event_call; eauto. i. des. subst.
  esplits; eauto. i.

  exploit forget_memory_call_sound.
  { exact CMDS_SRC. }
  { exact CMDS_TGT. }
  { exact STATE. }
  { eauto. }
  { eauto. }
  { eauto. }
  { instantiate (1:= InvMem.Rel.mk invmem0.(InvMem.Rel.src) invmem0.(InvMem.Rel.tgt)
                                   invmem1.(InvMem.Rel.gmax) invmem1.(InvMem.Rel.inject)).
    admit. }
  { instantiate (2:= mem1_src). instantiate (1:= mem1_tgt).
    admit. }

  i. des.

  exploit forget_stack_call_sound; eauto.
  { inv CONF. eauto. }
  { instantiate (1:= retval1_tgt). admit. }
  i. des.
  esplits; eauto.
  (* TODO: postcond_cmd_add *)
Admitted.
