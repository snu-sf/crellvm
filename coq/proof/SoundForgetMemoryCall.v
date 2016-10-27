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

Set Implicit Arguments.


Lemma forget_memory_call_Subset inv
  : Hints.Invariant.Subset (ForgetMemoryCall.t inv) inv.
Proof.
Admitted.

Lemma forget_memory_call_sound
      conf_src st0_src id_src fun_src args_src cmds_src
      conf_tgt st0_tgt id_tgt fun_tgt args_tgt cmds_tgt
      noret clattrs typ varg
      invmem0 invst0 inv0
      invmem1 mem1_src mem1_tgt
      (CMDS_SRC: st0_src.(EC).(CurCmds) = (insn_call id_src noret clattrs typ varg fun_src args_src) :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = (insn_call id_tgt noret clattrs typ varg fun_tgt args_tgt) :: cmds_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM_BEFORE_CALL: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (FUN:
         forall funval2_src
                (FUN_SRC: getOperandValue conf_src.(CurTargetData) fun_src st0_src.(EC).(Locals) conf_src.(Globals) = Some funval2_src),
         exists funval1_tgt,
          <<FUN_TGT: getOperandValue conf_tgt.(CurTargetData) fun_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some funval1_tgt>> /\
          <<INJECT: genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject) funval2_src funval1_tgt>>)
      (ARGS:
         forall args2_src
                (ARGS_SRC: params2GVs conf_src.(CurTargetData) args_src st0_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
         exists args1_tgt,
           <<ARGS_TGT: params2GVs conf_tgt.(CurTargetData) args_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>> /\
           <<INJECT: list_forall2 (genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject)) args2_src args1_tgt>>)
      (INCR: InvMem.Rel.le (InvMem.Rel.lift st0_src.(Mem) st0_tgt.(Mem) invmem0) invmem1)
      (MEM_AFTER_CALL: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem1)
  : exists invst2 invmem2,
      <<INCR: InvMem.Rel.le invmem0 invmem2>> /\
      <<STATE:
        InvState.Rel.sem
          conf_src conf_tgt
          (mkState st0_src.(EC) st0_src.(ECS) mem1_src)
          (mkState st0_tgt.(EC) st0_tgt.(ECS) mem1_tgt)
          invst2 invmem2 (ForgetMemoryCall.t inv0)>> /\
      <<MEM: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem2>>.
Proof.
Admitted.
