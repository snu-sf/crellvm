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
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.


(* TODO: in return we need to update locals.  SimulationLocal.v should also be changed. cf. `sim_local_stack` in Simulation.v *)
Lemma postcond_call_sound
      conf_src st0_src id_src noret_src clattrs_src typ_src varg_src fun_src args_src cmds_src
      conf_tgt st0_tgt id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt args_tgt cmds_tgt
      invst0 invmem0 inv0 inv1
      (CMDS_SRC: st0_src.(EC).(CurCmds) = (insn_call id_src noret_src clattrs_src typ_src varg_src fun_src args_src) :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = (insn_call id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt args_tgt) :: cmds_tgt)
      (POSTCOND:
         Postcond.postcond_cmd
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
      (INCR: InvMem.Rel.le invmem0 invmem1)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem1)
      (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject invmem1.(InvMem.Rel.inject)) retval1_src retval1_tgt)
      (RETURN_SRC: return_locals
                     conf_src.(CurTargetData)
                     retval1_src id_src noret_src typ_src
                     st0_src.(EC).(Locals)
                   = Some locals1_src),
    exists locals1_tgt invst1,
      <<RETURN_TGT: return_locals
                      conf_tgt.(CurTargetData)
                      retval1_tgt id_tgt noret_tgt typ_tgt
                      st0_tgt.(EC).(Locals)
                    = Some locals1_tgt>> /\
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
                         locals1_tgt
                         st0_tgt.(EC).(Allocas))
                   st0_tgt.(ECS) mem1_tgt)
          invst1 invmem1 inv1>>>>.
Proof.
  unfold Postcond.postcond_cmd in *. do 19 simtac0.
  rewrite <- (ite_spec noret_tgt None (Some id_src)) in *.
  rewrite <- (ite_spec noret_tgt None (Some id_tgt)) in *.
  splits; ss.
  - admit. (* fun *)
  - admit. (* args *)
  - admit. (* return *)
Admitted.
