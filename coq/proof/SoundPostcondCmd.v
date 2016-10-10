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
Require Import SoundPostcondForget.
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

  destruct (s_isFinialState conf_src st0_src) eqn:FINAL.
  { unfold s_isFinialState in FINAL. simtac. }
  exploit nerror_nfinal_nstuck; eauto. i. des.
  replace e with evt in *; cycle 1.
  { unfold postcond_cmd_check in COND. simtac.
    exploit (@noncall_event conf_src); eauto. i.
    exploit (@noncall_event conf_tgt); eauto. i.
    subst. ss.
  }

  exploit postcond_cmd_forget_sound; eauto.
  { exploit step_state_equiv_except; eauto. }
  { exploit step_state_equiv_except; eauto. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  i. des.

  exploit postcond_cmd_add_sound; eauto. i. des.
  esplits; eauto. etransitivity; eauto.
Admitted.
