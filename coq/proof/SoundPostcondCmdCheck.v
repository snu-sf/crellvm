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

Set Implicit Arguments.


Lemma postcond_cmd_check_mon
          src tgt
          def_src def_tgt uses_src uses_tgt
          inv0 inv1
          (LE: Invariant.le inv0 inv1)
          (CHECK: postcond_cmd_check
                    src tgt
                    def_src def_tgt uses_src uses_tgt
                    inv0):
  postcond_cmd_check
    src tgt
    def_src def_tgt uses_src uses_tgt
    inv1.
Proof.
  unfold postcond_cmd_check in *. simtac.
  destruct (postcond_cmd_inject_event src tgt inv1) eqn:X; ss. exfalso.
  admit.
Admitted.


Lemma event_call
      conf st0 st1 evt cmd cmds
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd::cmds)
      (NONCALL: Instruction.isCallInst cmd = false):
  evt = events.E0.
Proof.
  inv STEP; ss. inv CMDS. ss.
Qed.

Lemma postcond_cmd_check_sound
      conf_src st0_src cmd_src cmds_src def_src uses_src
      conf_tgt st0_tgt cmd_tgt cmds_tgt def_tgt uses_tgt
      invst0 invmem0 inv0
      st1_tgt evt
      (POSTCOND: Postcond.postcond_cmd_check cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv0)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt)
      (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
      (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false)
      (NERROR_SRC: ~ error_state conf_src st0_src)
      (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))
      (DEF_TGT: def_tgt = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt)))
      (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src))
      (USES_TGT: uses_tgt = AtomSetImpl_from_list (Cmd.get_ids cmd_tgt)):
  exists st1_src,
    <<STEP_SRC: sInsn conf_src st0_src st1_src evt>>.
Proof.
  destruct (s_isFinialState conf_src st0_src) eqn:FINAL.
  { unfold s_isFinialState in FINAL. simtac. }
  exploit nerror_nfinal_nstuck; eauto. i. des.
  replace e with evt in *.
  { esplits; eauto. }
  unfold postcond_cmd_check in POSTCOND. simtac.
  exploit (@event_call conf_src); eauto. i.
  exploit (@event_call conf_tgt); eauto. i.
  subst. ss.
Qed.
