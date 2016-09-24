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

(* TODO: we can assume source's progress *)
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
      (NONCALL_SRC: ~ Instruction.isCallInst cmd_src)
      (NONCALL_TGT: ~ Instruction.isCallInst cmd_tgt)
      (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))
      (DEF_TGT: def_tgt = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt)))
      (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src))
      (USES_TGT: uses_tgt = AtomSetImpl_from_list (Cmd.get_ids cmd_tgt)):
  exists st1_src,
    <<STEP_SRC: sInsn conf_src st0_src st1_src evt>>.
Proof.
Admitted.

Definition FORGET_MEMORY_TODO: Prop. Admitted. (* TODO *)

(* TODO: we can assume source's progress *)
Lemma postcond_cmd_forget_sound
      conf_src st0_src st1_src def_src leaks_src def_memory_src
      conf_tgt st0_tgt st1_tgt def_tgt leaks_tgt def_memory_tgt
      invst0 invmem0 inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (STATE_SRC: state_equiv_except def_src st0_src st1_src)
      (STATE_TGT: state_equiv_except def_tgt st0_tgt st1_tgt)
      (UNIQUE_SRC: unique_preserved_except conf_src invst0.(InvState.Rel.src) inv0.(Invariant.src) st1_src def_src leaks_src)
      (UNIQUE_TGT: unique_preserved_except conf_tgt invst0.(InvState.Rel.tgt) inv0.(Invariant.tgt) st1_tgt def_tgt leaks_tgt)
      (MEM_SRC: FORGET_MEMORY_TODO)
      (MEM_TGT: FORGET_MEMORY_TODO):
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1
                              (Postcond.postcond_cmd_forget
                                 def_src def_tgt leaks_src leaks_tgt
                                 def_memory_src def_memory_tgt
                                 inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
Admitted.

Lemma postcond_cmd_add_sound
      conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
      conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt
      invst0 invmem0 inv0
      evt
      (POSTCOND: Postcond.postcond_cmd_check cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv0)
      (STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem0)
      (STEP_SRC: sInsn conf_src st0_src st1_src evt)
      (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt)
      (NONCALL_SRC: ~ Instruction.isCallInst cmd_src)
      (NONCALL_TGT: ~ Instruction.isCallInst cmd_tgt)
      (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))
      (DEF_TGT: def_tgt = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt)))
      (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src))
      (USES_TGT: uses_tgt = AtomSetImpl_from_list (Cmd.get_ids cmd_tgt)):
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1
                              (Postcond.postcond_cmd_add cmd_src cmd_tgt inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
Admitted.

Definition Invariant_le (inv0 inv1: Invariant.t): Prop. Admitted. (* TODO *)

Lemma postcond_cmd_check_mon
          src tgt
          def_src def_tgt uses_src uses_tgt
          inv0 inv1
          (LE: Invariant_le inv0 inv1)
          (CHECK: postcond_cmd_check
                    src tgt
                    def_src def_tgt uses_src uses_tgt
                    inv0):
  postcond_cmd_check
    src tgt
    def_src def_tgt uses_src uses_tgt
    inv1.
Proof.
Admitted.

Lemma postcond_cmd_forget_le
      def_src def_tgt leaks_src leaks_tgt
      def_memory_src def_memory_tgt
      inv:
  Invariant_le
    (postcond_cmd_forget
       def_src def_tgt leaks_src leaks_tgt
       def_memory_src def_memory_tgt
       inv)
    inv.
Proof.
Admitted.

(* TODO: we can assume source's progress *)
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
      (NONCALL_SRC: ~ Instruction.isCallInst cmd_src)
      (NONCALL_TGT: ~ Instruction.isCallInst cmd_tgt):
  exists st1_src invst1 invmem1,
    <<STEP_SRC: sInsn conf_src st0_src st1_src evt>> /\
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1 inv1>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  unfold postcond_cmd in *. simtac.
  exploit postcond_cmd_check_sound; try exact STATE; eauto.
  { eapply postcond_cmd_check_mon; eauto.
    apply postcond_cmd_forget_le.
  }
  i. des.
  exploit postcond_cmd_forget_sound; eauto.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  i. des.
  exploit postcond_cmd_add_sound; eauto. i. des.
  esplits; eauto. etransitivity; eauto.
Admitted.
