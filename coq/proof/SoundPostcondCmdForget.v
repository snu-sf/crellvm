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


(* TODO: move this to soundforget.v? *)
Lemma postcond_cmd_forget_le
      def_src def_tgt leaks_src leaks_tgt
      inv:
  Invariant.le
    (Forget.t def_src def_tgt leaks_src leaks_tgt inv)
    inv.
Proof.
Admitted.

Lemma postcond_cmd_forget_memory_le
      def_memory_src def_memory_tgt
      inv:
  Invariant.le
    (ForgetMemory.t def_memory_src def_memory_tgt inv)
    inv.
Proof.
Admitted.

Lemma step_state_equiv_except
      cmd cmds
      conf st0 st1 evt
      (CMDS: st0.(EC).(CurCmds) = cmd :: cmds)
      (STEP: sInsn conf st0 st1 evt)
  : state_equiv_except (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd))) st0 st1.
Proof.
Admitted.

(* TODO: complete this lemma about unique_preserved_except *)
(* Lemma step_unique_preserved_except *)
(*           (STEP: sInsn conf_src st0_src st1_src evt) *)
(*     : unique_preserved_except conf_src (InvState.Rel.src invst0) (Invariant.src inv0) *)
(*     (AtomSetImpl_from_list (Cmd.get_def ?Goal13)) ?Goal *)


Definition FORGET_MEMORY_TODO: Prop. Admitted. (* TODO *)

(* TODO: we can assume source's progress *)
Lemma postcond_cmd_forget_sound
      conf_src st0_src st1_src def_src leaks_src cmd_src cmds_src def_memory_src
      conf_tgt st0_tgt st1_tgt def_tgt leaks_tgt cmd_tgt cmds_tgt def_memory_tgt
      invst0 invmem0 inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt)
      (STATE_SRC: state_equiv_except def_src st0_src st1_src)
      (STATE_TGT: state_equiv_except def_tgt st0_tgt st1_tgt)
      (UNIQUE_SRC: unique_preserved_except conf_src invst0.(InvState.Rel.src) inv0.(Invariant.src) st1_src def_src leaks_src)
      (UNIQUE_TGT: unique_preserved_except conf_tgt invst0.(InvState.Rel.tgt) inv0.(Invariant.tgt) st1_tgt def_tgt leaks_tgt)
      (MEM_SRC: FORGET_MEMORY_TODO)
      (MEM_TGT: FORGET_MEMORY_TODO)
  : exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1
                              (ForgetMemory.t def_memory_src def_memory_tgt
                                              (Forget.t def_src def_tgt leaks_src leaks_tgt inv0)) >> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
Admitted.
