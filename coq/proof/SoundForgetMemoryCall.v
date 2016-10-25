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

Set Implicit Arguments.


Definition FORGET_MEMORY_CALL_TODO: Prop. Admitted. (* TODO *)

Inductive state_equiv_private_unique conf invst inv0 st0 st1: Prop :=
| state_equiv_private_unique_intro
    (LOCALS: st0.(EC).(Locals) = st1.(EC).(Locals))
    (UNIQUE: forall x gptr ty a gv
                    (MEM: AtomSetImpl.mem x inv0.(Invariant.unique))
                    (PTR: lookupAL _ st0.(EC).(Locals) x = Some gptr)
                    (LOAD: mload conf.(CurTargetData) st0.(Mem) gptr ty a = Some gv),
        mload conf.(CurTargetData) st1.(Mem) gptr ty a = Some gv)
    (PRIVATE: forall tx gptr ty a gv
                    (MEM: IdTSet.mem tx inv0.(Invariant.private))
                    (PTR: InvState.Unary.sem_idT st0 invst tx = Some gptr)
                    (LOAD: mload conf.(CurTargetData) st0.(Mem) gptr ty a = Some gv),
        mload conf.(CurTargetData) st1.(Mem) gptr ty a = Some gv)
.

Definition unique_preserved conf inv st1: Prop :=
  forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique)),
           InvState.Unary.sem_unique conf st1 u.

Lemma postcond_call_forget_sound
      conf_src st0_src st1_src
      conf_tgt st0_tgt st1_tgt
      invst0 invmem0 inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (STATE_SRC: state_equiv_private_unique conf_src invst0.(InvState.Rel.src) inv0.(Invariant.src) st0_src st1_src)
      (STATE_TGT: state_equiv_private_unique conf_tgt invst0.(InvState.Rel.tgt) inv0.(Invariant.tgt) st0_tgt st1_tgt)
      (UNIQUE_SRC: unique_preserved conf_src inv0.(Invariant.src) st1_src)
      (UNIQUE_TGT: unique_preserved conf_tgt inv0.(Invariant.tgt) st1_tgt)
  : exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1
                              (ForgetMemoryCall.t inv0) >> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
Admitted.
