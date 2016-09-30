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


Definition noalias_with_def_memory (conf:Config) (def_memory:option (GenericValue * typ)) (ptr:GenericValue) (ty:typ): Prop :=
  forall gptr_def ty_def
         (DEF: def_memory = Some (gptr_def, ty_def)),
    InvState.Unary.sem_noalias conf gptr_def ptr ty_def ty.

Inductive state_equiv_except_mem (conf:Config) (def_mptr:option (GenericValue * typ)) (st0 st1:State): Prop :=
| state_equiv_except_mem_intro
    (LOCALS: st0.(EC).(Locals) = st1.(EC).(Locals))
    (MEM: forall ptr ty a gv
                 (NOALIAS: noalias_with_def_memory conf def_mptr ptr ty)
                 (LOAD: mload conf.(CurTargetData) st0.(Mem) ptr ty a = Some gv),
        mload conf.(CurTargetData) st1.(Mem) ptr ty a = Some gv)
.

Definition unique_preserved_mem conf st inv: Prop :=
  forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true),
    InvState.Unary.sem_unique conf st u.

Definition ptr_to_genericvalue conf st invst ptr: option (GenericValue * typ) :=
  match InvState.Unary.sem_valueT conf st invst ptr.(fst) with
  | Some gv => Some (gv, ptr.(snd))
  | None => None
  end.

Lemma forget_memory_unary_sound
      conf st0 invst0 invmem0 inv0
      def_memory st1 public
        (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
        (MEM_EQUIV: state_equiv_except_mem conf
                    (ptr_to_genericvalue conf st0 invst0 def_memory) st0
                    st1)
        (UNIQUE_PRSV: unique_preserved_mem conf st1 inv0)
    : exists invmem1,
      <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem1 (ForgetMemory.unary def_memory inv0)>> /\
      <<MEM_UNARY: InvMem.Unary.sem conf public st1.(Mem) invmem1>> /\
      <<MEMLE_UNARY: InvMem.Unary.le invmem0 invmem1>>.
Proof.
Admitted.

Lemma forget_memory_sound
      conf_src st0_src st1_src def_memory_src
      conf_tgt st0_tgt st1_tgt def_memory_tgt
      invst0 invmem0 inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (MEM_EQUIV_SRC: state_equiv_except_mem
                  conf_src
                  (monad.mbind _ _ (ptr_to_genericvalue conf_src st0_src invst0.(InvState.Rel.src)) def_memory_src)
                  st0_src st1_src)
      (MEM_EQUIV_TGT: state_equiv_except_mem
                  conf_tgt
                  (monad.mbind _ _ (ptr_to_genericvalue conf_tgt st0_tgt invst0.(InvState.Rel.tgt)) def_memory_tgt)
                  st0_tgt st1_tgt)
      (UNIQUE_PRSV_SRC: unique_preserved_mem conf_src st1_src inv0.(Invariant.src))
      (UNIQUE_PRSV_TGT: unique_preserved_mem conf_tgt st1_tgt inv0.(Invariant.tgt))
  : exists invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem1
                              (ForgetMemory.t def_memory_src def_memory_tgt inv0) >> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  inv STATE.
  unfold ForgetMemory.t.
  destruct def_memory_src as [[]|], def_memory_tgt as [[]|]; ss.
  - exploit forget_memory_unary_sound; try exact SRC; eauto. i. des.
    exploit forget_memory_unary_sound; try exact TGT; eauto. i. des.
    eexists (InvMem.Rel.mk _ _ _). splits; swap 2 3.
    + econs; ss; eauto. i.
      hexploit MAYDIFF; eauto. i.
      admit. (* easy; use H *)
    + econs; ss; eauto.
    + econs; ss; eauto.
      inv MEM.
      admit. (* hard; use INJECT *)
      (* state_equiv_except_mem st0 st1 (Some (ptr, ty, a, v)) -> *)
  - admit.
  - admit.
  - admit.
Admitted.
