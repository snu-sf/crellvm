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
Require Import Postcond.
Require Import Exprs.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.

Definition equiv_Locals_mod_ids (locals0 locals1:GVsMap) (ids:IdTSet.t): Prop :=
  forall id (NOT_IN: ~ IdTSet.In (Tag.physical, id) ids),
    lookupAL _ locals0 id = lookupAL _ locals1 id.

Definition equiv_EC_mod_ids (EC0 EC1: ExecutionContext) (ids:IdTSet.t): Prop :=
  EC0.(CurFunction) = EC1.(CurFunction) /\
  EC0.(CurBB) = EC1.(CurBB) /\
  EC0.(CurCmds) = EC1.(CurCmds) /\
  EC0.(Terminator) = EC1.(Terminator) /\
  EC0.(Allocas) = EC1.(Allocas) /\
  equiv_Locals_mod_ids EC0.(Locals) EC1.(Locals) ids.

Definition equiv_state_mod_ids (st0 st1: State) (ids:IdTSet.t): Prop :=
  st0.(ECS) = st1.(ECS) /\ st0.(Mem) = st1.(Mem) /\
  equiv_EC_mod_ids st0.(EC) st1.(EC) ids.

Lemma forget_sound
      conf_src conf_tgt st_src0 st_tgt0 st_src1 st_tgt1 invst0 invmem0 inv0 inv1 s_src s_tgt
      (EQUIV_SRC: equiv_state_mod_ids st_src0 st_src1 s_src)
      (EQUIV_TGT: equiv_state_mod_ids st_tgt0 st_tgt1 s_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src0 st_tgt0 invst0 invmem0 inv0)
      (FORGET: Forget.t s_src s_tgt inv0 = inv1):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src1 st_tgt1 invst1 invmem0 inv1>>.
Proof.
Admitted.