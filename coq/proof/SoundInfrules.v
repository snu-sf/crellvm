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
Require Import SimulationLocal.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.


Lemma apply_infrule_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem0 inv0
      infrule
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem0):
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem1
                              (Infrules.apply_infrule m_src m_tgt infrule inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
Admitted.

Lemma apply_infrules_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem0 inv0
      infrules
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem0):
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem1
                              (Infrules.apply_infrules m_src m_tgt infrules inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  unfold Infrules.apply_infrules. rewrite <- fold_left_rev_right.
  move infrules at top. revert_until infrules. induction (rev infrules); i.
  - esplits; eauto. reflexivity.
  - exploit IHl0; eauto. i. des.
    exploit apply_infrule_sound; eauto. i. des.
    esplits; eauto.
    etransitivity; eauto.
Qed.