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


Lemma implies_sound
      m_src conf_src st_src
      m_tgt conf_tgt st_tgt
      invst invmem inv0 inv1
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
      (IMPLIES: Hints.Invariant.implies inv0 inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv1>> /\
  <<MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem>>.
Proof.
Admitted.
