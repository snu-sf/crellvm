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
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.

Lemma snapshot_sound
      conf_src conf_tgt st_src st_tgt invst0 invmem0 inv0 inv1
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem0 inv0)
      (SNAPSHOT: Snapshot.t inv0 = inv1):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem0 inv1>>.
Proof.
Admitted.