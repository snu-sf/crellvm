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


(* TODO: lemma on tag.previous *)

Definition snapshot_as_previous st invst: Prop :=
  forall x gvx
         (LOCAL_IN: lookupAL _ st.(EC).(Locals) x = Some gvx),
    <<PREV: InvState.Unary.sem_idT st invst (Tag.previous, x) = Some gvx>>.

Lemma snapshot_unary_sound
      conf st invst0 invmem inv0
      (STATE: InvState.Unary.sem conf st invst0 invmem inv0)
  :
    exists invst1,
      <<STATE: InvState.Unary.sem conf st invst1 invmem (Snapshot.unary inv0)>> /\
               <<PREV: snapshot_as_previous st invst1>>.
Proof.
Admitted.

Lemma snapshot_sound
      conf_src conf_tgt st_src st_tgt invst0 invmem inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv0):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem (Snapshot.t inv0)>> /\
    <<PREV_SRC: snapshot_as_previous st_src invst1.(InvState.Rel.src)>> /\
    <<PREV_TGT: snapshot_as_previous st_tgt invst1.(InvState.Rel.tgt)>>.
Proof.
  inv STATE.
  apply snapshot_unary_sound in SRC.
  apply snapshot_unary_sound in TGT. des.
  esplits.
  - econs.
    + admit.
    + admit.
    + admit.
      (* Lemma snapshot_maydiff_incr *)
      (*       Snapshot.IdTSet maydiff *)



    
  



  
Admitted.
