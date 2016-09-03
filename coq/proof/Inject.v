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
Require Import GenericValues.
Require Import Nop.
Require Import SimulationLocal.
Require InvMem.
Require InvState.

(* TODO: name *)
Definition inject_locals
           (inv:InvMem.Rel.t)
           (locals_src locals_tgt:GVsMap): Prop :=
  forall (i:id) (gv_src:GenericValue) (LU_SRC: lookupAL _ locals_src i = Some gv_src),
  exists gv_tgt,
    <<LU_TGT: lookupAL _ locals_tgt i = Some gv_tgt>> /\
    <<INJECT: genericvalues_inject.gv_inject inv.(InvMem.Rel.inject) gv_src gv_tgt>>.

Definition inject_allocas
           (inv:InvMem.Rel.t)
           (alc_src alc_tgt:list mblock): Prop :=
  list_forall2
    (fun a_src a_tgt => inv.(InvMem.Rel.inject) a_src = Some (a_tgt, 0))
    alc_src alc_tgt.

Definition CONF_TODO: Prop. Admitted.

Lemma targetdata_dec
      (TD_src TD_tgt:TargetData):
  {TD_src = TD_tgt} + {TD_src <> TD_tgt}.
Proof.
  decide equality.
  - apply namedts_dec.
  - apply layouts_dec.
Qed.
