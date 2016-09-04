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

Set Implicit Arguments.


Definition CONF_TODO: Prop. Admitted.

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

Lemma inject_locals_getOperandValue
      inv val
      conf_src locals_src gval_src
      conf_tgt locals_tgt gval_tgt
      (CONF: CONF_TODO)
      (INJECT: inject_locals inv locals_src locals_tgt)
      (SRC: getOperandValue (CurTargetData conf_src) val locals_src (Globals conf_src) = Some gval_src)
      (TGT: getOperandValue (CurTargetData conf_tgt) val locals_tgt (Globals conf_tgt) = Some gval_tgt):
  genericvalues_inject.gv_inject inv.(InvMem.Rel.inject) gval_src gval_tgt.
Proof.
  destruct val; ss.
  - exploit INJECT; eauto. i. des.
    rewrite TGT in LU_TGT. inv LU_TGT. ss.
  - admit. (* CONF_TODO *)
Admitted.

Lemma inject_locals_params2GVs
      inv0 args0
      conf_src locals_src gvs_param_src
      conf_tgt locals_tgt gvs_param_tgt
      (CONF: CONF_TODO)
      (INJECT: inject_locals inv0 locals_src locals_tgt)
      (PARAM_SRC:params2GVs (CurTargetData conf_src) args0 locals_src (Globals conf_src) = Some gvs_param_src)
      (PARAM_TGT:params2GVs (CurTargetData conf_tgt) args0 locals_tgt (Globals conf_tgt) = Some gvs_param_tgt):
  list_forall2 (genericvalues_inject.gv_inject (InvMem.Rel.inject inv0)) gvs_param_src gvs_param_tgt.
Proof.
  revert gvs_param_src PARAM_SRC.
  revert gvs_param_tgt PARAM_TGT.
  induction args0.
  - i. ss. inv PARAM_SRC. inv PARAM_TGT. econs.
  - i. ss.
    destruct a as ((ty_a & attr_a) & v_a).
    revert PARAM_TGT. revert PARAM_SRC.
    (* TODO: make a tactic *)
    repeat
      (match goal with
       | [|- context[match ?c with | Some _ => _ | None => _ end]] =>
         let COND := fresh "COND" in
         destruct c eqn:COND
       end; ss).
    i. inv PARAM_SRC. inv PARAM_TGT.
    econs.
    + eapply inject_locals_getOperandValue; eauto.
    + eauto.
Qed.

Lemma inject_locals_inj_incr
      inv0 inv1
      locals_src locals_tgt
      (INJECT: inject_locals inv0 locals_src locals_tgt)
      (INCR: InvMem.Rel.le inv0 inv1):
  inject_locals inv1 locals_src locals_tgt.
Proof.
  ii. exploit INJECT; eauto. i. des.
  esplits; eauto.
  eapply genericvalues_inject.gv_inject_incr; try apply INCR; eauto.
Qed.

Lemma inject_allocas_inj_incr
      inv0 inv1
      allocas_src allocas_tgt
      (INJECT: inject_allocas inv0 allocas_src allocas_tgt)
      (INCR: InvMem.Rel.le inv0 inv1):
  inject_allocas inv1 allocas_src allocas_tgt.
Proof.
  eapply list_forall2_imply; eauto. s. i.
  apply INCR. auto.
Qed.

(* TODO: position *)
Lemma targetdata_dec
      (TD_src TD_tgt:TargetData):
  {TD_src = TD_tgt} + {TD_src <> TD_tgt}.
Proof.
  decide equality.
  - apply namedts_dec.
  - apply layouts_dec.
Qed.
