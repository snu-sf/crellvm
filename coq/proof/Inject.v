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
Require InvMem.

Set Implicit Arguments.


(* TODO: position *)
Lemma targetdata_dec
      (TD_src TD_tgt:TargetData):
  {TD_src = TD_tgt} + {TD_src <> TD_tgt}.
Proof.
  decide equality.
  - apply namedts_dec.
  - apply layouts_dec.
Qed.

(* TODO: name *)
Definition inject_locals
           (inv:InvMem.Rel.t)
           (locals_src locals_tgt:GVsMap): Prop :=
  forall (i:id) (gv_src:GenericValue) (LU_SRC: lookupAL _ locals_src i = Some gv_src),
  exists gv_tgt,
    <<LU_TGT: lookupAL _ locals_tgt i = Some gv_tgt>> /\
    <<INJECT: genericvalues_inject.gv_inject inv.(InvMem.Rel.inject) gv_src gv_tgt>>.

Inductive inject_conf (conf_src conf_tgt:Config): Prop :=
| inject_conf_intro
    (TARGETDATA: conf_src.(CurTargetData) = conf_tgt.(CurTargetData))
    (GLOBALS: conf_src.(Globals) = conf_tgt.(Globals))
.

Definition inject_allocas
           (inv:InvMem.Rel.t)
           (alc_src alc_tgt:list mblock): Prop :=
  list_forall2
    (fun a_src a_tgt => inv.(InvMem.Rel.inject) a_src = Some (a_tgt, 0))
    alc_src alc_tgt.

Lemma inject_locals_getOperandValue
      inv val
      conf_src locals_src gval_src
      conf_tgt locals_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (LOCALS: inject_locals inv locals_src locals_tgt)
      (SRC: getOperandValue conf_src.(CurTargetData) val locals_src (Globals conf_src) = Some gval_src):
  exists gval_tgt,
    <<TGT: getOperandValue conf_tgt.(CurTargetData) val locals_tgt (Globals conf_tgt) = Some gval_tgt>> /\
    <<INJECT: genericvalues_inject.gv_inject inv.(InvMem.Rel.inject) gval_src gval_tgt>>.
Proof.
  destruct val; ss.
  - exploit LOCALS; eauto.
  - destruct conf_src, conf_tgt. inv CONF. ss. subst.
    esplits; eauto.
    admit. (* const2GV inject refl *)
Admitted.

Lemma inject_locals_params2GVs
      inv0 args0
      conf_src locals_src gvs_param_src
      conf_tgt locals_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (LOCALS: inject_locals inv0 locals_src locals_tgt)
      (PARAM_SRC:params2GVs (CurTargetData conf_src) args0 locals_src (Globals conf_src) = Some gvs_param_src):
  exists gvs_param_tgt,
    <<PARAM_TGT:params2GVs (CurTargetData conf_tgt) args0 locals_tgt (Globals conf_tgt) = Some gvs_param_tgt>> /\
    <<INJECT: list_forall2 (genericvalues_inject.gv_inject (InvMem.Rel.inject inv0)) gvs_param_src gvs_param_tgt>>.
Proof.
  revert gvs_param_src PARAM_SRC.
  induction args0; ss.
  - i. inv PARAM_SRC. esplits; ss. econs.
  - i. destruct a as ((ty_a & attr_a) & v_a).
    (* TODO: make a tactic *)
    repeat
      (match goal with
       | [H: context[match ?c with | Some _ => _ | None => _ end] |- _] =>
         let COND := fresh "COND" in
         destruct c eqn:COND
       end; ss).
    inv PARAM_SRC.
    exploit inject_locals_getOperandValue; eauto. i. des.
    exploit IHargs0; eauto. i. des.
    rewrite TGT, PARAM_TGT. esplits; eauto. econs; eauto.
Qed.

Lemma locals_init
      inv la gvs_src
      args_src args_tgt
      conf_src conf_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (ARGS: list_forall2 (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) args_src args_tgt)
      (LOCALS_SRC : initLocals (CurTargetData conf_src) la args_src = Some gvs_src) :
  exists gvs_tgt,
    << LOCALS_TGT : initLocals (CurTargetData conf_tgt) la args_tgt = Some gvs_tgt >> /\
    << LOCALS: inject_locals inv gvs_src gvs_tgt >>.
Proof.
  unfold initLocals in *.
  revert gvs_src LOCALS_SRC. induction ARGS; ss.
  - i. destruct la; cycle 1.
    { admit. }
    ss. inv LOCALS_SRC. esplits; eauto. ss.
  - admit.
Admitted.

Lemma inject_locals_inj_incr
      inv0 inv1
      locals_src locals_tgt
      (LOCALS: inject_locals inv0 locals_src locals_tgt)
      (INCR: InvMem.Rel.le inv0 inv1):
  inject_locals inv1 locals_src locals_tgt.
Proof.
  ii. exploit LOCALS; eauto. i. des.
  esplits; eauto.
  eapply genericvalues_inject.gv_inject_incr; try apply INCR; eauto.
Qed.

Lemma inject_allocas_inj_incr
      inv0 inv1
      allocas_src allocas_tgt
      (ALLOCAS: inject_allocas inv0 allocas_src allocas_tgt)
      (INCR: InvMem.Rel.le inv0 inv1):
  inject_allocas inv1 allocas_src allocas_tgt.
Proof.
  eapply list_forall2_imply; eauto. s. i.
  apply INCR. auto.
Qed.
