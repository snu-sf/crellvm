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
Require Import Debug.
Require Import Decs.
Require Import GenericValues.
Require Import Nop.
Require InvMem.

Set Implicit Arguments.


(* TODO: position *)
Ltac simtac0 :=
  try match goal with
      | [H: ?a = ?a |- _] => clear H
      | [H: is_true true |- _] => clear H
      | [H: Some _ = Some _ |- _] => inv H
      | [H: context[let (_, _) := ?p in _] |- _] => destruct p
      | [H: negb _ = true |- _] =>
        apply negb_true_iff in H
      | [H: negb _ = false |- _] =>
        apply negb_false_iff in H
      | [H: andb _ _ = true |- _] => apply andb_true_iff in H; destruct H

      | [H: proj_sumbool (id_dec ?a ?b) = true |- _] =>
        destruct (id_dec a b)
      | [H: proj_sumbool (typ_dec ?a ?b) = true |- _] =>
        destruct (typ_dec a b)
      | [H: proj_sumbool (l_dec ?a ?b) = true |- _] =>
        destruct (l_dec a b)
      | [H: proj_sumbool (fheader_dec ?a ?b) = true |- _] =>
        destruct (fheader_dec a b)
      | [H: proj_sumbool (noret_dec ?a ?b) = true |- _] =>
        destruct (noret_dec a b)
      | [H: proj_sumbool (clattrs_dec ?a ?b) = true |- _] =>
        destruct (clattrs_dec a b)
      | [H: proj_sumbool (varg_dec ?a ?b) = true |- _] =>
        destruct (varg_dec a b)
      | [H: proj_sumbool (layouts_dec ?a ?b) = true |- _] => destruct (layouts_dec a b)
      | [H: proj_sumbool (namedts_dec ?a ?b) = true |- _] => destruct (namedts_dec a b)
      | [H: productInModuleB_dec ?a ?b = left _ |- _] => destruct (productInModuleB_dec a b)

      | [H: context[match ?c with
                    | [] => _
                    | _::_ => _
                    end] |- _] =>
        let COND := fresh "COND" in
        destruct c eqn:COND
      | [H: context[match ?c with
                    | Some _ => _
                    | None => _
                    end] |- _] =>
        let COND := fresh "COND" in
        destruct c eqn:COND
      | [H: context[if ?c then _ else _] |- _] =>
        let COND := fresh "COND" in
        destruct c eqn:COND
      end;
  unfold Debug.debug_print_validation_process, Debug.debug_print in *;
  try subst; ss.

Ltac simtac := repeat simtac0.


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

Lemma updateAddAL_inject_locals
      id inv
      retval_src locals_src
      retval_tgt locals_tgt
      (RETVAL: genericvalues_inject.gv_inject inv.(InvMem.Rel.inject) retval_src retval_tgt)
      (LOCAL: inject_locals inv locals_src locals_tgt):
  <<LOCAL: inject_locals inv
                         (updateAddAL _ locals_src id retval_src)
                         (updateAddAL _ locals_tgt id retval_tgt)>>.
Proof.
  ii. destruct (id_dec i0 id).
  - subst. rewrite lookupAL_updateAddAL_eq in *. inv LU_SRC.
    esplits; eauto.
  - erewrite <- lookupAL_updateAddAL_neq in *; eauto.
Qed.

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

Lemma decide_nonzero_inject
      TD alpha decision
      val_src val_tgt
      (INJECT: genericvalues_inject.gv_inject alpha val_src val_tgt)
      (DECIDE_SRC: decide_nonzero TD val_src decision):
  decide_nonzero TD val_tgt decision.
Proof.
  inv DECIDE_SRC. inv INJECT; ss.
  destruct v1; ss. destruct gv1; ss. simtac. inv H. inv H0.
  apply inj_pair2 in H3. subst.
  econs; eauto. unfold GV2int.
  destruct (Nat.eq_dec (wz + 1) (Size.to_nat Size.One)); ss.
Qed.

Lemma decide_nonzero_unique
      TD val dec1 dec2
      (DEC1: decide_nonzero TD val dec1)
      (DEC2: decide_nonzero TD val dec2):
  dec1 = dec2.
Proof.
  inv DEC1. inv DEC2.
  rewrite INT in INT0. inv INT0. ss.
Qed.

Lemma decide_nonzero_inject_aux
      TD alpha
      val_src decision_src
      val_tgt decision_tgt
      (INJECT: genericvalues_inject.gv_inject alpha val_src val_tgt)
      (DECIDE_SRC: decide_nonzero TD val_src decision_src)
      (DECIDE_TGT: decide_nonzero TD val_tgt decision_tgt):
  decision_src = decision_tgt.
Proof.
  exploit decide_nonzero_inject; eauto. i.
  eapply decide_nonzero_unique; eauto.
Qed.

Lemma get_switch_branch_inject
      TD typ cls l0 alpha l
      val_src val_tgt
      (INJECT: genericvalues_inject.gv_inject alpha val_src val_tgt)
      (DECIDE_SRC: get_switch_branch TD typ val_src cls l0 = Some l):
  get_switch_branch TD typ val_tgt cls l0 = Some l.
Proof.
  destruct typ; ss.
  exploit genericvalues_inject.simulation__eq__GV2int; eauto. i.
  (* TODO: The definition of val_inject is WRONG!
   * https://github.com/snu-sf/llvmberry/issues/327
   *)
  rewrite x0 in *. eauto.
Qed.

Lemma get_switch_branch_inject_aux
      TD typ cls l0 alpha
      val_src l_src
      val_tgt l_tgt
      (INJECT: genericvalues_inject.gv_inject alpha val_src val_tgt)
      (DECIDE_SRC: get_switch_branch TD typ val_src cls l0 = Some l_src)
      (DECIDE_TGT: get_switch_branch TD typ val_tgt cls l0 = Some l_tgt):
  l_src = l_tgt.
Proof.
  exploit get_switch_branch_inject; eauto. i.
  rewrite DECIDE_TGT in x0. inv x0. ss.
Qed.
