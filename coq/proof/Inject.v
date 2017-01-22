Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.
Require Import vellvm.
Require Import opsem.
Require Import genericvalues_inject.

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

Lemma targetdata_dec
      (TD_src TD_tgt:TargetData):
  {TD_src = TD_tgt} + {TD_src <> TD_tgt}.
Proof.
  decide equality.
  - apply namedts_dec.
  - apply layouts_dec.
Qed.
Hint Resolve targetdata_dec: EqDecDb.

Lemma app_inject: forall mi gv1 gv2 gv1' gv2'
    (IN1: gv_inject mi gv1 gv1')
    (IN2: genericvalues_inject.gv_inject mi gv2 gv2'),
  gv_inject mi (gv1 ++ gv2) (gv1' ++ gv2').
Proof.
  induction gv1.
  - i; destruct gv1'; [|inv IN1]; eauto.
  - i. destruct gv1'; inv IN1.
    econs; eauto.
Qed.

Lemma uninits_inject
      n maxb mi Mem1 Mem2
      (Hwfsim: genericvalues_inject.wf_sb_mi maxb mi Mem1 Mem2):
  genericvalues_inject.gv_inject mi (uninits n) (uninits n).
Proof.
  i; induction n; econs; eauto. 
Qed.

Lemma repeatGV_inject
      mi n g g'
      (INJ: genericvalues_inject.gv_inject mi g g'):
  genericvalues_inject.gv_inject mi (repeatGV g n) (repeatGV g' n).
Proof.
  induction n; s; eauto using app_inject.
Qed.

Lemma zeroconst2GV_aux_inject
      TD maxb mi Mem1 Mem2 (Hwfsim: genericvalues_inject.wf_sb_mi maxb mi Mem1 Mem2)
      acc (Hnc: forall id5 gv5, 
              lookupAL _ acc id5 = Some (Some gv5) ->
              genericvalues_inject.gv_inject mi gv5 gv5)
      t gv (Hz: zeroconst2GV_aux TD acc t = Some gv):
  genericvalues_inject.gv_inject mi gv gv.
Proof.
  revert_until t.
  induction t using typ_ind_gen; i; ss; try by inv Hz; econs; eauto.
  - destruct floating_point5; inv Hz; econs; eauto.
  - destruct sz5 as [|s]; try solve [uniq_result; auto using gv_inject_uninits].
    inv_mbind; exploit IHt; eauto.
    eauto 10 using gv_inject_app, uninits_inject, repeatGV_inject.
  - inv_mbind.  
    destruct g; inv H0; [by econs; eauto|].
    revert HeqR; generalize (p::g); clear p g; intro gv; i.
    revert_until l0; induction l0; s; i; [by inv HeqR; eauto|].
    inv IH; inv_mbind; eapply gv_inject_app.
      by symmetry_ctx; eauto.
      eapply gv_inject_app; eauto using uninits_inject.
  - inv_mbind; symmetry_ctx; eauto.
Qed.

Lemma zeroconsts2GV_aux_inject
      TD maxb mi Mem1 Mem2 (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2)
      acc (Hnc: forall id5 gv5, 
              lookupAL _ acc id5 = Some (Some gv5) ->
              gv_inject mi gv5 gv5)
      lt gv (Hz: zeroconsts2GV_aux TD acc lt = Some gv):
  gv_inject mi gv gv.
Proof.
  revert_until lt. induction lt; s; i; [by inv Hz; econs; eauto|].
  inv_mbind; symmetry_ctx; exploit IHlt; eauto; intro IJT.
  eapply zeroconst2GV_aux_inject in HeqR0; eauto.
  eauto using gv_inject_app, uninits_inject.
Qed.

Lemma zeroconst2GV_for_namedts_inject
      TD l maxb mi Mem1 Mem2 (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2)
      n id gv (LU: lookupAL (monad GenericValue) (zeroconst2GV_for_namedts TD l n) id = ret (ret gv)):
  gv_inject mi gv gv.
Proof.
  revert_until n. induction n; ss.
  i; destruct a; ss. destruct (eq_dec id0 i0); subst; eauto.
  inv LU; inv_mbind; symmetry_ctx.
  destruct g; inv H1; [by econs; eauto|].
  eapply zeroconsts2GV_aux_inject; eauto.
Qed.

Lemma zeroconst2GV_inject
      maxb mi Mem1 Mem2 gv td t
      (WF: wf_sb_mi maxb mi Mem1 Mem2)
      (ZERO: zeroconst2GV td t = Some gv):
  gv_inject mi gv gv.
Proof. 
  destruct td. 
  eauto using zeroconst2GV_aux_inject, zeroconst2GV_for_namedts_inject.
Qed.

Lemma cgv2gv_inject
      maxb mi Mem1 Mem2 g t
      (WF: wf_sb_mi maxb mi Mem1 Mem2)
      (INJECT: gv_inject mi g g):
  gv_inject mi (cgv2gv g t) (cgv2gv g t).
Proof.
  destruct g; eauto.
Qed.

Lemma cgv2gv_inject_rev
      maxb mi Mem1 Mem2 g t
      (WF: wf_sb_mi maxb mi Mem1 Mem2)
      (INJECT: gv_inject mi (cgv2gv g t) (cgv2gv g t)):
  gv_inject mi g g.
Proof.
  destruct g; eauto.
Qed.

Lemma const2GV_list_inject
      maxb mi Mem1 Mem2 TD gl t ll gv
      (Hwf: wf_sb_mi maxb mi Mem1 Mem2)
      (IH: Forall
             (fun c : const =>
                forall gv : GenericValue,
                  const2GV TD gl c = ret gv -> gv_inject mi gv gv) ll)
      (Hgv: _list_const_struct2GV_ _const2GV TD gl ll = ret (gv, t)):
  gv_inject mi gv gv.
Proof.
  revert ll t gv IH Hgv; induction ll.
  - i; inv Hgv; eauto using uninits_inject.
  - i; inv IH; unfold const2GV in Hgv; s in Hgv; inv_mbind.
    eapply gv_inject_app.
    + eapply cgv2gv_inject_rev; eauto.
      eapply H1; unfold const2GV; rewrite <- HeqR0; eauto.
    + eapply gv_inject_app; eauto using uninits_inject.
Qed.

Lemma const2GV_inject
      maxb mi Mem Mem' TD gl c gv
      (Hwf: wf_sb_mi maxb mi Mem Mem')
      (Hgl: wf_globals maxb gl)
      (Hgv: const2GV TD gl c = Some gv):
  gv_inject mi gv gv.
Proof.
  revert gv Hgv; induction c using const_ind_gen
  ; [M|M|M|M|M| |M|M|M|M|M|M|M|M|M|M|M|M|M]; Mdo unfold const2GV; s; i; inv_mbind.
  - inv H0; apply symmetry in HeqR0.
    eauto using zeroconst2GV_inject, cgv2gv_inject.
  - inv Hgv; econs; eauto.
  - inv H0; destruct floating_point5; inv HeqR; s; econs; eauto.
  - inv H0; symmetry_ctx; eauto using cgv2gv_inject, gv_inject_gundef.
  - inv Hgv; inv Hwf; econs; eauto.
  - i; revert l0 IH gv Hgv; induction l0.
    + i; inv Hgv; eauto using uninits_inject.
      econs; eauto.
    + i; inv IH; unfold const2GV in Hgv; s in Hgv; inv_mbind.
      destruct typ_dec; subst; [|done].
      inv_mbind; inv H0.
      eapply cgv2gv_inject; eauto.
      eapply gv_inject_app.
      * eapply cgv2gv_inject_rev; eauto.
        eapply H1; unfold const2GV; rewrite <- HeqR0; eauto.
      * eapply gv_inject_app; eauto using uninits_inject.
        specialize (IHl0 H2).
        unfold const2GV in IHl0; s in IHl0.
        rewrite <- HeqR in IHl0.
        destruct l0; [by inv HeqR; eauto|].
        s in IHl0; eapply cgv2gv_inject_rev; eauto.
  - inv H0; eapply cgv2gv_inject; eauto.
    destruct typ_eq_list_typ; [|by inv H1].
    destruct g; inv H1; eauto using uninits_inject.
    revert HeqR0; generalize (p::g) as gg; clear p g; i.
    eauto using const2GV_list_inject.
  - inv H0; eapply cgv2gv_inject; eauto.
    symmetry_ctx; eauto using global_gv_inject_refl.
  - inv H0; eapply cgv2gv_inject; eauto.
    symmetry_ctx; eapply simulation__mtrunc_refl, HeqR.
    unfold const2GV in IHc; rewrite HeqR0 in IHc.
    eauto using cgv2gv_inject_rev.
  - inv H0; eapply cgv2gv_inject; eauto.
    symmetry_ctx; eapply simulation__mext_refl, HeqR.
    unfold const2GV in IHc; rewrite HeqR0 in IHc.
    eauto using cgv2gv_inject_rev.
  - inv H0; eapply cgv2gv_inject; eauto.
    symmetry_ctx; eapply simulation__mcast_refl, HeqR.
    unfold const2GV in IHc; rewrite HeqR0 in IHc.
    eauto using cgv2gv_inject_rev.
  - apply symmetry in H1; inv H0; eapply cgv2gv_inject; eauto.
    destruct t; tinv H1.
    remember (getConstGEPTyp l0 (typ_pointer t)) as R2.
    destruct R2; tinv H1.
    remember (GV2ptr TD (getPointerSize TD) g) as R3.
    destruct R3; tinv H1.
    remember (intConsts2Nats TD l0) as R4.
    destruct R4; tinv H1.
    remember (mgep TD t v l1) as R5.
    destruct R5; inv H1.
    symmetry_ctx; unfold const2GV in IHc; rewrite HeqR0 in IHc.
    eapply simulation__mgep_refl with (mi:=mi) in HeqR5 
    ; eauto using GV2ptr_refl, cgv2gv_inject_rev.
    unfold ptr2GV, val2GV. simpl. auto.

    inv_mbind. symmetry_ctx. 
    eauto using gv_inject_gundef.
    inv_mbind. symmetry_ctx. 
    eauto using gv_inject_gundef.
    inv_mbind. symmetry_ctx.
    eauto using gv_inject_gundef.
  - inv H0; unfold const2GV in IHc2, IHc3; destruct p0, p1.
    rewrite <- HeqR in IHc2; rewrite <- HeqR1 in IHc3.
    destruct isGVZero; inv H1; eauto.
  - inv H0; eapply cgv2gv_inject; eauto.
    unfold const2GV in IHc1, IHc2.
    rewrite <- HeqR0 in IHc1; rewrite <- HeqR in IHc2.
    apply symmetry in HeqR1.
    eapply simulation__micmp_refl, HeqR1; eauto using cgv2gv_inject_rev.
  - inv H0; eapply cgv2gv_inject; eauto.
    destruct t; try by inv H1.
    inv_mbind; unfold const2GV in IHc1, IHc2.
    rewrite <- HeqR0 in IHc1; rewrite <- HeqR in IHc2.
    apply symmetry in HeqR1.
    eapply simulation__mfcmp_refl, HeqR1; eauto using cgv2gv_inject_rev.

  - inv H0; eapply cgv2gv_inject; eauto. 
    unfold const2GV in IHc; rewrite <-HeqR0 in IHc.
    specialize (IHc _ eq_refl); eapply cgv2gv_inject_rev in IHc; eauto.
    eapply simulation__extractGenericValue_refl; eauto.  

  - inv H0; eapply cgv2gv_inject; eauto. 
    unfold const2GV in IHc1, IHc2; rewrite <-HeqR0 in IHc1; rewrite <-HeqR in IHc2.
    specialize (IHc1 _ eq_refl); eapply cgv2gv_inject_rev in IHc1; eauto.
    specialize (IHc2 _ eq_refl); eapply cgv2gv_inject_rev in IHc2; eauto.
    symmetry_ctx; eapply simulation__insertGenericValue_refl in HeqR1; eauto.

  - inv H0; eapply cgv2gv_inject; eauto. 
    destruct t; try by inv H1.
    inv_mbind.
    unfold const2GV in IHc1, IHc2; rewrite <-HeqR0 in IHc1; rewrite <-HeqR in IHc2.
    specialize (IHc1 _ eq_refl); eapply cgv2gv_inject_rev in IHc1; eauto.
    specialize (IHc2 _ eq_refl); eapply cgv2gv_inject_rev in IHc2; eauto.
    symmetry_ctx; eapply simulation__mbop_refl in HeqR1; eauto.

  - inv H0; eapply cgv2gv_inject; eauto. 
    destruct t; try by inv H1.
    inv_mbind.
    unfold const2GV in IHc1, IHc2; rewrite <-HeqR0 in IHc1; rewrite <-HeqR in IHc2.
    specialize (IHc1 _ eq_refl); eapply cgv2gv_inject_rev in IHc1; eauto.
    specialize (IHc2 _ eq_refl); eapply cgv2gv_inject_rev in IHc2; eauto.
    symmetry_ctx; eapply simulation__mfbop_refl in HeqR1; eauto.
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
      conf_src mem_src locals_src gval_src
      conf_tgt mem_tgt locals_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (LOCALS: inject_locals inv locals_src locals_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (SRC: getOperandValue conf_src.(CurTargetData) val locals_src (Globals conf_src) = Some gval_src):
  exists gval_tgt,
    <<TGT: getOperandValue conf_tgt.(CurTargetData) val locals_tgt (Globals conf_tgt) = Some gval_tgt>> /\
           <<INJECT: genericvalues_inject.gv_inject inv.(InvMem.Rel.inject) gval_src gval_tgt>>.
Proof.
  destruct val; ss.
  - exploit LOCALS; eauto.
  - destruct conf_src, conf_tgt. inv CONF. ss. subst.
    esplits; eauto.
    inv MEM. inv TGT.
    eapply const2GV_inject; eauto.
Qed.

Lemma inject_locals_params2GVs
      inv0 args0
      conf_src mem_src locals_src gvs_param_src
      conf_tgt mem_tgt locals_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (LOCALS: inject_locals inv0 locals_src locals_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv0)
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

(* define with "Definition"? How is it good/bad compared with Inductive? *)
(* ex: Definition -> sem_lessdef *)
(* ex: Inductive -> sem_unique *)
(* @jeehoonkang noted that # of premises can matter, it may be concatenated with "/\" when using "Definition" *)
(* Also he mentioned econs/exploit's behavior may differ *)
Inductive GVsMap_inject meminj gvs0 gvs1: Prop :=
| GVsMap_inject_intro
    (INJECT:
       forall id gv0
       (LOOKUP: lookupAL GenericValue gvs0 id = ret gv0),
         exists gv1, lookupAL GenericValue gvs1 id = ret gv1 /\ gv_inject meminj gv0 gv1)
.

(* Definition GVsMap_inject *)
(*            meminj gvs0 gvs1 *)
(*   := *)
(*     forall id gv0 (LOOKUP: lookupAL GenericValue gvs0 id = ret gv0), *)
(*     <<LOOKUP: exists gv1, lookupAL GenericValue gvs1 id = ret gv1 /\ gv_inject meminj gv0 gv1>> *)
(* . *)

(* Definition GVsMap_inject *)
(*            meminj gvs0 gvs1 id gv0 *)
(*            (LOOKUP: lookupAL GenericValue gvs0 id = ret gv0) *)
(*   := *)
(*     <<LOOKUP: exists gv1, lookupAL GenericValue gvs1 id = ret gv1 /\ gv_inject meminj gv0 gv1>> *)
(* . *)

Ltac des_lookupAL_updateAddAL :=
  repeat match goal with
         | [ H: context[lookupAL ?t (updateAddAL ?t _ ?idA _) ?idB] |- _ ] =>
           destruct (eq_atom_dec idB idA);
           [ss; clarify; rewrite lookupAL_updateAddAL_eq in H |
            ss; clarify; rewrite <- lookupAL_updateAddAL_neq in H]; ss; clarify
         | [ |- context[lookupAL ?t (updateAddAL ?t _ ?idA _) ?idB] ] =>
           destruct (eq_atom_dec idB idA);
           [ss; clarify; rewrite lookupAL_updateAddAL_eq |
            ss; clarify; rewrite <- lookupAL_updateAddAL_neq]; ss; clarify
         end.

Lemma gv_inject_initialize_frames
      al bl meminj TD la g
  (INJECT: list_forall2 (gv_inject meminj) al bl)
  (FRAMES: _initializeFrameValues TD la al [] = ret g)
  gmax mem_src mem_tgt
  (WASABI: wf_sb_mi gmax meminj mem_src mem_tgt)
  :
    <<FRAMES: exists g',
      (_initializeFrameValues TD la bl [] = ret g')
        /\ GVsMap_inject meminj g g'>>
.
(* use meminj instead inv? just conservatively (inv have more info) *)
Proof.
  red.
  generalize dependent la.
  generalize dependent g.
  induction INJECT; ii; ss; des.
  - rewrite FRAMES.
    Print _initializeFrameValues.
    esplits; eauto.
    generalize dependent g.
    induction la; ii; ss; des; clarify; ss.
    des_ifs.
    exploit IHla; eauto; []; ii; des.
    inv x.
    econs; eauto. ii.
    des_lookupAL_updateAddAL.
    + esplits; eauto. eapply gv_inject_gundef; eauto.
    + exploit INJECT; eauto.
  -
    destruct la.
    { ss. clarify. esplits; eauto. econs; eauto. ii; des. inv LOOKUP. }
    cbn in FRAMES. des_ifs.
    exploit IHINJECT; eauto; []; ii; des.
    cbn.
    exploit simulation__fit_gv; eauto.
    ii; des.
    des_ifs.
    esplits; eauto.
    econs; eauto.
    ii.
    des_lookupAL_updateAddAL.
    + esplits; eauto.
    + inv x0. eapply INJECT0; eauto.
Qed.

Lemma locals_init
      inv la gvs_src
      args_src args_tgt
      conf_src conf_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (ARGS: list_forall2 (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) args_src args_tgt)
      (LOCALS_SRC : initLocals (CurTargetData conf_src) la args_src = Some gvs_src)
      mem_src mem_tgt
      (WASABI: wf_sb_mi inv.(InvMem.Rel.gmax) inv.(InvMem.Rel.inject) mem_src mem_tgt)
  :
  exists gvs_tgt,
    << LOCALS_TGT : initLocals (CurTargetData conf_tgt) la args_tgt = Some gvs_tgt >> /\
                    << LOCALS: inject_locals inv gvs_src gvs_tgt >>.
Proof.
  unfold initLocals in *.
  revert gvs_src LOCALS_SRC. induction ARGS; ss.
  -
    induction la.
    + ii. cbn in *. clarify.
      esplits; eauto.
      ii. inv LU_SRC.
    +
      ii.
      cbn in LOCALS_SRC. des_ifs.
      exploit IHla; eauto; []; ii; des.
      cbn in *. rewrite LOCALS_TGT. inv CONF. rewrite <- TARGETDATA. rewrite Heq0.
      esplits; eauto.
      ii.
      des_lookupAL_updateAddAL.
      * esplits; eauto.
        eapply gv_inject_gundef; eauto.
      * exploit LOCALS; eauto.
  -
    ii.
    destruct la; clarify.
    { ss. inv LOCALS_SRC. esplits; eauto. ii. inv LU_SRC. }
    cbn in LOCALS_SRC. des_ifs.
    cbn. inv CONF. rewrite <- TARGETDATA. clear TARGETDATA.
    exploit gv_inject_initialize_frames; eauto; []; ii; des. inv x1.
    exploit simulation__fit_gv; eauto.
    ii; des.
    des_ifs.
    esplits; eauto.
    ii.
    des_lookupAL_updateAddAL; clear IHARGS.
    + esplits; eauto.
    + exploit INJECT; eauto.
Qed.

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
