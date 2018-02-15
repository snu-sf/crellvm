Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Import Opsem.

Require Import sflib.
Require Import paco.

Require Import GenericValues.
Require Import Nop.
Require AssnMem.
Require AssnState.
Require Import Inject.
Require Import SoundBase.
Require Import Simulation.
Require Import SimulationLocal.
Require Import TODOProof.
Require Import memory_props.
Require Import TODO.

Set Implicit Arguments.


Inductive sim_local_stack
          (conf_src conf_tgt:Config):
  forall (ecs_src ecs_tgt: ECStack) (inv:AssnMem.Rel.t), Prop :=
| sim_local_stack_nil
    inv:
    sim_local_stack conf_src conf_tgt nil nil inv
| sim_local_stack_cons
    ecs0_src ecs0_tgt inv0
    inv1
    func_src b_src id_src noret_src clattrs_src typ_src varg_src fun_src params_src cmds_src term_src locals_src allocas_src ecs_src mem_src uniqs_src privs_src
    func_tgt b_tgt id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt params_tgt cmds_tgt term_tgt locals_tgt allocas_tgt ecs_tgt mem_tgt uniqs_tgt privs_tgt
    (STACK: sim_local_stack conf_src conf_tgt ecs0_src ecs0_tgt inv0)
    (LE0: AssnMem.Rel.le inv0 inv1)
    (NORET: noret_src = noret_tgt)
    (CLATTRS: clattrs_src = clattrs_tgt)
    (TYP: typ_src = typ_tgt)
    (VARG: varg_src = varg_tgt)
    (UNIQS_SRC: forall mptr typ align val
                  (LOAD: mload conf_src.(CurTargetData) mem_src mptr typ align = Some val),
        AssnMem.gv_diffblock_with_blocks conf_src val uniqs_src)
    (UNIQS_GLOBALS_SRC: forall b, In b uniqs_src -> (inv1.(AssnMem.Rel.gmax) < b)%positive)
    (UNIQS_TGT: forall mptr typ align val
                  (LOAD: mload conf_tgt.(CurTargetData) mem_tgt mptr typ align = Some val),
        AssnMem.gv_diffblock_with_blocks conf_tgt val uniqs_tgt)
    (TGT_NOUNIQ: uniqs_tgt = [])
    (UNIQS_GLOBALS_TGT: forall b, In b uniqs_tgt -> (inv1.(AssnMem.Rel.gmax) < b)%positive)
    (PRIVS_SRC: forall b, In b privs_src -> AssnMem.private_block mem_src (AssnMem.Rel.public_src inv1.(AssnMem.Rel.inject)) b)
    (PRIVS_TGT: forall b, In b privs_tgt -> AssnMem.private_block mem_tgt (AssnMem.Rel.public_tgt inv1.(AssnMem.Rel.inject)) b)
    (LOCAL:
       forall inv' mem'_src mem'_tgt retval'_src retval'_tgt locals'_src
         (INCR: AssnMem.Rel.le (AssnMem.Rel.lift mem_src mem_tgt uniqs_src uniqs_tgt privs_src privs_tgt inv1) inv')
         (MEM: AssnMem.Rel.sem conf_src conf_tgt mem'_src mem'_tgt inv')
         (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject inv'.(AssnMem.Rel.inject)) retval'_src retval'_tgt)
         (VALID: valid_retvals mem'_src mem'_tgt retval'_src retval'_tgt)
         (RETURN_SRC: return_locals
                        conf_src.(CurTargetData)
                        retval'_src id_src noret_src typ_src
                        locals_src = Some locals'_src)
       ,
       exists inv'' idx' locals'_tgt,
         <<RETURN_TGT: return_locals
                         conf_tgt.(CurTargetData)
                         retval'_tgt id_tgt noret_tgt typ_tgt
                         locals_tgt = Some locals'_tgt>> /\
         <<MEMLE: AssnMem.Rel.le inv1 inv''>> /\
         forall
           (WF_SRC: wf_StateI conf_src
                              (mkState
                                 (mkEC func_src b_src cmds_src term_src locals'_src allocas_src)
                                 ecs_src mem'_src))
           (WF_TGT: wf_StateI conf_tgt
                              (mkState (mkEC func_tgt b_tgt cmds_tgt term_tgt locals'_tgt allocas_tgt)
                                       ecs_tgt mem'_tgt))
         ,
         <<SIM:
           sim_local
             conf_src conf_tgt ecs0_src ecs0_tgt
             inv'' idx'
             (mkState
                (mkEC func_src b_src cmds_src term_src locals'_src allocas_src)
                ecs_src
                mem'_src)
             (mkState
                (mkEC func_tgt b_tgt cmds_tgt term_tgt locals'_tgt allocas_tgt)
                ecs_tgt
                mem'_tgt)>>)
    inv2
    (LE1: AssnMem.Rel.le (AssnMem.Rel.lift mem_src mem_tgt uniqs_src uniqs_tgt privs_src privs_tgt inv1) inv2)
  :
    sim_local_stack
      conf_src conf_tgt
      ((mkEC func_src b_src ((insn_call id_src noret_src clattrs_src typ_src varg_src fun_src params_src)::cmds_src) term_src locals_src allocas_src) :: ecs_src)
      ((mkEC func_tgt b_tgt ((insn_call id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt params_tgt)::cmds_tgt) term_tgt locals_tgt allocas_tgt) :: ecs_tgt)
      inv2
.

Inductive sim_local_lift
          (conf_src conf_tgt:Config)
          (idx:nat) (st_src st_tgt: State): Prop :=
| sim_local_lift_intro
    ecs0_src ecs0_tgt inv0
    inv
    (CONF: inject_conf conf_src conf_tgt)
    (STACK: sim_local_stack conf_src conf_tgt ecs0_src ecs0_tgt inv0)
    (LOCAL: sim_local conf_src conf_tgt ecs0_src ecs0_tgt
                      inv idx st_src st_tgt)
    (LE0: AssnMem.Rel.le inv0 inv)
.

Inductive sim_products (conf_src conf_tgt:Config) (prod_src prod_tgt:products): Prop :=
| sim_products_intro
    (SIM_SOME: forall fid fdef_src
                      (FDEF_SRC: lookupFdefViaIDFromProducts prod_src fid = Some fdef_src),
        exists fdef_tgt,
          <<FDEF_TGT: lookupFdefViaIDFromProducts prod_tgt fid = Some fdef_tgt>> /\
                      <<SIM: sim_fdef conf_src conf_tgt fdef_src fdef_tgt>>)
    (SIM_NONE: forall fid
                      (FDEF_SRC: lookupFdefViaIDFromProducts prod_src fid = None),
        <<FDEF_TGT: lookupFdefViaIDFromProducts prod_tgt fid = None>>)
    (SIM_SOME_FDEC: forall fid header deck
                      (FDEC_SRC: lookupFdecViaIDFromProducts prod_src fid
                                 = Some (fdec_intro header deck)),
          <<FDEC_TGT: lookupFdecViaIDFromProducts prod_tgt fid = Some (fdec_intro header deck)>>)
.

Inductive sim_conf (conf_src conf_tgt:Config): Prop :=
| sim_conf_intro
    (SIM_PRODUCTS: sim_products conf_src conf_tgt conf_src.(CurProducts) conf_tgt.(CurProducts))
.

(* fid_same *)
Lemma lookupFdefViaPtr_inject_eq
      S TD Ps gl fs S0 TD0 Ps0 gl0 fs0 Mem1 inv_curr Mem0
      (MEM: AssnMem.Rel.sem
              (mkCfg S TD Ps gl fs)
              (mkCfg S0 TD0 Ps0 gl0 fs0)
              Mem0 Mem1 inv_curr)
      fid fptr rt la va lb fa
      (LOOKUP0: lookupFdefViaPtr Ps fs fptr = ret fdef_intro (fheader_intro fa rt fid la va) lb)
      fptr0 fid0 rt0 la0 va0 lb0 fa0
      (LOOKUP1: lookupFdefViaPtr Ps0 fs0 fptr0 = ret fdef_intro (fheader_intro fa0 rt0 fid0 la0 va0) lb0)
      (INJECT : genericvalues_inject.gv_inject (AssnMem.Rel.inject inv_curr) fptr fptr0)
  :
    <<EQID: fid = fid0>>
.
Proof.
  inv MEM. ss. unfold ftable_simulation in *.
  expl FUNTABLE.
  apply_all_once lookupFdefViaPtr_inversion. des.
  rewrite LOOKUP0 in *. rewrite LOOKUP1 in *. clarify.
  apply_all_once lookupFdefViaIDFromProducts_ideq. clarify.
Qed.

Lemma gv_inject_list_spec
      mi gvs gvs0
      (INJECT: list_forall2 (genericvalues_inject.gv_inject mi) gvs gvs0)
  :
  <<INJECT: genericvalues_inject.gv_list_inject mi gvs gvs0>>
.
Proof.
  ginduction gvs; ii; ss; inv INJECT.
  - econs; eauto.
  - econs; eauto.
    expl IHgvs.
Qed.

(* TODO: Move to more proper place *)
Axiom callExternalOrIntrinsics_inject: forall
  TD Gs
  S0 S1 Ps0 Ps1 Fs0 Fs1
  Mem0 fid rt la dck oresult0 tr Mem0' args0 args1
  assnmem0 Mem1
  (SRC_CALL: callExternalOrIntrinsics TD Gs Mem0 fid rt (args2Typs la) dck args0
             = ret (oresult0, tr, Mem0'))
  (ARGS_INJECT: list_forall2 (genericvalues_inject.gv_inject (AssnMem.Rel.inject assnmem0)) args0 args1)
  (MEM: AssnMem.Rel.sem (mkCfg S0 TD Ps0 Gs Fs0) (mkCfg S1 TD Ps1 Gs Fs1) Mem0 Mem1 assnmem0)
  ,
    exists oresult1 Mem1',
      (<<TGT_CALL: callExternalOrIntrinsics TD Gs Mem1 fid rt (args2Typs la) dck args1
                   = ret (oresult1, tr, Mem1')>>)
      /\ (exists assnmem1,
             (<<MEM: AssnMem.Rel.sem (mkCfg S0 TD Ps0 Gs Fs0) (mkCfg S1 TD Ps1 Gs Fs1) Mem0' Mem1' assnmem1>>)
             /\ (<<MEMLE: AssnMem.Rel.le assnmem0 assnmem1>>)
             /\ (<<VAL_INJECT: option_f2 (genericvalues_inject.gv_inject (AssnMem.Rel.inject assnmem1))
                                 oresult0 oresult1>>)
             /\ (<<VALID: valid_retvals Mem0' Mem1' oresult0 oresult1>>))
.

Lemma sim_local_stack_assnmem_le
      conf_src conf_tgt ecs0_src ecs0_tgt inv0
      (STACK: sim_local_stack conf_src conf_tgt ecs0_src ecs0_tgt inv0)
      inv1
      (LE: AssnMem.Rel.le inv0 inv1)
  :
    <<STACK: sim_local_stack conf_src conf_tgt ecs0_src ecs0_tgt inv1>>
.
Proof.
  red.
  inv STACK.
  - econs; eauto.
  - econs; eauto.
    etransitivity; eauto.
Qed.

(* TODO move to definition point *)
Lemma sop_star_preservation
      conf st0 st1 tr
      (WF_CONF: wf_ConfigI conf)
      (WF_ST: wf_StateI conf st0)
      (SOP_STAR: sop_star conf st0 st1 tr)
  :
    <<WF_ST: wf_StateI conf st1>>
.
Proof.
  ginduction SOP_STAR; ii; ss.
  eapply IHSOP_STAR; eauto.
  eapply preservation; eauto.
Qed.

Lemma GV2Vint_sim
      mi gv0 gv1
      (INJ: genericvalues_inject.gv_inject mi gv0 gv1)
      vi
      (SRCV: GV2Vint gv0 = Some vi)
  :
    <<TGTV: GV2Vint gv1 = Some vi>>
.
Proof.
  unfold GV2Vint in SRCV.
  des_ifs.
  inv INJ. inv H4. inv H3. apply inj_pair2 in H1. clarify.
Qed.

Lemma sim_local_lift_sim conf_src conf_tgt
      (SIM_CONF: sim_conf conf_src conf_tgt):
  (sim_local_lift conf_src conf_tgt) <3= (sim conf_src conf_tgt).
Proof.
  s. pcofix CIH.
  intros idx st_src st_tgt SIM. pfold.
  inv SIM. rename inv into inv_curr. rename inv0 into inv_stack.
  punfold LOCAL. inv LOCAL.
  - (* error *)
    econs 1; eauto.
  - (* return *)
    rename inv2 into inv_curr'.
    eapply sop_star_sim; eauto.
    destruct st2_src, st_tgt. ss.
    destruct EC0, EC1. ss. subst.
    eapply _sim_src_error. i.
    inv STACK.
    + (* final *)
      exploit nerror_stuck_final; eauto.
      { ii. des. inv H. }
      i. des. ss.
      unfold s_isFinalState in *. ss. des_ifs.
      exploit RET; eauto. i. des.
      inv VALID.
      eapply _sim_exit; eauto.
      * unfold s_isFinalState. ss.
        rewrite Heq. eauto.
      * unfold s_isFinalState. ss.
        rewrite RET_TGT.
        eapply GV2Vint_sim; eauto.
    + (* return *)
      rename inv0 into inv_stack0.
      rename inv1 into inv_stack1.
      rename inv_stack into inv_stack2.
      exploit nerror_nfinal_nstuck; eauto. i. des.
      inv x0. ss. rewrite returnUpdateLocals_spec in *. ss.
      simtac0. simtac0.
      exploit RET; eauto. i. des.
      apply _sim_step.
      { intro STUCK. apply STUCK. destruct conf_tgt. ss.
        inv CONF. ss. clarify.
        inv SIM_CONF. ss.
        exploit OpsemPP.free_allocas_not_stuck; []; intro FREE_ALLOCAS. des.
        destruct noret_tgt; simtac.
        - esplits.
          econs; ss; eauto.
          rewrite returnUpdateLocals_spec, RET_TGT. ss.
        - exploit genericvalues_inject.simulation__fit_gv; eauto.
          { inv MEM. eauto. }
          i. des.
          esplits. econs; ss; eauto.
          rewrite returnUpdateLocals_spec, RET_TGT. ss.
          rewrite x0. eauto.
      }
      i. expl preservation. rename preservation into WF_TGT_NEXT.
      inv STEP0. ss. rewrite returnUpdateLocals_spec in *. ss.
      inv CONF. ss. clarify.
      expl assnmem_free_allocas_assnmem_rel. rename assnmem_free_allocas_assnmem_rel into MEMFREE.
      des_ifs.
      * exploit LOCAL; try exact MEMFREE; eauto.
        { etransitivity; eauto. etransitivity; eauto. }
        { instantiate (2:= Some _).
          instantiate (1:= Some _).
          eassumption.
        }
        {
          exploit RET; eauto. i; des.
          eapply free_allocas_preserves_valid_retvals; eauto.
        }
        { ss. }
        clear LOCAL. intro LOCAL. des. simtac.


        assert(SRC_STEP:
                  sInsn (mkCfg S TD0 Ps gl0 fs)
                        (mkState (mkEC CurFunction0 CurBB0 [] (insn_return id2_src typ1_tgt ret2_src)
                                       Locals0 Allocas0)
                                 ((mkEC func_src b_src
                                        (insn_call id_src true clattrs_tgt typ_tgt
                                                   varg_tgt fun_src params_src :: cmds_src)
                                        term_src lc'' allocas_src) :: ecs_src)
                                 Mem0)
                        (mkState (mkEC func_src b_src cmds_src term_src lc'' allocas_src) ecs_src Mem')
                        E0).
        { econs; eauto.
          rewrite returnUpdateLocals_spec, COND. ss.
        }
        (* I tried dependent split, but it gives sInsn_indexed (not sInsn) which gives two cases when "inv"ed *)
        (* SRC_STEP is needed for preservation, to get WF_SRC_NEXT, which is needed to exploit LOCAL1 *)
        (* TODO: Can we do this in more smart way? *)

        (* Anyway, I will state how I get the above statement solely by tactic: *)
        (* do 3 eexists. *)
        (* split; [econs|]. apply dependent_split. *)
        (* { econs 1. econs; eauto. *)
        (*   rewrite returnUpdateLocals_spec, COND. ss. *)
        (* } *)
        (* { intro SRC_STEP. *) (* <----------------- this *)

        exploit LOCAL1.
        { eapply sop_star_preservation; eauto.
          eapply opsem_props.OpsemProps.sop_star_trans; try eassumption.
          econs; eauto. }
        { eauto. }
        intro LOCAL; des. clear LOCAL1.
        esplits; eauto.
        { econs 1. eauto. }
        { right. apply CIH. econs; eauto.
          - ss.
          - etransitivity; eauto.
        }
      * exploit LOCAL; try exact MEMFREE; eauto.
        { etransitivity; eauto. etransitivity; eauto. }
        { instantiate (2:= Some _).
          instantiate (1:= Some _).
          eassumption.
        }
        { exploit RET; eauto. i; des.
          eapply free_allocas_preserves_valid_retvals; eauto.
        }
        { ss. des_ifs. }
        clear LOCAL. intro LOCAL. des. simtac.

        assert(SRC_STEP:
                  sInsn (mkCfg S TD0 Ps gl0 fs)
                        (mkState (mkEC CurFunction0 CurBB0 [] (insn_return id2_src typ1_tgt ret2_src)
                                       Locals0 Allocas0)
                                 ((mkEC func_src b_src
                                        (insn_call id_src false clattrs_tgt typ_tgt
                                                   varg_tgt fun_src params_src :: cmds_src)
                                        term_src locals_src allocas_src) :: ecs_src)
                                 Mem0)
                        (mkState (mkEC func_src b_src cmds_src term_src
                                       (updateAddAL GenericValue locals_src id_src g1) allocas_src)
                                 ecs_src Mem')
                        E0).
        { econs; eauto.
          rewrite returnUpdateLocals_spec, COND. ss. des_ifs.
        }

        exploit LOCAL1.
        { eapply sop_star_preservation; eauto.
          eapply opsem_props.OpsemProps.sop_star_trans; try eassumption.
          econs; eauto. }
        { eauto. }
        intro LOCAL; des. clear LOCAL1.

        esplits; eauto.
        { econs 1. eauto. }
        { right. apply CIH. econs; eauto.
          - ss.
          - etransitivity; eauto.
        }
  - (* return_void *)
    eapply sop_star_sim; eauto.
    destruct st2_src, st_tgt. ss.
    destruct EC0, EC1. ss. subst.
    eapply _sim_src_error. i.
    inv STACK.
    + (* final *)
      exploit nerror_stuck_final; eauto.
      { ii. des. inv H. }
      i. des. ss.
      eapply _sim_exit; eauto.
    + (* return *)
      exploit nerror_nfinal_nstuck; eauto. i. des.
      inv x0. ss.
      apply _sim_step.
      { intro STUCK. apply STUCK. destruct conf_tgt. ss.
        inv CONF. ss. clarify.
        exploit OpsemPP.free_allocas_not_stuck; []; intro FREE_ALLOCAS. des.
        esplits. econs; ss; eauto. des_ifs.
      }
      i. expl preservation. rename preservation into WF_TGT_NEXT.
      inv STEP0. ss.
      inv CONF. ss. clarify.
      expl assnmem_free_allocas_assnmem_rel. rename assnmem_free_allocas_assnmem_rel into MEMFREE.
      des_ifs.
      * exploit LOCAL; try exact MEMFREE; eauto.
        { etransitivity; eauto. }
        { instantiate (2:= Some _).
          instantiate (1:= Some _).
          ss. (* it may put existential goals as nil/nil, but I don't care. It's return void *)
        }
        { econs; eauto; ss. }
        { ss. }
        clear LOCAL. intro LOCAL. des. simtac.

        exploit LOCAL1.
        { eapply sop_star_preservation; eauto.
          eapply opsem_props.OpsemProps.sop_star_trans; try eassumption.
          econs; eauto. }
        { eauto. }
        intro LOCAL; des. clear LOCAL1.

        esplits; eauto.
        { econs 1. econs; eauto. }
        { right. apply CIH. econs; eauto.
          - ss.
          - etransitivity; eauto.
        }
  - (* call *)
    eapply sop_star_sim; eauto.
    destruct st2_src, st_tgt. ss.
    destruct EC0, EC1. ss. subst.
    eapply _sim_src_error. i.
    exploit nerror_nfinal_nstuck; eauto. i. des.
    inv x0; ss.
    + (* call *)
      exploit FUN; eauto. i. des.
      exploit ARGS; eauto. i. des.
      apply _sim_step; ss.
      { ii. apply H. clear H.
        inv CONF; ss; clarify.
        inv SIM_CONF. ss.
        destruct conf_tgt; ss.
        unfold lookupFdefViaPtr in *. unfold mbind in *. des_ifs.
        inv SIM_PRODUCTS.
        expl SIM_SOME. ss.
        destruct fdef_tgt; ss. destruct fheader5; ss.
        exploit SIM; eauto.
        { econs; eauto. ss. }
        intro SIM_TGT; des. clear SIM_TGT0.
        inv SIM_TGT. ss. des_ifs.
        esplits; eauto.
        eapply sCall; eauto.
        - unfold lookupFdefViaPtr.
          unfold mbind.
          inv MEM. ss. unfold ftable_simulation in FUNTABLE. expl FUNTABLE.
          rewrite <- FUNTABLE0. rewrite Heq.
          rewrite FDEF_TGT. ss.
        - unfold getEntryBlock in *. ss.
      }
      i. expl preservation. rename preservation into WF_TGT_NEXT.
      inv STEP0; ss; cycle 1.
      { exfalso.
        rewrite FUN_TGT in *. clarify.
        clear - H18 H23 INJECT MEM SIM_CONF.
        unfold lookupFdefViaPtr, lookupExFdecViaPtr in *. unfold mbind in *. des_ifs.
        clear H23.

        assert(i0 = i1).
        { inv MEM. clear SRC TGT INJECT0 WF.
          expl FUNTABLE. clear FUNTABLE. ss. rewrite Heq in *. rewrite Heq1 in *. clarify.
        }
        clarify.

        inv SIM_CONF. ss. inv SIM_PRODUCTS.
        expl SIM_SOME. clear SIM.
        rewrite FDEF_TGT in *. clarify.
      }
      rewrite FUN_TGT in H22. inv H22.
      rewrite ARGS_TGT in H25. inv H25.

      (* assert (SIM_FDEF: sim_fdef conf_src conf_tgt  *)
      assert (FID_SAME: fid0 = fid).
      {
        expl lookupFdefViaPtr_inject_eq.
      }
      subst.
      exploit lookupFdefViaPtr_inversion; try exact H18. i. des.
      exploit lookupFdefViaIDFromProducts_ideq; try exact x1. i. subst.
      exploit lookupFdefViaPtr_inversion; try exact H23. i. des.
      exploit lookupFdefViaIDFromProducts_ideq; try exact x3. i. subst.

      inv SIM_CONF. inv SIM_PRODUCTS.
      exploit SIM_SOME; eauto.
      i. des.
      unfold sim_fdef in SIM.
      hexploit SIM; try apply assnmem_lift; eauto.
      { econs; eauto. }
      clear SIM. intro SIM; des.

      (* do 3 eexists. *)
      (* split; [econs|]. *)
      (* apply dependent_split. *)
      (* { econs 1. econs; eauto. } *)
      (* { i. Set Printing All. <----------------------- I get stmt from here *)
      assert(STEP_SRC:
               sInsn (mkCfg S TD Ps gl fs)
           (mkState
              (mkEC CurFunction0 CurBB0
                    ((insn_call id2_src noret1_tgt clattrs1_tgt typ1_tgt varg1_tgt fun2_src params2_src) ::
                    cmds2_src) Terminator0 Locals0 Allocas0) ECS0 Mem0)
           (mkState
              (mkEC (fdef_intro (fheader_intro fa rt fid la va) lb)
                    (l', (stmts_intro ps' cs' tmn')) cs' tmn' lc' [])
              ((mkEC CurFunction0 CurBB0
                    ((insn_call id2_src noret1_tgt clattrs1_tgt typ1_tgt varg1_tgt fun2_src params2_src) ::
                       cmds2_src) Terminator0 Locals0 Allocas0) :: ECS0)
              Mem0)
           E0).
      { econs; eauto. }
      
      esplits; eauto.
      * econs 1. eauto.
      * right. apply CIH.
        {
          eapply sim_local_lift_intro with
              (inv := (AssnMem.Rel.lift Mem0 Mem1 uniqs_src [] privs_src privs_tgt inv2)); ss.
          {
            econstructor 2 with (inv1 := inv2); [..|reflexivity]; ss; try eassumption.
            { etransitivity; eauto. }
            { s. i.
              hexploit RETURN; eauto. clear RETURN. intro RETURN. des.
              esplits; eauto.
              i. specialize (RETURN1 WF_SRC1). specialize (RETURN1 WF_TGT1).
              inv RETURN1; ss.
              eauto.
            }
          }
          {
            match goal with
            | [H: context[init_fdef] |- _ ] => inv H
            end.
            unfold getEntryBlock in *.
            des_ifs.
            ss. clarify.
            eapply SIM0.
            - splits; ss.
              eapply sop_star_preservation; eauto.
              eapply opsem_props.OpsemProps.sop_star_trans; try eassumption.
              econs; eauto.
            - splits; ss.
          }
          { reflexivity. }
        }
    + (* excall *)
      exploit FUN; eauto. i. des.
      exploit ARGS; eauto. i. des.
      inv CONF; ss; clarify.
      destruct conf_tgt; ss.
      exploit callExternalOrIntrinsics_inject; try apply assnmem_lift; eauto.
      { instantiate (1:= args1_tgt). ss. }
      i; des.

      apply _sim_step; ss.
      { ii. apply H. clear H.
        inv SIM_CONF. ss.
        unfold lookupExFdecViaPtr in *. unfold mbind in *. des_ifs.
        inv SIM_PRODUCTS.
        expl SIM_NONE.
        expl SIM_SOME_FDEC.

        rename H18 into FDEC_SRC. move FDEC_SRC at bottom.
        assert(i0= fid).
        {
          expl lookupFdecViaIDFromProducts_ideq.
        } des; clarify.

        move H21 at bottom. rename H21 into SRC_LOCALS.
        assert(exists Locals1', exCallUpdateLocals CurTargetData0 typ1_tgt noret1_tgt id1_tgt
                                                   oresult1 Locals1 = ret Locals1').
        {
          destruct noret1_tgt; ss.
          - esplits; eauto.
          - inv VAL_INJECT.
            + des_ifsH SRC_LOCALS.
              exploit genericvalues_inject.simulation__fit_gv; eauto.
              { apply MEM0. }
              i; des.
              rewrite x0.
              esplits; eauto.
            + des_ifs.
        } des.

        esplits; eauto.
        eapply sExCall; eauto.
        - unfold lookupExFdecViaPtr.
          unfold mbind.
          inv MEM. ss. unfold ftable_simulation in FUNTABLE. expl FUNTABLE.
          rewrite <- FUNTABLE0. rewrite Heq.
          rewrite SIM_NONE0.
          rewrite SIM_SOME_FDEC0. ss.
      }
      i. expl preservation. rename preservation into WF_TGT_NEXT.
      inv STEP0; ss.
      { exfalso. (* call excall mismatch *)
        clarify.
        rename H18 into SRC_LOOKUP.
        rename H27 into TGT_LOOKUP.
        clear - SIM_CONF MEM SRC_LOOKUP TGT_LOOKUP INJECT. rename funval1_tgt into fptr0. clear_tac.
        unfold lookupFdefViaPtr in *. unfold lookupExFdecViaPtr in *. unfold mbind in *. des_ifs.
        inv MEM. clear SRC TGT INJECT0 WF. ss.
        expl FUNTABLE.
        rewrite Heq in *. rewrite Heq0 in *. clarify.
        clear - TGT_LOOKUP Heq1 SIM_CONF.
        inv SIM_CONF. ss. inv SIM_PRODUCTS.
        expl SIM_NONE.
        clarify. }
      clarify.
      move TGT_CALL at bottom.

      rename Mem' into mem_src.
      rename Mem'0 into mem_tgt.
      rename H18 into FDEC_SRC.
      rename H27 into FDEC_TGT.
      move FDEC_SRC at bottom.
      move FDEC_TGT at bottom.
      assert(dck0 = dck /\ va0 = va /\ la0 = la /\ fid0 = fid /\ rt0 = rt /\ fa0 = fa).
      { inv SIM_CONF. inv SIM_PRODUCTS. ss.
        unfold lookupExFdecViaPtr in *. unfold mbind in *. des_ifs. ss.
        expl SIM_SOME_FDEC.
        assert(i0 = i1).
        {
          inv MEM. ss.
          expl FUNTABLE. rewrite FUNTABLE0 in *. clarify.
        } clarify.
      } des; clarify.



      {
        assert(RETURN_LOCALS: exists locals4_src, return_locals CurTargetData0 oresult id2_src noret1_tgt
                                     typ1_tgt Locals0 = ret locals4_src).
        {
          rewrite exCallUpdateLocals_spec in *.
          unfold return_locals in *.
          des_ifs; esplits; eauto.
        } des.

        hexploit RETURN; eauto.
        { inv VAL_INJECT; ss. }
        clear RETURN. intro RETURN. des.

        rewrite exCallUpdateLocals_spec in *.
        rewrite RETURN_LOCALS in *. rewrite RETURN_TGT in *. clarify.

        (* do 3 eexists. *)
        (* split; [econs|]. *)
        (* apply dependent_split. *)
        (* { econs 1. econs; eauto. *)
        (*   rewrite exCallUpdateLocals_spec; eauto. *)
        (* } *)
        (* { i. Set Printing All. *) (* <------------------- this *)
        (* TODO: this kind of asserting STEP_SRC is weird.. *)
        (* We may make lemma that replaces current goal's sInsn_indexed into sInsn *)
        (* If that is completed, we can get STEP_SRC via dependent_split, *)
        (* not by writing the whole fragile term *)
        assert(STEP_SRC:
                 sInsn (mkCfg S CurTargetData0 Ps Globals0 fs)
                       (mkState (mkEC CurFunction0 CurBB0
                                      ((insn_call id2_src noret1_tgt clattrs1_tgt
                                                  typ1_tgt varg1_tgt fun2_src params2_src) :: cmds2_src)
                                      Terminator0 Locals0 Allocas0)
                                ECS0 Mem0)
                       (mkState (mkEC CurFunction0 CurBB0 cmds2_src Terminator0 lc' Allocas0) ECS0 mem_src)
                       event).
        { econs; eauto.
          rewrite exCallUpdateLocals_spec; eauto.
        }

        hexploit RETURN1; eauto.
        { eapply sop_star_preservation; eauto.
          eapply opsem_props.OpsemProps.sop_star_trans; try eassumption.
          econs; eauto.
        }
        intro SIM; des.

        esplits; eauto.
        * econs 1. econs; eauto.
          rewrite exCallUpdateLocals_spec; eauto.
        * right. apply CIH.
          econs; try reflexivity; swap 2 3.
          { ss. }
          {
            inv SIM; eauto; ss.
          }
          {
            eapply sim_local_stack_assnmem_le; eauto.
            etransitivity; eauto. etransitivity; eauto.
          }
      }
  - (* step *)
    econs 3; ss. i. exploit STEP; eauto. i. des.
    inv SIM; [|done].
    esplits; eauto. right.
    apply CIH.
    econs; [..|M]; Mskip eauto.
    { etransitivity; eauto. }
Unshelve.
{ by econs; eauto. }
{ by econs; eauto. }
Qed.
