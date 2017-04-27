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
Require InvMem.
Require InvState.
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
  forall (ecs_src ecs_tgt: ECStack) (inv:InvMem.Rel.t), Prop :=
| sim_local_stack_nil
    inv:
    sim_local_stack conf_src conf_tgt nil nil inv
| sim_local_stack_cons
    ecs0_src ecs0_tgt inv0
    inv
    func_src b_src id_src noret_src clattrs_src typ_src varg_src fun_src params_src cmds_src term_src locals_src allocas_src ecs_src mem_src uniqs_src privs_src
    func_tgt b_tgt id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt params_tgt cmds_tgt term_tgt locals_tgt allocas_tgt ecs_tgt mem_tgt uniqs_tgt privs_tgt
    (STACK: sim_local_stack conf_src conf_tgt ecs0_src ecs0_tgt inv0)
    (LE0: InvMem.Rel.le inv0 inv)
    (NORET: noret_src = noret_tgt)
    (CLATTRS: clattrs_src = clattrs_tgt)
    (TYP: typ_src = typ_tgt)
    (VARG: varg_src = varg_tgt)
    (UNIQS_SRC: forall mptr typ align val
                  (LOAD: mload conf_src.(CurTargetData) mem_src mptr typ align = Some val),
        InvMem.gv_diffblock_with_blocks conf_src val uniqs_src)
    (UNIQS_GLOBALS_SRC: forall b, In b uniqs_src -> (inv.(InvMem.Rel.gmax) < b)%positive)
    (UNIQS_TGT: forall mptr typ align val
                  (LOAD: mload conf_tgt.(CurTargetData) mem_tgt mptr typ align = Some val),
        InvMem.gv_diffblock_with_blocks conf_tgt val uniqs_tgt)
    (UNIQS_GLOBALS_TGT: forall b, In b uniqs_tgt -> (inv.(InvMem.Rel.gmax) < b)%positive)
    (PRIVS_SRC: forall b, In b privs_src -> InvMem.private_block mem_src (InvMem.Rel.public_src inv.(InvMem.Rel.inject)) b)
    (PRIVS_TGT: forall b, In b privs_tgt -> InvMem.private_block mem_tgt (InvMem.Rel.public_tgt inv.(InvMem.Rel.inject)) b)
    (LOCAL:
       forall inv' mem'_src mem'_tgt retval'_src retval'_tgt locals'_src
         (INCR: InvMem.Rel.le (InvMem.Rel.lift mem_src mem_tgt uniqs_src uniqs_tgt privs_src privs_tgt inv) inv')
         (MEM: InvMem.Rel.sem conf_src conf_tgt mem'_src mem'_tgt inv')
         (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject inv'.(InvMem.Rel.inject)) retval'_src retval'_tgt)
         (RETURN_SRC: return_locals
                        conf_src.(CurTargetData)
                        retval'_src id_src noret_src typ_src
                        locals_src = Some locals'_src),
       exists inv'' idx' locals'_tgt,
         <<RETURN_TGT: return_locals
                         conf_tgt.(CurTargetData)
                         retval'_tgt id_tgt noret_tgt typ_tgt
                         locals_tgt = Some locals'_tgt>> /\
         <<MEMLE: InvMem.Rel.le inv inv''>> /\
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
                mem'_tgt)>>):
    sim_local_stack
      conf_src conf_tgt
      ((mkEC func_src b_src ((insn_call id_src noret_src clattrs_src typ_src varg_src fun_src params_src)::cmds_src) term_src locals_src allocas_src) :: ecs_src)
      ((mkEC func_tgt b_tgt ((insn_call id_tgt noret_tgt clattrs_tgt typ_tgt varg_tgt fun_tgt params_tgt)::cmds_tgt) term_tgt locals_tgt allocas_tgt) :: ecs_tgt)
      (InvMem.Rel.lift mem_src mem_tgt uniqs_src uniqs_tgt privs_src privs_tgt inv)
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
    (LE0: InvMem.Rel.le inv0 inv)
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
        (* exists header_tgt, *)
          <<FDEC_TGT: lookupFdecViaIDFromProducts prod_tgt fid = Some (fdec_intro header deck)>>)
.

Inductive sim_conf (conf_src conf_tgt:Config): Prop :=
| sim_conf_intro
    (SIM_PRODUCTS: sim_products conf_src conf_tgt conf_src.(CurProducts) conf_tgt.(CurProducts))
.

(* fid_same *)
Lemma lookupFdefViaPtr_inject_eq
      S TD Ps gl fs S0 TD0 Ps0 gl0 fs0 Mem1 inv_curr Mem0
      (MEM: InvMem.Rel.sem
              (mkCfg S TD Ps gl fs)
              (mkCfg S0 TD0 Ps0 gl0 fs0)
              Mem0 Mem1 inv_curr)
      fid fptr rt la va lb fa
      (LOOKUP0: lookupFdefViaPtr Ps fs fptr = ret fdef_intro (fheader_intro fa rt fid la va) lb)
      fptr0 fid0 rt0 la0 va0 lb0 fa0
      (LOOKUP1: lookupFdefViaPtr Ps0 fs0 fptr0 = ret fdef_intro (fheader_intro fa0 rt0 fid0 la0 va0) lb0)
      (INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject inv_curr) fptr fptr0)
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

(* call & excall mismatch *)
Lemma lookupExFdecViaPtr_inject
      conf_src conf_tgt Mem1 inv_curr Mem0
      (SIM_CONF: sim_conf conf_src conf_tgt)
      (MEM: InvMem.Rel.sem
              conf_src conf_tgt
              Mem0 Mem1 inv_curr)
      fptr res0
      (LOOKUP0: lookupExFdecViaPtr conf_src.(CurProducts) conf_src.(FunTable) fptr = ret res0)
      fptr0 res1
      (LOOKUP1: lookupFdefViaPtr conf_tgt.(CurProducts) conf_tgt.(FunTable) fptr0 = ret res1)
      (INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject inv_curr) fptr fptr0)
  :
    False
.
Proof.
  unfold lookupFdefViaPtr in *. unfold lookupExFdecViaPtr in *. unfold mbind in *. des_ifs.
  inv MEM. clear SRC TGT INJECT0 WF. ss.
  expl FUNTABLE.
  rewrite Heq0 in *. rewrite Heq in *. clarify.
  inv SIM_CONF. inv SIM_PRODUCTS.
  expl SIM_NONE.
  clarify.
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
Theorem callExternalOrIntrinsics_inject
  TD Gs
  S0 S1 Ps0 Ps1 Fs0 Fs1
  Mem0 fid rt la dck oresult0 e0 Mem0' args0 args1
  invmem0 Mem1
  (SRC_CALL: callExternalOrIntrinsics TD Gs Mem0 fid rt (args2Typs la) dck args0
             = ret (oresult0, e0, Mem0'))
  (ARGS_INJECT: list_forall2 (genericvalues_inject.gv_inject (InvMem.Rel.inject invmem0)) args0 args1)
  (MEM: InvMem.Rel.sem (mkCfg S0 TD Ps0 Gs Fs0) (mkCfg S1 TD Ps1 Gs Fs1) Mem0 Mem1 invmem0)
  :
    exists oresult1 e1 Mem1',
      (<<TGT_CALL: callExternalOrIntrinsics TD Gs Mem1 fid rt (args2Typs la) dck args1
                   = ret (oresult1, e1, Mem1')>>)
      /\ (<<EV_INJECT: match_traces (globals2Genv TD Gs) e0 e1>>)
      /\ (<<MEM: exists invmem1, InvMem.Rel.sem (mkCfg S0 TD Ps0 Gs Fs0) (mkCfg S1 TD Ps1 Gs Fs1)
                                                Mem0 Mem1 invmem1 /\ InvMem.Rel.le invmem0 invmem1>>)
.
Proof.
Admitted.

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
    Require Program.
    inv STACK.
    + (* final *)
      exploit nerror_stuck_final; eauto.
      { ii. des. inv H. }
      i. des. ss. exploit RET; eauto. i. des.
      eapply _sim_exit; eauto.
    + (* return *)
      rename inv into inv_stack.
      rename inv0 into inv_stack0.
      exploit nerror_nfinal_nstuck; eauto. i. des.
      inv x0. ss. rewrite returnUpdateLocals_spec in *. ss.
      simtac0. simtac0.
      exploit RET; eauto. i. des.
      (expl SoundBase.mem_le_private_parent (try exact MEMLE));
        rewrite mem_le_private_parent in *; clear mem_le_private_parent;
          rewrite mem_le_private_parent0 in *; clear mem_le_private_parent0.
      apply _sim_step.
      { intro STUCK. apply STUCK. destruct conf_tgt. ss.
        inv CONF. ss. clarify.
        inv SIM_CONF. ss.
        eapply inject_allocas_inj_incr in ALLOCAS; eauto.
        exploit inject_allocas_free_allocas; eauto.
        intro FREE_ALLOCAS; des.
        destruct noret_tgt; simtac.
        - esplits. econs; ss; eauto.
          + rewrite returnUpdateLocals_spec, RET_TGT. ss.
        - exploit genericvalues_inject.simulation__fit_gv; eauto.
          { inv MEM. eauto. }
          i. des.
          esplits. econs; ss; eauto.
          + rewrite returnUpdateLocals_spec, RET_TGT. ss.
            rewrite x0. eauto.
      }
      i. inv STEP0. ss. rewrite returnUpdateLocals_spec in *. ss.
      inv CONF. ss. clarify.
      destruct noret_tgt; simtac.
      *
        exploit invmem_free_allocas_invmem_rel; eauto.
        { eapply inject_allocas_mem_le in ALLOCAS; eauto. }
        intro MEMFREE; des.
        exploit LOCAL; try exact MEMFREE; eauto.
        { etransitivity; eauto. }
        { instantiate (2:= Some _).
          instantiate (1:= Some _).
          ss.
        }
        { ss. }
        i. des. simtac.
        esplits; eauto.
        { econs 1. econs; eauto.
          rewrite returnUpdateLocals_spec, COND. ss.
        }
        { right. apply CIH. econs; try exact SIM; eauto.
          - ss.
          - etransitivity; eauto.
        }
      *
        exploit invmem_free_allocas_invmem_rel; eauto.
        { eapply inject_allocas_mem_le in ALLOCAS; eauto. }
        intro MEMFREE; des.
        exploit LOCAL; try exact MEMFREE; eauto.
        { etransitivity; eauto. }
        { instantiate (2 := Some _).
          instantiate (1 := Some _).
          eauto.
        }
        { s. rewrite COND2. ss. }
        i. des. simtac.
        esplits; eauto.
        { econs 1. econs ;eauto.
          rewrite returnUpdateLocals_spec, COND. s.
          rewrite COND2. ss.
        }
        { right. apply CIH. econs; try exact SIM; eauto.
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
        hexploit inject_allocas_free_allocas; eauto; []; intro FREE_ALLOCAS; des.
        esplits. econs; ss; eauto.
        - destruct noret_tgt; ss.
      }
      i. inv STEP0. ss.
      inv CONF. ss. clarify.
      exploit invmem_free_allocas_invmem_rel; eauto; [].
      intro MEMFREE; des.

      exploit LOCAL; try exact MEMFREE; [M|..]; Mskip eauto.
      { ss. }
      { instantiate (1 := None). instantiate (1 := None). ss. }
      { destruct noret_tgt; ss. }
      i. des.
      des_ifs. cbn in *. clarify. (* local_tgt' = locals_tgt *)
      esplits; eauto.
      * econs 1. econs; eauto.
      * right. apply CIH.
        econs; try apply SIM; try eassumption.
        { ss. }
        { etransitivity; eauto. }
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
      i. inv STEP0; ss; cycle 1.
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
      hexploit SIM; try apply invmem_lift; eauto.
      { econs; eauto. }
      i; des.

      esplits; eauto.
      * econs 1. econs; eauto.
      * right. apply CIH. econs; try reflexivity.
        { ss. }
        {
          econs 2; eauto.
          s. i.
          hexploit RETURN; eauto. i. des. inv SIM0; ss.
          esplits; eauto.
        }
        {
          inv H.
          unfold getEntryBlock in *.
          des_ifs.
          ss. clarify.
          exact H0.
        }
    + (* excall *)
      exploit FUN; eauto. i. des.
      exploit ARGS; eauto. i. des.
      apply _sim_step; ss.
      { ii. apply H. clear H.
        inv CONF; ss; clarify.
        inv SIM_CONF. ss.
        destruct conf_tgt; ss.
        unfold lookupExFdecViaPtr in *. unfold mbind in *. des_ifs.
        inv SIM_PRODUCTS.
        expl SIM_NONE.
        expl SIM_SOME_FDEC.
        (* destruct fdef_tgt; ss. destruct fheader5; ss. *)
        (* exploit SIM; eauto. *)
        (* { econs; eauto. ss. } *)
        (* intro SIM_TGT; des. clear SIM_TGT0. *)
        (* inv SIM_TGT. ss. des_ifs. *)

        rename H18 into FDEC_SRC. move FDEC_SRC at bottom.
        assert(i0= fid).
        {
          expl lookupFdecViaIDFromProducts_ideq.
        } des; clarify.

        esplits; eauto.
        eapply sExCall; eauto.
        - unfold lookupExFdecViaPtr.
          unfold mbind.
          inv MEM. ss. unfold ftable_simulation in FUNTABLE. expl FUNTABLE.
          rewrite <- FUNTABLE0. rewrite Heq.
          rewrite SIM_NONE0.
          rewrite SIM_SOME_FDEC0. ss.
        - move H20 at bottom.
          move INJECT0 at bottom.
          move MEM at bottom.
          admit. (* AXIOM *)
        - move H21 at bottom.
          rewrite exCallUpdateLocals_spec in *.
          unfold return_locals in *.
          admit. (* AXIOM *)
      }
      i. inv STEP0; ss.
      { exfalso. clarify. clear - SIM_CONF MEM H18 H23 INJECT. rename funval1_tgt into fptr0. clear_tac.
        move H18 at bottom.
        rename H18 into SRC_EXCALL.
        rename H23 into TGT_CALL.
        unfold lookupFdefViaPtr in *. unfold lookupExFdecViaPtr in *. unfold mbind in *. des_ifs.
        inv MEM. clear SRC TGT INJECT0 WF. ss.
        expl FUNTABLE.
        rewrite Heq1 in *. rewrite Heq in *. clarify.
        clear - TGT_CALL Heq0 SIM_CONF.
        inv SIM_CONF. ss. inv SIM_PRODUCTS.
        expl SIM_NONE.
        clarify. }
      rewrite FUN_TGT in H22. inv H22.
      rewrite ARGS_TGT in H24. inv H24.

      rename Mem' into mem_src.
      rename Mem'0 into mem_tgt.


      rename H18 into FDEC_SRC. rename H23 into FDEC_TGT.
      assert(dck0 = dck).
      { inv SIM_CONF. inv SIM_PRODUCTS. ss.
        unfold lookupExFdecViaPtr in *. unfold mbind in *. des_ifs. ss.
        expl SIM_SOME_FDEC.
        assert(i0 = i1).
        {
          inv MEM. ss.
          expl FUNTABLE. rewrite FUNTABLE0 in *. clarify.
        } clarify.
      } clarify.

      assert(event = e).
      { (* AXIOM same event *) admit. } clarify.

      (* assert(extcall_other_sem TD rt (args2Typs la) (globals2Genv TD gl) gvs Mem0 E0 oresult mem_src). *)
      (* { destruct dck; ss; unfold add_empty_trace in *; ss; des_ifs. *)
      (*   - eapply callIntrinsics__extcall_properties; eauto. *)
      (*   - Fail eapply callMalloc__extcall_properties; eauto. *)
      (*     admit. *)
      (*   - admit. *)
      (*   - admit. *)
      (*   - admit. } *)

      rewrite exCallUpdateLocals_spec in *. ss.
      (* Can't say oresult0 = exists oresult0 *)
      assert(RETVALS_RELATED: exists mi_after oresult0,
                (option_f2 (genericvalues_inject.gv_inject mi_after) oresult oresult0) /\
                (inject_incr (InvMem.Rel.inject inv_curr) mi_after)
                (* (inject_incr f' (InvMem.Rel.inject inv_after) *)
            ).
      {
        destruct dck; ss; unfold add_empty_trace in *; ss; des_ifs.
        - hexploit callIntrinsics__extcall_properties; try exact Heq0; eauto; []; intro EXTCALL_SEM_SRC; des.

          hexploit extcall_other_ok; eauto; intro EXTCALL_OK; des.
          destruct EXTCALL_OK.
          clear ec_well_typed ec_arity ec_symbols_preserved ec_valid_block ec_bounds ec_mem_extends.
          clear ec_trace_length ec_receptive ec_determ.

          hexploit ec_mem_inject; eauto; swap 1 3; swap 1 2.
          { instantiate (1:= Mem1).
            instantiate (1:= inv_curr.(InvMem.Rel.inject)).
            move MEM at bottom.
            inv MEM. ss.
            inv INJECT1.
            inv WF.
            (* Vellvm's relational memory invariant is a bit different from compcert *)
            (* but the Axiom uses Compcert's memory relation *)

            (* WE HAVE *)
            Print InvMem.Rel.sem.
            Print memory_sim.MoreMem.mem_inj.
            Print genericvalues_inject.wf_sb_mi.
            (* NEEDED IN AXIOM *)
            Print Mem.mem_inj.
            Print Mem.inject'.

            (* TODO: Add our axiom? or add Mem.inject' in InvMem? *)
            (* for the latter one, are we sure we can maintain that invariant during step? *)
            econs; eauto.
            - admit.
            - admit.
            - admit.
          }
          { eapply gv_inject_list_spec; eauto. }
          { admit. (* preserves_globals *) }
          i; des.
          assert(oresult0 = vres').
          {
            hexploit callIntrinsics__extcall_properties; try exact Heq; eauto; []; intro EXTCALL_SEM_TGT; des.
            inv EXTCALL_SEM_TGT.
            inv H.
            move H7 at bottom.
            (* unfold option_f2t in *. *)
            (* eventgv_list_match_determ_2 *)
            admit.
          }
          esplits; eauto.
        - hexploit callMalloc__extcall_properties; try exact Heq0; eauto; []; intro EXTCALL_SEM_SRC; des.


          hexploit extcall_other_ok; eauto; intro EXTCALL_OK; des.
          destruct EXTCALL_OK.
          clear ec_well_typed ec_arity ec_symbols_preserved ec_valid_block ec_bounds ec_mem_extends.
          clear ec_trace_length ec_receptive ec_determ.


          hexploit ec_mem_inject; eauto; swap 1 3; swap 1 2.
          { instantiate (1:= Mem1).
            instantiate (1:= inv_curr.(InvMem.Rel.inject)).
            admit. }
          { eapply gv_inject_list_spec; eauto. }
          { admit. (* preserves_globals *) }
          i; des.
          esplits; eauto.
        - hexploit callFree__extcall_properties; try exact Heq0; eauto; []; intro EXTCALL_SEM_SRC; des.


          hexploit extcall_other_ok; eauto; intro EXTCALL_OK; des.
          destruct EXTCALL_OK.
          clear ec_well_typed ec_arity ec_symbols_preserved ec_valid_block ec_bounds ec_mem_extends.
          clear ec_trace_length ec_receptive ec_determ.


          hexploit ec_mem_inject; eauto; swap 1 3; swap 1 2.
          { instantiate (1:= Mem1).
            instantiate (1:= inv_curr.(InvMem.Rel.inject)).
            admit. }
          { eapply gv_inject_list_spec; eauto. }
          { admit. (* preserves_globals *) }
          i; des.
          esplits; eauto.
        - hexploit callIOFunction__extcall_io_sem; try exact H20; eauto; []; intro EXTCALL_SEM_SRC; des.
          inv EXTCALL_SEM_SRC.
          admit. (* eventval_match // genericvalue_injet.gv_inject *)
        - hexploit callExternalFunction__extcall_other_sem; try exact Heq0; eauto; []; intro EXTCALL_SEM_SRC; des.


          hexploit extcall_other_ok; eauto; intro EXTCALL_OK; des.
          destruct EXTCALL_OK.
          clear ec_well_typed ec_arity ec_symbols_preserved ec_valid_block ec_bounds ec_mem_extends.
          clear ec_trace_length ec_receptive ec_determ.


          hexploit ec_mem_inject; eauto; swap 1 3; swap 1 2.
          { instantiate (1:= Mem1).
            instantiate (1:= inv_curr.(InvMem.Rel.inject)).
            admit. }
          { eapply gv_inject_list_spec; eauto. }
          { admit. (* preserves_globals *) }
          i; des.
          esplits; eauto.
      }
      des.


      assert(INVMEM_EXTERNAL: exists inv_after,
                (InvMem.Rel.sem (mkCfg S TD Ps gl fs) (mkCfg S0 TD0 Ps0 gl0 fs0) mem_src mem_tgt inv_after)
                /\ (InvMem.Rel.le (InvMem.Rel.lift Mem0 Mem1 uniqs_src uniqs_tgt privs_src privs_tgt inv_curr)
                                  inv_after)
                /\ (inv_after.(InvMem.Rel.inject) = mi_after)
            ).
      { admit. (* AXIOM *) }
      des.
      rewrite <- INVMEM_EXTERNAL1 in *. clear INVMEM_EXTERNAL1.


      inv CONF. ss. clarify.

      hexploit RETURN; eauto.
      { (* THIS DOES NOT HOLD *)
        (* In normal call case, we only used RETURN when proving sim_local_stack, and sim_local_stack itself *)
        (* provided this. *)
        (* All we can get is RETVAL_RELATED, by the given Axiom, and this is the best we can do *)
        (* We need to add more Axiom *)
        instantiate (1:= oresult0).
        assert(oresult1 = oresult0) by admit; clarify.
        ginduction oresult; ii; ss; inv RETVALS_RELATED; ss.
      }
      i. des. inv SIM; ss.
      rewrite RETURN_TGT in *. clarify. clear_tac.


      esplits; eauto.
      * econs 1. econs; eauto.
        rewrite exCallUpdateLocals_spec. eauto.
      * right. apply CIH.
        econs; eauto.
        { ss. }
        { etransitivity; eauto. }
        (* eapply sim_local_stack_cons. eauto. *)
        (*   eapply sim_local_stack_cons with (mem_src:= mem_src) (mem_tgt:= mem_tgt) *)
        (*                                    (uniqs_src:= uniqs_src) (uniqs_tgt:= uniqs_tgt) *)
        (*                                    (privs_src:= privs_src) (privs_tgt:= privs_tgt); eauto. *)
        (*   { s. admit. (* extcall preserves uniq *) } *)
        (*   { s. admit. (* extcall preserves uniq *) } *)
        (*   { s. admit. (* extcall preserves uniq *) } *)
        (*   { s. admit. (* extcall preserves uniq *) } *)
        (*   i. ss. *)
        (*   hexploit RETURN; eauto. *)
        (*   { ss. etransitivity; eauto. admit. } *)
        (*   i; des. inv SIM; ss. *)
        (*   esplits; eauto. *)
        (* } *)
        (* econs; try apply SIM; ss; eauto. *)
        (* punfold H. econs; eauto. *)
        (* admit. (* sim *) *)
  - (* step *)
    econs 3; ss. i. exploit STEP; eauto. i. des.
    inv SIM; [|done].
    esplits; eauto. right.
    apply CIH.
    econs; [..|M]; Mskip eauto.
    { etransitivity; eauto. }
Admitted.
