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

Definition sim_products
          (conf_src conf_tgt:Config)
          (prod_src prod_tgt:products): Prop :=
  forall fid fdef_src fdef_tgt
    (FDEF_SRC: lookupFdefViaIDFromProducts prod_src fid = Some fdef_src)
    (FDEF_TGT: lookupFdefViaIDFromProducts prod_tgt fid = Some fdef_tgt),
    sim_fdef conf_src conf_tgt fdef_src fdef_tgt.

Inductive sim_conf (conf_src conf_tgt:Config): Prop :=
| sim_conf_intro
    (SIM_PRODUCTS: sim_products conf_src conf_tgt conf_src.(CurProducts) conf_tgt.(CurProducts))
.

Lemma sim_local_lift_sim conf_src conf_tgt
      (SIM_CONF: sim_conf conf_src conf_tgt):
  (sim_local_lift conf_src conf_tgt) <3= (sim conf_src conf_tgt).
Proof.
  s. pcofix CIH.
  intros idx st_src st_tgt SIM. inv SIM.
  pfold. punfold LOCAL. inv LOCAL.
  - (* error *)
    econs 1; eauto.
  - (* return *)
    eapply sop_star_sim; eauto.
    destruct st2_src, st_tgt. ss.
    destruct EC0, EC1. ss. subst.
    eapply _sim_src_error. i.
    inv STACK.
    + (* final *)
      exploit nerror_stuck_final; eauto.
      { ii. des. inv H. }
      i. des. ss. exploit RET; eauto. i. des.
      eapply _sim_exit; eauto.
    + (* return *)
      exploit nerror_nfinal_nstuck; eauto. i. des.
      inv x0. ss. rewrite returnUpdateLocals_spec in *. ss.
      simtac0. simtac0.
      exploit RET; eauto. i. des.
      apply _sim_step.
      { intro STUCK. apply STUCK. destruct conf_tgt. ss.
        destruct noret_tgt; simtac.
        - esplits. econs; ss; eauto.
          + admit. (* free_allocas *)
          + rewrite returnUpdateLocals_spec, RET_TGT. ss.
        - exploit genericvalues_inject.simulation__fit_gv; eauto.
          { admit. (* genericvalues_inject.wf_sb_mi *) }
          i. des.
          esplits. econs; ss; eauto.
          + admit. (* free_allocas *)
          + rewrite returnUpdateLocals_spec, RET_TGT. ss.
            inv CONF. ss. subst. rewrite x0. eauto.
      }
      i. inv STEP0. ss. rewrite returnUpdateLocals_spec in *. ss.
      destruct noret_tgt; simtac.
      * exploit LOCAL; eauto.
        { instantiate (2 := Some _).
          instantiate (1 := Some _).
          eauto.
        }
        { ss. }
        i. des. simtac.
        esplits; eauto.
        { econs 1. econs; eauto.
          rewrite returnUpdateLocals_spec, COND. ss.
        }
        { right. apply CIH. econs; [..|M]; Mskip eauto.
          - admit. (* free_allocas *)
          - etransitivity; eauto.
        }
      * exploit LOCAL; eauto.
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
        { right. apply CIH. econs; [..|M]; Mskip eauto.
          - admit. (* free_allocas *)
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
        esplits. econs; ss; eauto.
        - admit. (* free_allocas *)
        - destruct noret_tgt; ss.
      }
      i. inv STEP0. ss.
      exploit LOCAL; [M|..]; Mskip eauto.
      { ss. }
      { instantiate (1 := None). instantiate (1 := None). ss. }
      { destruct noret_tgt; ss. }
      i. des.
      esplits; eauto.
      * econs 1. econs; eauto.
      * right. apply CIH. econs; eauto.
        admit. (* free_allocas *)
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
      { admit. (* tgt not stuck *) }
      i. inv STEP0; ss; cycle 1.
      { admit. (* call & excall mismatch *) }
      rewrite FUN_TGT in H22. inv H22.
      rewrite ARGS_TGT in H25. inv H25.

      (* assert (SIM_FDEF: sim_fdef conf_src conf_tgt  *)
      assert (FID_SAME: fid0 = fid).
      { admit. (* fid same *) }
      subst.
      exploit lookupFdefViaPtr_inversion; try exact H18. i. des.
      exploit lookupFdefViaIDFromProducts_ideq; try exact x1. i. subst.
      exploit lookupFdefViaPtr_inversion; try exact H23. i. des.
      exploit lookupFdefViaIDFromProducts_ideq; try exact x3. i. subst.

      inv SIM_CONF.
      exploit SIM_PRODUCTS; try eapply invmem_lift; eauto.
      { econs; eauto. }
      i. des.

      esplits; eauto.
      * econs 1. econs; eauto.
      * right. apply CIH. econs; try reflexivity.
        { ss. }
        { econs 2; eauto.
          s. i.
          hexploit RETURN; eauto. i. des. inv SIM; ss.
          esplits; eauto.
        }
        { inv x.
          unfold getEntryBlock in *.
          des_ifs.
          ss. clarify.
          exact x4.
        }
    + (* excall *)
      exploit FUN; eauto. i. des.
      exploit ARGS; eauto. i. des.
      apply _sim_step; ss.
      { admit. (* tgt not stuck *) }
      i. inv STEP0; ss.
      { admit. (* call & excall mismatch *) }
      rewrite FUN_TGT in H22. inv H22.
      rewrite ARGS_TGT in H24. inv H24.
      hexploit RETURN; try reflexivity; eauto.
      { admit. (* InvMem.Rel.sem *) }
      { s. admit. (* retvals are related *) }
      { rewrite exCallUpdateLocals_spec in *. eauto. }
      i. des. inv SIM; ss.
      esplits; eauto.
      * econs 1. econs; eauto.
        admit. (* callExternalOrIntrinsics *)
      * admit. (* sim *)
  - (* step *)
    econs 3; ss. i. exploit STEP; eauto. i. des.
    inv SIM; [|done].
    esplits; eauto. right.
    apply CIH. econs; eauto. etransitivity; eauto.
Admitted.
