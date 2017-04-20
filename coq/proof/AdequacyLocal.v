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
  (forall fid fdef_src fdef_tgt
          (FDEF_SRC: lookupFdefViaIDFromProducts prod_src fid = Some fdef_src)
          (FDEF_TGT: lookupFdefViaIDFromProducts prod_tgt fid = Some fdef_tgt),
      sim_fdef conf_src conf_tgt fdef_src fdef_tgt)
  /\
  (forall fptr fid_src fid_tgt
          (SRC: lookupFdefViaGVFromFunTable conf_src.(FunTable) fptr = Some fid_src)
          (TGT: lookupFdefViaGVFromFunTable conf_tgt.(FunTable) fptr = Some fid_tgt)
    ,
      fid_src = fid_tgt)
.

Inductive sim_conf (conf_src conf_tgt:Config): Prop :=
| sim_conf_intro
    (SIM_PRODUCTS: sim_products conf_src conf_tgt conf_src.(CurProducts) conf_tgt.(CurProducts))
.

(* TODO: Move to TODOProof *)
Lemma invmem_free_invmem_unary
      conf_src inv m x lo hi m' TD inv_unary
      (BOUNDS: Mem.bounds m x = (lo, hi))
      (FREE: free TD m (blk2GV TD x) = ret m')
      (PARENT: list_disjoint [x] inv_unary.(InvMem.Unary.private_parent))
      (pub_unary: mblock -> Prop)
      (UNARY: InvMem.Unary.sem conf_src (InvMem.Rel.gmax inv) pub_unary m inv_unary)
  :
    <<INVMEM: InvMem.Unary.sem conf_src (InvMem.Rel.gmax inv) pub_unary m' inv_unary>>
.
Proof.
  inv UNARY.
  assert(NEXTBLOCK_EQ: Mem.nextblock m' = Mem.nextblock m).
  {
    unfold free in *. des_ifs.
    expl Mem.nextblock_free.
  }
  econs; eauto.
  + eapply memory_props.MemProps.free_preserves_wf_Mem; eauto.
  + ii.
    expl PRIVATE_PARENT.
    inv PRIVATE_PARENT0.
    econs; eauto.
    rewrite NEXTBLOCK_EQ in *. ss.
  + ii.
    expl MEM_PARENT.
    rewrite MEM_PARENT0.
    rename b into __b__.
    clear - FREE IN PARENT.
    abstr (InvMem.Unary.private_parent inv_unary) private_parent.
    move mc at top.
    revert_until mc.
    induction mc; ii; ss.
    {
      expl IHmc.
      rewrite IHmc0. clear IHmc0 IHmc.
      assert(Mem.load a m __b__ o = Mem.load a m' __b__ o).
      {
        cbn in *. des_ifs.
        symmetry.
        eapply Mem.load_free; eauto.
        left. ii. clarify.
        exploit PARENT; eauto. left. ss.
      }
      des_ifs.
    }
  + ii.
    expl UNIQUE_PARENT_MEM.
    exploit memory_props.MemProps.free_preserves_mload_inv; eauto.
    Show Existentials. (* It can give some info whether there is Unshelved goals or not *)
    Unshelve. Undo 2.
    (* Just using hexploit/exploit && eauto gives Unshelved goals. *)
    (* It seems when lemma's goal is exactly same with current goal, exploit; eauto approach *)
    (* does not care on premises, just putting all the premises in the unshelved goal. *)
    (* In this case, by using eapply, this problem can be avoided. *)
    eapply memory_props.MemProps.free_preserves_mload_inv; eauto.
  + rewrite NEXTBLOCK in *.
    rewrite NEXTBLOCK_EQ in *. ss.
Qed.

Lemma invmem_free_invmem_rel
      conf_src conf_tgt inv
      m0 m1
      (MEM: InvMem.Rel.sem conf_src conf_tgt m0 m1 inv)
      x0 x1 lo hi
      (BOUNDS0: Mem.bounds m0 x0 = (lo, hi))
      (BOUNDS1: Mem.bounds m1 x1 = (lo, hi))
      m0' m1'
      TD
      (FREE0 : free TD m0 (blk2GV TD x0) = ret m0')
      (INJECT: inv.(InvMem.Rel.inject) x0 = ret (x1, 0))
      (FREE1 : free TD m1 (blk2GV TD x1) = ret m1')
      (PARENT_SRC: list_disjoint [x0] inv.(InvMem.Rel.src).(InvMem.Unary.private_parent))
      (PARENT_TGT: list_disjoint [x1] inv.(InvMem.Rel.tgt).(InvMem.Unary.private_parent))
  :
    <<MEM: InvMem.Rel.sem conf_src conf_tgt m0' m1' inv>>
.
Proof.
  inv MEM.
  econs; eauto.
  - clear INJECT INJECT0 WF TGT PARENT_TGT BOUNDS1 FREE1. clear_tac.
    abstr (InvMem.Rel.src inv) inv_unary.
    abstr (InvMem.Rel.public_src (InvMem.Rel.inject inv)) pub_unary.
    eapply invmem_free_invmem_unary; try eassumption.
  - clear INJECT INJECT0 WF SRC PARENT_SRC BOUNDS0 FREE0. clear_tac.
    abstr (InvMem.Rel.tgt inv) inv_unary.
    abstr (InvMem.Rel.public_tgt (InvMem.Rel.inject inv)) pub_unary.
    eapply invmem_free_invmem_unary; try eassumption.
  - cbn in *. des_ifs.
    expl genericvalues_inject.mem_inj__free.
    repeat rewrite Z.add_0_r in *. clarify.
  - cbn in *. des_ifs.
    expl genericvalues_inject.mem_inj__free.
    repeat rewrite Z.add_0_r in *. clarify.
Qed.

(* TODO: move to TODOProof or somewhere *)
Lemma list_disjoint_cons_inv
      X (hd: X) tl xs
      (DISJOINT: list_disjoint (hd :: tl) xs)
  :
    <<DISJOINT: list_disjoint [hd] xs /\ list_disjoint tl xs>>
.
Proof.
  splits.
  - ii. clarify. ss. des; ss. clarify. expl DISJOINT. left. ss.
  - eapply list_disjoint_cons_left; eauto.
Qed.

Lemma inject_allocas_free_allocas
      inv Allocas0 Allocas1
      (ALLOCAS: inject_allocas inv Allocas0 Allocas1)
      TD Mem0 Mem0'
      (FREE_ALLOCAS: free_allocas TD Mem0 Allocas0 = ret Mem0')
      Mem1 conf_src conf_tgt
      (MEM: InvMem.Rel.sem conf_src conf_tgt Mem0 Mem1 inv)
      (ALLOCAS_PARENT_SRC: list_disjoint Allocas0
                                         inv.(InvMem.Rel.src).(InvMem.Unary.private_parent))
      (ALLOCAS_PARENT_TGT: list_disjoint Allocas1
                                         inv.(InvMem.Rel.tgt).(InvMem.Unary.private_parent))
  :
    <<FREE_ALLOCAS: exists Mem1', free_allocas TD Mem1 Allocas1 = ret Mem1'>>
.
Proof.
  revert_until Allocas1.
  revert Allocas1.
  induction Allocas0; ii; ss; clarify; inv ALLOCAS.
  - esplits; eauto. unfold free_allocas. eauto.
  - des_ifs.
    unfold InvMem.Rel.inject in *. des_ifs.
    assert(FREE_SRC:= Heq).
    cbn in Heq. des_ifs.
    dup MEM. inv MEM. simpl in *. (* cbn causes FREE to shatter *)
    expl genericvalues_inject.mi_bounds.
    rewrite Heq0 in *.
    {
      des_ifsG; [|]; rename Heq1 into FREE_TGT; cycle 1.
      {
        exfalso.
        expl genericvalues_inject.mem_inj__free.
        repeat rewrite <- Zplus_0_r_reverse in *.
        unfold free in FREE_TGT. unfold GV2ptr in FREE_TGT. cbn in FREE_TGT. des_ifs.
      }
      exploit IHAllocas0; try exact FREE_ALLOCAS; eauto.
      {
        clear_tac.
        instantiate (1:= conf_tgt).
        instantiate (1:= conf_src).
        eapply invmem_free_invmem_rel; eauto.
        { expl list_disjoint_cons_inv (try exact ALLOCAS_PARENT_SRC; eauto). ss. }
        { expl list_disjoint_cons_inv (try exact ALLOCAS_PARENT_TGT; eauto). ss. }
      }
      { expl list_disjoint_cons_inv (try exact ALLOCAS_PARENT_SRC; eauto). ss. }
      { expl list_disjoint_cons_inv (try exact ALLOCAS_PARENT_TGT; eauto). ss. }
    }
Qed.

Lemma inject_allocas_cons_inv
      a0 a1 Allocas0 Allocas1 inv
      (ALLOCAS: inject_allocas inv (a0 :: Allocas0) (a1 :: Allocas1))
  :
    <<ALLOCAS: inject_allocas inv Allocas0 Allocas1 /\
               InvMem.Rel.inject inv a0 = ret (a1, 0)>>
.
Proof.
  inv ALLOCAS.
  splits; ss.
Qed.

Lemma inject_allocas_mem_le
      Allocas0 Allocas1 inv inv'
      (MEMLE: InvMem.Rel.le inv inv')
      (ALLOCAS: inject_allocas inv Allocas0 Allocas1)
  :
    <<ALLOCAS: inject_allocas inv' Allocas0 Allocas1>>
.
Proof.
  inv MEMLE.
  eapply list_forall2_imply; eauto.
Qed.

Lemma invmem_free_allocas_invmem_rel
  S Ps fs S0 TD0 Ps0 gl0 fs0 Allocas1 m_tgt0 Allocas0 m_src0 inv m_src1 m_tgt1
  (ALLOCAS_DISJOINT_SRC: list_disjoint Allocas0 (InvMem.Unary.private_parent (InvMem.Rel.src inv)))
  (ALLOCAS_DISJOINT_TGT: list_disjoint Allocas1 (InvMem.Unary.private_parent (InvMem.Rel.tgt inv)))
  (ALLOC_SRC: free_allocas TD0 m_src0 Allocas0 = ret m_src1)
  (ALLOC_TGT: free_allocas TD0 m_tgt0 Allocas1 = ret m_tgt1)
  (MEM: InvMem.Rel.sem
          (mkCfg S TD0 Ps gl0 fs)
          (mkCfg S0 TD0 Ps0 gl0 fs0)
          m_src0 m_tgt0 inv)
  (ALLOCAS: inject_allocas inv Allocas0 Allocas1)
  :
    <<INVMEM: InvMem.Rel.sem (mkCfg S TD0 Ps gl0 fs) (mkCfg S0 TD0 Ps0 gl0 fs0) m_src1 m_tgt1 inv>>
.
Proof.
  {
    ginduction Allocas0; ii; ss.
    - clarify. ss.
      inv ALLOCAS. ss. clarify.
    - destruct Allocas1; ss.
      { inv ALLOCAS. }
      apply inject_allocas_cons_inv in ALLOCAS. des.
      apply list_disjoint_cons_inv in ALLOCAS_DISJOINT_SRC.
      apply list_disjoint_cons_inv in ALLOCAS_DISJOINT_TGT. des.
      des_ifs. ss.
      exploit IHAllocas0; try exact H; eauto. clear IHAllocas0.
      rename Heq0 into FREE0.
      rename Heq into FREE1.
      dup FREE0. dup FREE1.
      unfold free in FREE0, FREE1. des_ifs.
      simpl in *. clarify. clear_tac.
      exploit genericvalues_inject.mem_inj__free.
      1: apply MEM.
      1-5: try eassumption.
      1: apply MEM.
      ss.
      i; des.

      exploit genericvalues_inject.mi_bounds.
      { apply MEM. }
      { eauto. }
      i. rewrite Heq2 in *. rewrite Heq0 in *. clarify.

      exploit invmem_free_invmem_rel.
      2: exact Heq2.
      2: exact Heq0.
      all: ss; try eassumption.
      (* { apply MEMLE. eauto. } *)
      i; des.
      ss.
  }
Qed.

Lemma mem_le_private_parent
      inv0 inv1
      (MEMLE: InvMem.Rel.le inv0 inv1)
  :
    <<PRIVATE_PARENT_EQ:
    InvMem.Unary.private_parent (InvMem.Rel.src inv0) = InvMem.Unary.private_parent (InvMem.Rel.src inv1)
    /\
    InvMem.Unary.private_parent (InvMem.Rel.tgt inv0) = InvMem.Unary.private_parent (InvMem.Rel.tgt inv1)>>
.
Proof.
  splits; apply MEMLE.
Qed.

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
      (expl mem_le_private_parent (try exact MEMLE));
        rewrite mem_le_private_parent0 in *; clear mem_le_private_parent0;
          rewrite mem_le_private_parent1 in *; clear mem_le_private_parent1.
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
        { right. apply CIH. econs; [..|M]; Mskip eauto.
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
        { right. apply CIH. econs; [..|M]; Mskip eauto.
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
      { admit. (* tgt not stuck *) }
      i. inv STEP0; ss; cycle 1.
      { admit. (* call & excall mismatch *) }
      rewrite FUN_TGT in H22. inv H22.
      rewrite ARGS_TGT in H25. inv H25.

      (* assert (SIM_FDEF: sim_fdef conf_src conf_tgt  *)
      assert (FID_SAME: fid0 = fid).
      {
        assert(fun1_tgt = fun2_src) by admit.
        clarify.
        assert(exists f_cnst, fun2_src = value_const f_cnst) by admit.
        des. clarify. cbn in *. des_ifs.
        inv CONF. ss. clarify.
        move H18 at bottom. move H23 at bottom.
        Require Import TODO.
        apply_all_once lookupFdefViaPtr_inversion. des.
        move SIM_CONF at bottom.
        assert(fn = fn0).
        { inv SIM_CONF. ss. inv SIM_PRODUCTS. ss.
          expl H2. }
        clarify.
        apply_all_once lookupFdefViaIDFromProducts_ideq. clarify.
      }
      subst.
      exploit lookupFdefViaPtr_inversion; try exact H18. i. des.
      exploit lookupFdefViaIDFromProducts_ideq; try exact x1. i. subst.
      exploit lookupFdefViaPtr_inversion; try exact H23. i. des.
      exploit lookupFdefViaIDFromProducts_ideq; try exact x3. i. subst.

      inv SIM_CONF. unfold sim_products in *. des. ss.
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
      { clear CIH RETURN ARGS FUN ERROR_SRC STEP STACK SIM_CONF.
        inv CONF. ss. subst.
        econs; eauto; eapply invmem_lift; eauto. }
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
