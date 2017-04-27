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

Definition sim_products
           (conf_src conf_tgt:Config)
           (prod_src prod_tgt:products): Prop :=
  <<SIM_SOME: forall fid fdef_src
          (FDEF_SRC: lookupFdefViaIDFromProducts prod_src fid = Some fdef_src),
          exists fdef_tgt,
          <<FDEF_TGT: lookupFdefViaIDFromProducts prod_tgt fid = Some fdef_tgt>> /\
                      <<SIM: sim_fdef conf_src conf_tgt fdef_src fdef_tgt>> >> /\
  <<SIM_NONE: forall fid
          (FDEF_SRC: lookupFdefViaIDFromProducts prod_src fid = None),
      <<FDEF_TGT: lookupFdefViaIDFromProducts prod_tgt fid = None>> >>
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

Lemma f_equal6 (A1 A2 A3 A4 A5 A6 B: Type) (f: A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> B)
      (x1 y1: A1) (EQ1: x1 = y1)
      (x2 y2: A2) (EQ2: x2 = y2)
      (x3 y3: A3) (EQ3: x3 = y3)
      (x4 y4: A4) (EQ4: x4 = y4)
      (x5 y5: A5) (EQ5: x5 = y5)
      (x6 y6: A6) (EQ6: x6 = y6)
  :
    <<EQ: f x1 x2 x3 x4 x5 x6 = f y1 y2 y3 y4 y5 y6>>
.
Proof. subst. reflexivity. Qed.

Lemma f_equal7 (A1 A2 A3 A4 A5 A6 A7 B: Type) (f: A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> B)
      (x1 y1: A1) (EQ1: x1 = y1)
      (x2 y2: A2) (EQ2: x2 = y2)
      (x3 y3: A3) (EQ3: x3 = y3)
      (x4 y4: A4) (EQ4: x4 = y4)
      (x5 y5: A5) (EQ5: x5 = y5)
      (x6 y6: A6) (EQ6: x6 = y6)
      (x7 y7: A7) (EQ7: x7 = y7)
  :
    <<EQ: f x1 x2 x3 x4 x5 x6 x7 = f y1 y2 y3 y4 y5 y6 y7>>
.
Proof. subst. reflexivity. Qed.

Lemma f_equal8 (A1 A2 A3 A4 A5 A6 A7 A8 B: Type) (f: A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> B)
      (x1 y1: A1) (EQ1: x1 = y1)
      (x2 y2: A2) (EQ2: x2 = y2)
      (x3 y3: A3) (EQ3: x3 = y3)
      (x4 y4: A4) (EQ4: x4 = y4)
      (x5 y5: A5) (EQ5: x5 = y5)
      (x6 y6: A6) (EQ6: x6 = y6)
      (x7 y7: A7) (EQ7: x7 = y7)
      (x8 y8: A8) (EQ8: x8 = y8)
  :
    <<EQ: f x1 x2 x3 x4 x5 x6 x7 x8 = f y1 y2 y3 y4 y5 y6 y7 y8>>
.
Proof. subst. reflexivity. Qed.

Ltac rpapply H :=
  first[erewrite f_equal8 | erewrite f_equal7 | erewrite f_equal6 | erewrite f_equal5 |
        erewrite f_equal4 | erewrite f_equal3 | erewrite f_equal2 | erewrite f_equal];
  [exact H|..]; try reflexivity.

(* TODO: move to Vellvm or TODOProof *)
Global Program Instance PreOrder_inject_incr: PreOrder inject_incr.
Next Obligation.
  ii.
  expl H.
Qed.

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
  inv SIM_CONF. ss. unfold sim_products in *. des. (* destruct and inv does not respect name *)
  (* TODO: define in inductive prop *)
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
      { admit. (* tgt not stuck *) }
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

        inv SIM_CONF. ss.
        unfold sim_products in *. des.
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

      inv SIM_CONF. unfold sim_products in *. des. ss.
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
      { admit. (* tgt not stuck *) }
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
        inv SIM_CONF. ss. unfold sim_products in *. des. (* destruct and inv does not respect name *)
        (* TODO: define in inductive prop *)
        expl SIM_NONE.
        clarify. }
      rewrite FUN_TGT in H22. inv H22.
      rewrite ARGS_TGT in H24. inv H24.

      rename Mem' into mem_src.
      rename Mem'0 into mem_tgt.


      assert(dck0 = dck).
      { admit. (* same kind *) } clarify.

      assert(event = e).
      { (* same event *) admit. } clarify.

      assert(INVMEM_EXTERNAL: exists inv_after,
                (InvMem.Rel.sem (mkCfg S TD Ps gl fs) (mkCfg S0 TD0 Ps0 gl0 fs0) mem_src mem_tgt inv_after)
                /\ (InvMem.Rel.le (InvMem.Rel.lift Mem0 Mem1 uniqs_src uniqs_tgt privs_src privs_tgt inv_curr)
                                  inv_after)).
      { admit. (* AXIOM *) }
      des.

      hexploit RETURN; try eassumption; eauto; swap 1 2.
      { rewrite exCallUpdateLocals_spec in *. eauto. }
      { s.
        instantiate (1:= oresult0).
        clear H26 H21.
        destruct dck; ss.
        - unfold add_empty_trace in *.
          des_ifs.
          expl callIntrinsics__extcall_properties (try exact Heq).
          rename callIntrinsics__extcall_properties into EXTCALL_SEM_TGT.
          expl callIntrinsics__extcall_properties (try exact Heq0).
          rename callIntrinsics__extcall_properties into EXTCALL_SEM_SRC.
          expl extcall_other_ok.
          destruct extcall_other_ok.
          clear ec_well_typed ec_arity ec_symbols_preserved ec_valid_block ec_bounds ec_mem_extends.
          clear ec_trace_length ec_receptive ec_determ.
          exploit ec_mem_inject; eauto; swap 1 3; swap 1 2.
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
          { clear - x0.
            (* don't instantiate oresult0 in top *)
            admit. }
        - admit.
      }
      i. des. inv SIM; ss. rename H into SIM.
      rewrite <- exCallUpdateLocals_spec in *.
      rewrite RETURN_TGT in *. clarify.

      inv CONF. ss. clarify.


      esplits; eauto.
      * econs 1. econs; eauto.
      * right. apply CIH.
        econs.
        { ss. }
        all: swap 1 2.
        { eauto. }
        { eauto. }
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
