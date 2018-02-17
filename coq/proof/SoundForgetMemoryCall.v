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
Require Import Hints.
Require Import Exprs.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require AssnMem.
Require AssnState.
Require Import TODOProof.
Require Import Inject.
Require Import SoundBase.
Require Import memory_props.

Set Implicit Arguments.


Lemma forget_memory_call_unary_Subset inv
  : Assertion.Subset_unary (ForgetMemoryCall.unary inv) inv.
Proof.
  unfold ForgetMemoryCall.unary. ss.
  econs.
  - ii. ss.
    rewrite ExprPairSetFacts.filter_iff in *; try by solve_compat_bool.
    des. eauto.
  - split; ss.
  - ii. ss.
    rewrite AtomSetFacts.filter_iff in *; try by solve_compat_bool.
    des. eauto.
  - ii. ss.
Qed.

Lemma forget_memory_call_Subset inv
  : Assertion.Subset (ForgetMemoryCall.t inv) inv.
Proof.
  unfold ForgetMemoryCall.t.
  destruct inv.
  econs; ss; apply forget_memory_call_unary_Subset.
Qed.

Lemma forget_memory_call_unique_implies_private inv:
  unique_is_private_unary (ForgetMemoryCall.unary inv).
Proof.
  unfold unique_is_private_unary, ForgetMemoryCall.unary in *. ss. i.
  rewrite AtomSetFacts.filter_b in UNIQUE; try by solve_compat_bool.
  des_bool. des. eauto.
Qed.

Lemma private_preserved_after_call
        conf st0 invst0 assnmem0 gmax public0 inv0
        mem0 uniqs
        assnmem1 public1 mem1
        (STATE : AssnState.Unary.sem conf st0 invst0 assnmem0 gmax public0 inv0)
        (INCR : AssnMem.Unary.le (AssnMem.Unary.lift
                                   mem0 uniqs
                                   (memory_blocks_of_t conf st0 invst0 inv0.(Assertion.private))
                                   assnmem0) assnmem1)
        (MEM_AFTER_CALL : AssnMem.Unary.sem conf gmax public1 mem1 assnmem1)
  : <<PRIVATE_PRESERVED: forall mc b o,
      In b (memory_blocks_of_t conf st0 invst0 inv0.(Assertion.private)) ->
      mload_aux mem0 mc b o = mload_aux mem1 mc b o>>.
Proof.
  ii.
  inv MEM_AFTER_CALL.
  inv INCR.
  rewrite <- MEM_PARENT.
  - ss. rewrite MEM_PARENT_EQ. eauto.
  - rewrite <- PRIVATE_PARENT_EQ.
    apply in_app. left. eauto.
Qed.

Lemma sem_expr_private_preserved
      conf st0 invst0 inv0 mem1
      e1 e2 e
      (PRIVATE_PRESERVED: forall (mc : list AST.memory_chunk) (b : mblock) (o : Z),
          In b (memory_blocks_of_t conf st0 invst0 inv0.(Assertion.private)) ->
          mload_aux (Mem st0) mc b o = mload_aux mem1 mc b o)
      (IN_PRIVATE: ExprPairSet.In (e1, e2)
                                  (ExprPairSet.filter
                                     (ForgetMemoryCall.is_private_ExprPair inv0)
                                     (Assertion.lessdef inv0)))
      (EXP_EQ: e=e1 \/ e=e2)
  : AssnState.Unary.sem_expr conf st0 invst0 e =
    AssnState.Unary.sem_expr conf (mkState st0.(EC) st0.(ECS) mem1) invst0 e.
Proof.
  destruct e; ss.
  { erewrite <- sem_list_valueT_eq_locals with (st0 := mkState st0.(EC) st0.(ECS) mem1); ss. }
  erewrite <- sem_valueT_eq_locals with (st0 := mkState st0.(EC) st0.(ECS) mem1); ss.
  des_ifs.
  unfold mload. des_ifs.
  apply PRIVATE_PRESERVED.
  apply ExprPairSetFacts.filter_iff in IN_PRIVATE; try by solve_compat_bool. desH IN_PRIVATE.
  unfold ForgetMemoryCall.is_private_ExprPair in *.
  des_bool. ss. unfold ForgetMemoryCall.is_private_Expr in *.
  des.
  - subst. destruct v; ss.
    unfold memory_blocks_of_t.
    eapply in_flat_map.
    esplits; eauto; cycle 1.
    + rewrite Heq.
      eapply GV2ptr_In_GV2blocks; eauto.
    + apply InA_iff_In with (myeq := (fun x0 y : IdT.t => IdT.compare x0 y = Eq)).
      { split; i.
        - solve_leibniz; ss.
        - subst. finish_by_refl; ss. }
      apply IdTSetFacts.elements_iff.
      eapply IdTSetFacts.mem_iff.
      eauto.
  - subst. destruct v; ss.
    unfold memory_blocks_of_t.
    eapply in_flat_map.
    esplits; eauto; cycle 1.
    + rewrite Heq.
      eapply GV2ptr_In_GV2blocks; eauto.
    + apply InA_iff_In with (myeq := (fun x0 y : IdT.t => IdT.compare x0 y = Eq)).
      { split; i.
        - solve_leibniz; ss.
        - subst. finish_by_refl; ss. }
      apply IdTSetFacts.elements_iff.
      eapply IdTSetFacts.mem_iff.
      eauto.
Qed.

Lemma mem_lift_le_nextblock
      conf uniqs privs
      gmax0 public0 mem0 assnmem0
      gmax1 public1 mem1 assnmem1
      (MEM_BEFORE_CALL : AssnMem.Unary.sem conf gmax0 public0 mem0 assnmem0)
      (MEM_AFTER_CALL : AssnMem.Unary.sem conf gmax1 public1 mem1 assnmem1)
      (MEM_LIFT_LE : AssnMem.Unary.le (AssnMem.Unary.lift mem0 uniqs privs assnmem0) assnmem1)
  : (mem0.(Memory.Mem.nextblock) <= mem1.(Memory.Mem.nextblock))%positive.
Proof.
  inv MEM_LIFT_LE.
  inv MEM_BEFORE_CALL. inv MEM_AFTER_CALL.
  rewrite NEXTBLOCK. rewrite NEXTBLOCK0. eauto.
Qed.

Lemma mem_le_wf_lc
      conf st gmax uniqs privs
      public0 mem0 assnmem0
      public1 mem1 assnmem1
      (MEM_LE : AssnMem.Unary.le (AssnMem.Unary.lift mem0 uniqs privs assnmem0) assnmem1)
      (WF_LOCAL : memory_props.MemProps.wf_lc mem0 st)
      (MEM_BEFORE_CALL : AssnMem.Unary.sem conf gmax public0 mem0 assnmem0)
      (MEM_AFTER_CALL : AssnMem.Unary.sem conf gmax public1 mem1 assnmem1)
  : memory_props.MemProps.wf_lc mem1 st.
Proof.
  unfold memory_props.MemProps.wf_lc in *. i.
  exploit WF_LOCAL; eauto. i.
  eapply memory_props.MemProps.valid_ptrs__trans; eauto.
  inv MEM_LE. ss.
  inv MEM_BEFORE_CALL. inv MEM_AFTER_CALL.
  congruence.
Qed.

(* TODO: doing here *)
Lemma forget_memory_call_unary_sound
      conf st0 mem1
      gmax public0 public1
      assnmem0 assnmem1
      invst0 inv0
      (MEM_LE : AssnMem.Unary.le (AssnMem.Unary.lift st0.(Mem)
                                                         (memory_blocks_of conf st0.(EC).(Locals) inv0.(Assertion.unique))
                                                         (memory_blocks_of_t conf st0 invst0 inv0.(Assertion.private))
                                                   assnmem0) assnmem1)
      (MEM_BEFORE_CALL: AssnMem.Unary.sem conf gmax public0 st0.(Mem) assnmem0)
      (MEM_AFTER_CALL: AssnMem.Unary.sem conf gmax public1 mem1 assnmem1)
      (INCR: forall b, public0 b -> public1 b)
      (STATE : AssnState.Unary.sem conf st0 invst0 assnmem0 gmax public0 inv0)
  : <<STATE_UNARY: AssnState.Unary.sem conf (mkState st0.(EC) st0.(ECS) mem1) invst0
                                      (AssnMem.Unary.unlift assnmem0 assnmem1)
                                      gmax public1
                                      (ForgetMemoryCall.unary inv0)>> /\
    <<MEM_UNARY: AssnMem.Unary.sem conf gmax public1 mem1 (AssnMem.Unary.unlift assnmem0 assnmem1)>>.
Proof.
  hexploit private_preserved_after_call; eauto. intro PRIVATE_PRESERVED. des.
  split.
  { (* STATE *)
    assert (STATE_CPY:=STATE).
    inv STATE.
    econs.
    - (* lessdef *)
      ii. destruct x as [e1 e2]. ss.
      erewrite <- sem_expr_private_preserved in VAL1; eauto.
      assert (X:= H).
      apply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool. des.
      
      exploit LESSDEF; eauto. i.
      erewrite <- sem_expr_private_preserved; eauto.
    - inv NOALIAS. rename NOALIAS0 into NOALIAS.
      econs.
      + (* DIFFBLOCK *)
        i.
        erewrite sem_valueT_eq_locals in VAL1.
        { erewrite sem_valueT_eq_locals in VAL2.
          { ss. eapply DIFFBLOCK; eauto. }
          ss.
        }
        ss.
      + (* NOALIAS *)
        i.
        erewrite sem_valueT_eq_locals in VAL1.
        { erewrite sem_valueT_eq_locals in VAL2.
          { ss. eapply NOALIAS; eauto. }
          ss.
        }
        ss.
    - ss.
      intros x IN_X.
      apply AtomSetFacts.filter_iff in IN_X; try by solve_compat_bool.
      destruct IN_X as [IN_X MEM_PRIVATE].

      exploit UNIQUE; eauto. intro UNIQUE_BEFORE.
      inv UNIQUE_BEFORE.
      econs; eauto.
      ss.
      inv MEM_AFTER_CALL. i.
      hexploit UNIQUE_PARENT_MEM; eauto. intro GV_DIFFBLOCK.

      clear LOCALS MEM GLOBALS GLOBALS0 PRIVATE_PARENT MEM_PARENT UNIQUE_PARENT_MEM.
      clear WF_LOCAL WF_PREVIOUS WF_GHOST UNIQUE_PARENT_LOCAL.
      clear LESSDEF NOALIAS UNIQUE PRIVATE.
      clear PRIVATE_PRESERVED MEM_BEFORE_CALL.
      (* MEM_PRIVATE  *)
      clear UNIQUE_PARENT_GLOBALS UNIQUE_PRIVATE_PARENT.
      clear NEXTBLOCK STATE_CPY INCR LOAD.
      inv MEM_LE.
      clear MEM_PARENT_EQ PRIVATE_PARENT_EQ MEM_PARENT NEXTBLOCK_LE.
      clear WF.
      (* clear VAL. *)

      {
        clear_tac.
        unfold AssnState.Unary.sem_diffblock. ii. clarify.
        unfold AssnMem.gv_diffblock_with_blocks in *.
        eapply GV_DIFFBLOCK; eauto. clear GV_DIFFBLOCK.
        rewrite <- UNIQUE_PARENT_EQ. ss.
        apply in_app. left.
        apply filter_In.
        splits.
        - unfold memory_blocks_of_t.
          apply in_flat_map.
          esplits; eauto.
          + eapply IdTSetFacts.mem_iff in MEM_PRIVATE.
            eapply InA_iff_In with (myeq := (fun x0 y : IdT.t => IdT.compare x0 y = Eq)).
            { split; i.
              - solve_leibniz. ss.
              - subst. finish_by_refl. }
            eapply IdTSetFacts.elements_iff; eauto.
          + unfold AssnState.Unary.sem_idT. ss.
            rewrite VAL. ss.
        - unfold memory_blocks_of.
          eapply existsb_exists.
          exists y; splits; cycle 1.
          { compute. des_ifs. }
          apply in_flat_map.
          esplits; eauto.
          + apply InA_In.
            apply AtomSetFacts.elements_iff. apply IN_X.
          + des_ifs.
      }
    - ss.
      ii. exploit PRIVATE; eauto. i. des.
      esplits; eauto.
      ss.
      assert (B_IN: In b (memory_blocks_of_t conf st0 invst0 (Assertion.private inv0))).
      { unfold memory_blocks_of_t.
        eapply in_flat_map.
        esplits; eauto.
        - eapply InA_iff_In with (myeq := (fun x0 y : IdT.t => IdT.compare x0 y = Eq)).
          { split; i.
            - solve_leibniz. ss.
            - subst. finish_by_refl. }
          apply IdTSetFacts.elements_iff.
          apply H.
        - erewrite sem_idT_eq_locals. rewrite VAL.
          ss. ss.
      }
      inv MEM_AFTER_CALL.
      apply PRIVATE_PARENT.
      inv MEM_LE.
      rewrite <- PRIVATE_PARENT_EQ. ss.
      apply in_app. left. eauto.
    - ss.
    - eapply Forall_harder.
      { rpapply ALLOCAS_VALID. }
      ss. i.
      eapply Pos.lt_le_trans; eauto.
      inv MEM_LE. ss.
      rewrite MEM_PARENT_EQ in *.
      apply MEM_AFTER_CALL.
    - ss.
      ii. exploit WF_LOCAL; eauto. i.
      eapply memory_props.MemProps.valid_ptrs__trans; eauto.
      eapply mem_lift_le_nextblock; eauto.
    - ss. eapply mem_le_wf_lc; eauto.
    - ss. eapply mem_le_wf_lc; eauto.
    - ss.
    - ss.
    - ss.
  }
  { (* MEM *)
    hexploit mem_lift_le_nextblock; try exact MEM_LE; eauto. intro NEXT_BLOCK.

    inv MEM_BEFORE_CALL.
    rename GLOBALS into GLOBALS_B.
    rename WF into WF_B.
    rename PRIVATE_PARENT into PRIVATE_PARENT_B.
    rename MEM_PARENT into MEM_PARENT_B.
    rename UNIQUE_PARENT_MEM into UNIQUE_PARENT_MEM_B.
    rename UNIQUE_PARENT_GLOBALS into UNIQUE_PARENT_GLOBALS_B.
    rename UNIQUE_PRIVATE_PARENT into UNIQUE_PRIVATE_PARENT_B.
    inv MEM_AFTER_CALL.
    econs; eauto.
    - ss. i.
      apply PRIVATE_PARENT.
      inv MEM_LE.
      rewrite <- PRIVATE_PARENT_EQ.
      ss. apply in_app. right. eauto.
    - i. rewrite MEM_PARENT_B; eauto.
      rewrite <- MEM_PARENT.
      + inv MEM_LE. ss.
        rewrite <- MEM_PARENT_EQ. eauto.
      + inv MEM_LE. ss.
        rewrite <- PRIVATE_PARENT_EQ.
        apply in_app. right. eauto.
    - ii. exploit UNIQUE_PARENT_MEM; eauto.
      inv MEM_LE. ss.
      rewrite <- UNIQUE_PARENT_EQ.
      {
        des.
        esplits; eauto.
        apply in_app. right. ss.
      }
    - ss.
      clear - MEM_LE NEXTBLOCK0 NEXTBLOCK NEXTBLOCK_PARENT.
      {
        inv MEM_LE. ss. clear MEM_PARENT_EQ PRIVATE_PARENT_EQ UNIQUE_PARENT_EQ MEM_PARENT.
        rewrite NEXTBLOCK0.
        etransitivity; eauto.
        etransitivity; try apply NEXTBLOCK_LE; eauto.
        rewrite NEXTBLOCK. reflexivity.
      }
  }
Qed.

Lemma incr_public_src
      assnmem0 assnmem1 b
      (INJECT : Values.inject_incr (AssnMem.Rel.inject assnmem0) (AssnMem.Rel.inject assnmem1))
      (PUBLIC : AssnMem.Rel.public_src (AssnMem.Rel.inject assnmem0) b)
  : AssnMem.Rel.public_src (AssnMem.Rel.inject assnmem1) b.
Proof.
  unfold AssnMem.Rel.public_src in *.
  destruct (AssnMem.Rel.inject assnmem0 b) eqn:INJ_B; ss.
  destruct p.
  exploit INJECT; eauto. ii. congruence.
Qed.

Lemma incr_public_tgt
      assnmem0 assnmem1 b
      (INJECT : Values.inject_incr (AssnMem.Rel.inject assnmem0) (AssnMem.Rel.inject assnmem1))
      (PUBLIC : AssnMem.Rel.public_tgt (AssnMem.Rel.inject assnmem0) b)
  : AssnMem.Rel.public_tgt (AssnMem.Rel.inject assnmem1) b.
Proof.
  unfold AssnMem.Rel.public_tgt in *. des.
  exploit INJECT; eauto.
Qed.

(* TODO: location *)
Lemma filter_subset
      f xs
  :
    <<SUBSET: AtomSetImpl.filter f xs [<=] xs>>
.
Proof.
  ii.
  apply AtomSetFacts.filter_iff in H; [| solve_compat_bool]. des; ss.
Qed.

Lemma forget_memory_call_sound
      conf_src st0_src id_src fun_src args_src cmds_src
      conf_tgt st0_tgt id_tgt fun_tgt args_tgt cmds_tgt
      noret clattrs typ varg
      assnmem0 invst0 inv0
      assnmem1 mem1_src mem1_tgt
      (CMDS_SRC: st0_src.(EC).(CurCmds) = (insn_call id_src noret clattrs typ varg fun_src args_src) :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = (insn_call id_tgt noret clattrs typ varg fun_tgt args_tgt) :: cmds_tgt)
      (STATE: AssnState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 assnmem0 inv0)
      (MEM_BEFORE_CALL: AssnMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) assnmem0)
      (FUN:
         forall funval2_src
                (FUN_SRC: getOperandValue conf_src.(CurTargetData) fun_src st0_src.(EC).(Locals) conf_src.(Globals) = Some funval2_src),
         exists funval1_tgt,
          <<FUN_TGT: getOperandValue conf_tgt.(CurTargetData) fun_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some funval1_tgt>> /\
          <<INJECT: genericvalues_inject.gv_inject assnmem0.(AssnMem.Rel.inject) funval2_src funval1_tgt>>)
      (ARGS:
         forall args2_src
                (ARGS_SRC: params2GVs conf_src.(CurTargetData) args_src st0_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
         exists args1_tgt,
           (<<ARGS_TGT: params2GVs (conf_tgt.(CurTargetData))
                                  args_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>>) /\
           (<<INJECT: list_forall2 (genericvalues_inject.gv_inject
                                     assnmem0.(AssnMem.Rel.inject)) args2_src args1_tgt>>) /\
           (<<VALID_SRC: List.Forall (MemProps.valid_ptrs (Memory.Mem.nextblock st0_src.(Mem))) args2_src>>) /\
           (<<VALID_TGT: List.Forall (MemProps.valid_ptrs (Memory.Mem.nextblock st0_tgt.(Mem))) args1_tgt>>))
      (INCR: AssnMem.Rel.le (AssnMem.Rel.lift st0_src.(Mem) st0_tgt.(Mem)
                                            (memory_blocks_of conf_src st0_src.(EC).(Locals) inv0.(Assertion.src).(Assertion.unique))
                                            (memory_blocks_of conf_tgt st0_tgt.(EC).(Locals) inv0.(Assertion.tgt).(Assertion.unique))
                                            (memory_blocks_of_t conf_src st0_src invst0.(AssnState.Rel.src) inv0.(Assertion.src).(Assertion.private))
                                            (memory_blocks_of_t conf_tgt st0_tgt invst0.(AssnState.Rel.tgt) inv0.(Assertion.tgt).(Assertion.private))
                                            assnmem0) assnmem1)
      (MEM_AFTER_CALL: AssnMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt assnmem1)
  : (* exists invst2  *) exists assnmem2,
      <<INCR: AssnMem.Rel.le assnmem0 assnmem2>> /\
      <<STATE:
        AssnState.Rel.sem
          conf_src conf_tgt
          (mkState st0_src.(EC) st0_src.(ECS) mem1_src)
          (mkState st0_tgt.(EC) st0_tgt.(ECS) mem1_tgt)
          invst0 assnmem2 (ForgetMemoryCall.t inv0)>> /\
      <<MEM: AssnMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt assnmem2>> /\
      <<MEM_INJ: assnmem2.(AssnMem.Rel.inject) = assnmem1.(AssnMem.Rel.inject)>>.
Proof.
  assert(INJECT_ALLOCAS_NEW:
           AssnState.Rel.inject_allocas (AssnMem.Rel.inject assnmem1)
                                       st0_src.(EC).(Allocas)
                                       st0_tgt.(EC).(Allocas)).
  { eapply AssnState.Rel.inject_allocas_preserved_le_lift; try exact INCR; eauto; try apply STATE.
    - inv MEM_BEFORE_CALL. inv SRC. etransitivity; eauto.
      inv INCR. ss. inv SRC. ss. rewrite MEM_PARENT_EQ. reflexivity.
    - inv MEM_BEFORE_CALL. inv TGT. etransitivity; eauto.
      inv INCR. ss. inv TGT. ss. rewrite MEM_PARENT_EQ. reflexivity.
  }
  hexploit SoundBase.lift_unlift_le; eauto.
  { apply MEM_BEFORE_CALL. }
  { apply MEM_BEFORE_CALL. }
  intro NEW_LE; des.
  exists (AssnMem.Rel.unlift assnmem0 assnmem1).
  unfold AssnMem.Rel.unlift in *.
  assert (INCR_CPY:=INCR).
  inv INCR. ss.
  rename SRC into LE_SRC. rename TGT into LE_TGT.
  inv STATE. inv MEM_BEFORE_CALL. inv MEM_AFTER_CALL.
  rewrite GMAX in *.

  exploit forget_memory_call_unary_sound; try exact LE_SRC; eauto.
  { i. eapply incr_public_src; eauto. }
  i. des.
  exploit forget_memory_call_unary_sound; try exact LE_TGT; eauto.
  { i. eapply incr_public_tgt; eauto. }
  i. des.

  esplits; eauto.
  - econs; ss.
    + eapply AtomSetFacts.Empty_s_m_Proper; eauto. red.
      eapply filter_subset; eauto.
    +
      ii. exploit MAYDIFF; eauto. i.
      erewrite sem_idT_eq_locals.
      { des. esplits; eauto.
        eapply genericvalues_inject.gv_inject_incr; eauto. }
      ss.
  - econs; ss.
Qed.
