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
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.

Set Implicit Arguments.


Lemma forget_memory_call_unary_Subset inv
  : Invariant.Subset_unary (ForgetMemoryCall.unary inv) inv.
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
  : Invariant.Subset (ForgetMemoryCall.t inv) inv.
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
      mem0 mem1 invmem0 invmem1
      conf gmax public uniqs
      (INCR : InvMem.Unary.le (InvMem.Unary.lift mem0 uniqs invmem0) invmem1)
      (MEM : InvMem.Unary.sem conf gmax public mem1 invmem1)
  : <<PRIVATE_PRESERVED: forall mc b o, In b invmem0.(InvMem.Unary.private) ->
                                   mload_aux mem0 mc b o = mload_aux mem1 mc b o>>.
Proof.
  ii. inv INCR. ss.
  inv MEM.
  rewrite <- MEM_PARENT0; cycle 1.
  { rewrite <- PRIVATE_PARENT_EQ.
    apply in_app. eauto. }
  apply MEM_PARENT. apply in_app. eauto.
Qed.

Lemma sem_expr_private_preserved
      conf st0 invst0 invmem0 inv0 invmem1 mem1 uniqs
      e e1 e2
      (* gmax public *)
      (STATE : InvState.Unary.sem conf st0 invst0 invmem0 inv0)
      (* (MEM : InvMem.Unary.sem conf gmax public mem1 invmem1) *)
      (IN_PRIVATE: ExprPairSet.In (e1, e2)
                                  (ExprPairSet.filter
                                     (ForgetMemoryCall.is_private_ExprPair inv0)
                                     (Invariant.lessdef inv0)))
      (PRIVATE_PRESERVED: forall (mc : list AST.memory_chunk) (b : mblock) (o : Z),
          In b (InvMem.Unary.private invmem0) -> mload_aux (Mem st0) mc b o = mload_aux mem1 mc b o)
      (EXP_EQ: e=e1 \/ e=e2)
      (MEM_LE: InvMem.Unary.le (InvMem.Unary.lift st0.(Mem) uniqs invmem0) invmem1)
  : InvState.Unary.sem_expr conf st0 invst0 e =
    InvState.Unary.sem_expr conf (mkState st0.(EC) st0.(ECS) mem1) invst0 e.
Proof.
  destruct e; ss.
  { (* gep *)
    erewrite <- sem_list_valueT_eq_locals with (st0 := mkState st0.(EC) st0.(ECS) mem1); ss.
  }
  erewrite <- sem_valueT_eq_locals with (st0 := mkState st0.(EC) st0.(ECS) mem1); ss.
  des_ifs.
  unfold mload. des_ifs.
  apply PRIVATE_PRESERVED.
  apply ExprPairSetFacts.filter_iff in IN_PRIVATE; try by solve_compat_bool. desH IN_PRIVATE.
  unfold ForgetMemoryCall.is_private_ExprPair in *.
  des_bool. ss. unfold ForgetMemoryCall.is_private_Expr in *.
  des.
  - subst. destruct v; ss.
    unfold ForgetMemoryCall.is_private_Expr.
    inv STATE.
    exploit PRIVATE; eauto.
    { apply IdTSetFacts.mem_iff. eauto. }
    i. des_ifs.
  - subst. destruct v; ss.
    unfold ForgetMemoryCall.is_private_Expr.
    inv STATE.
    exploit PRIVATE; eauto.
    { apply IdTSetFacts.mem_iff. eauto. }
    i. des_ifs.
Qed.

(* TODO: position *)
Lemma filter_map_spec
      X Y
      a b (f:X -> option Y) l
      (IN: In a l)
      (APP: f a = Some b)
  : In b (filter_map f l).
Proof.
  induction l; ss.
  des.
  - subst. rewrite APP.
    econs. eauto.
  - des_ifs; eauto.
    constructor 2. eauto.
Qed.

Lemma mem_lift_le_nextblock
      conf ublks
      gmax0 public0 mem0 invmem0
      gmax1 public1 mem1 invmem1
      (MEM_BEFORE_CALL : InvMem.Unary.sem conf gmax0 public0 mem0 invmem0)
      (MEM_AFTER_CALL : InvMem.Unary.sem conf gmax1 public1 mem1 invmem1)
      (MEM_LIFT_LE : InvMem.Unary.le (InvMem.Unary.lift mem0 ublks invmem0) invmem1)
  : (mem0.(Memory.Mem.nextblock) <= mem1.(Memory.Mem.nextblock))%positive.
Proof.
  inv MEM_LIFT_LE.
  inv MEM_BEFORE_CALL. inv MEM_AFTER_CALL.
  rewrite NEXTBLOCK. rewrite NEXTBLOCK0. eauto.
Qed.

Lemma forget_memory_call_unary_sound
      conf st0 mem1
      gmax public0 public1
      invmem0 invmem1
      invst0 inv0
      (MEM_LE : InvMem.Unary.le (InvMem.Unary.lift st0.(Mem)
                                                   (memory_blocks_of conf st0.(EC).(Locals) inv0.(Invariant.unique))
                                                   invmem0) invmem1)
      (MEM_BEFORE_CALL: InvMem.Unary.sem conf gmax public0 st0.(Mem) invmem0)
      (MEM_AFTER_CALL: InvMem.Unary.sem conf gmax public1 mem1 invmem1)
      (INCR: forall b, public0 b -> public1 b)
      (STATE : InvState.Unary.sem conf st0 invst0 invmem0 inv0)
  : <<STATE_UNARY: InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) mem1) invst0
                                      (InvMem.Unary.mk invmem0.(InvMem.Unary.private)
                                                   invmem0.(InvMem.Unary.private_parent)
                                                   invmem0.(InvMem.Unary.mem_parent)
                                                   invmem0.(InvMem.Unary.unique_parent)
                                                   invmem1.(InvMem.Unary.nextblock))
                                      (ForgetMemoryCall.unary inv0)>> /\
    <<MEM_UNARY: InvMem.Unary.sem conf gmax public1 mem1
                                  (InvMem.Unary.mk invmem0.(InvMem.Unary.private)
                                                   invmem0.(InvMem.Unary.private_parent)
                                                   invmem0.(InvMem.Unary.mem_parent)
                                                   invmem0.(InvMem.Unary.unique_parent)
                                                   invmem1.(InvMem.Unary.nextblock))>>.
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
          { ss. exploit DIFFBLOCK; eauto. }
          ss.
        }
        ss.
      + (* NOALIAS *)
        i.
        erewrite sem_valueT_eq_locals in VAL1.
        { erewrite sem_valueT_eq_locals in VAL2.
          { ss. exploit NOALIAS; eauto. }
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

      unfold InvState.Unary.sem_diffblock. des_ifs. ii. subst.
      unfold InvMem.gv_diffblock_with_blocks in *.
      exploit GV_DIFFBLOCK; eauto.

      exploit PRIVATE.
      { apply IdTSetFacts.mem_iff; eauto. }
      { eauto. }
      i. des_ifs.
      inv MEM_LE.
      rewrite <- UNIQUE_PARENT_EQ. ss.
      apply in_app. left.
      rewrite filter_In.
      split; eauto.
      apply existsb_exists.
      exists b0. split.
      + unfold memory_blocks_of.
        eapply filter_map_spec.
        * apply InA_iff_In.
          apply AtomSetFacts.elements_iff.
          eauto.
        * des_ifs.
      + destruct (Values.eq_block b0 b0); eauto.
    - ss.
    - ss.
      ii. exploit WF_LOCAL; eauto. i.
      eapply memory_props.MemProps.valid_ptrs__trans; eauto.
      eapply mem_lift_le_nextblock; eauto.
    - ss.
  }
  { (* MEM *)
    hexploit mem_lift_le_nextblock; try exact MEM_LE; eauto. intro NEXT_BLOCK.

    inv MEM_BEFORE_CALL.
    rename GLOBALS into GLOBALS_B.
    rename WF into WF_B.
    rename PRIVATE into PRIVATE_B.
    rename PRIVATE_PARENT into PRIVATE_PARENT_B.
    rename PRIVATE_DISJOINT into PRIVATE_DISJOINT_B.
    rename MEM_PARENT into MEM_PARENT_B.
    rename UNIQUE_PARENT_MEM into UNIQUE_PARENT_MEM_B.
    rename UNIQUE_PARENT_GLOBALS into UNIQUE_PARENT_GLOBALS_B.
    rename UNIQUE_PRIVATE_PARENT into UNIQUE_PRIVATE_PARENT_B.
    inv MEM_AFTER_CALL.
    econs; eauto.
    - ss.
      admit.
      (* b is private in invmem0 then it is private_parent for callee *)
      (* then it's not in public1. *)
      (* so we can prove *)
    - ss.
      admit.
      (* b is private_parent in invmem0 then it is also private_parent for callee *)
      (* then it's not in public1. *)
      (* so we can prove *)
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
      apply in_app. right. eauto.
  }
Admitted.

Lemma incr_public_src
      invmem0 invmem1 b
      (INJECT : Values.inject_incr (InvMem.Rel.inject invmem0) (InvMem.Rel.inject invmem1))
      (PUBLIC : InvMem.Rel.public_src (InvMem.Rel.inject invmem0) b)
  : InvMem.Rel.public_src (InvMem.Rel.inject invmem1) b.
Proof.
  unfold InvMem.Rel.public_src in *.
  destruct (InvMem.Rel.inject invmem0 b) eqn:INJ_B; ss.
  destruct p.
  exploit INJECT; eauto. ii. congruence.
Qed.

Lemma incr_public_tgt
      invmem0 invmem1 b
      (INJECT : Values.inject_incr (InvMem.Rel.inject invmem0) (InvMem.Rel.inject invmem1))
      (PUBLIC : InvMem.Rel.public_tgt (InvMem.Rel.inject invmem0) b)
  : InvMem.Rel.public_tgt (InvMem.Rel.inject invmem1) b.
Proof.
  unfold InvMem.Rel.public_tgt in *. des.
  exploit INJECT; eauto.
Qed.

Lemma forget_memory_call_sound
      conf_src st0_src id_src fun_src args_src cmds_src
      conf_tgt st0_tgt id_tgt fun_tgt args_tgt cmds_tgt
      noret clattrs typ varg
      invmem0 invst0 inv0
      invmem1 mem1_src mem1_tgt
      (CMDS_SRC: st0_src.(EC).(CurCmds) = (insn_call id_src noret clattrs typ varg fun_src args_src) :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = (insn_call id_tgt noret clattrs typ varg fun_tgt args_tgt) :: cmds_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM_BEFORE_CALL: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (FUN:
         forall funval2_src
                (FUN_SRC: getOperandValue conf_src.(CurTargetData) fun_src st0_src.(EC).(Locals) conf_src.(Globals) = Some funval2_src),
         exists funval1_tgt,
          <<FUN_TGT: getOperandValue conf_tgt.(CurTargetData) fun_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some funval1_tgt>> /\
          <<INJECT: genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject) funval2_src funval1_tgt>>)
      (ARGS:
         forall args2_src
                (ARGS_SRC: params2GVs conf_src.(CurTargetData) args_src st0_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
         exists args1_tgt,
           <<ARGS_TGT: params2GVs conf_tgt.(CurTargetData) args_tgt st0_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>> /\
           <<INJECT: list_forall2 (genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject)) args2_src args1_tgt>>)
      (INCR: InvMem.Rel.le (InvMem.Rel.lift st0_src.(Mem) st0_tgt.(Mem)
                                            (memory_blocks_of conf_src st0_src.(EC).(Locals) inv0.(Invariant.src).(Invariant.unique))
                                            (memory_blocks_of conf_tgt st0_tgt.(EC).(Locals) inv0.(Invariant.tgt).(Invariant.unique))
                                            invmem0) invmem1)
      (MEM_AFTER_CALL: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem1)
  : (* exists invst2  *) exists invmem2,
      <<INCR: InvMem.Rel.le invmem0 invmem2>> /\
      <<STATE:
        InvState.Rel.sem
          conf_src conf_tgt
          (mkState st0_src.(EC) st0_src.(ECS) mem1_src)
          (mkState st0_tgt.(EC) st0_tgt.(ECS) mem1_tgt)
          invst0 invmem2 (ForgetMemoryCall.t inv0)>> /\
      <<MEM: InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem2>> /\
      <<MEM_INJ: invmem2.(InvMem.Rel.inject) = invmem1.(InvMem.Rel.inject)>>.
Proof.
  exists (InvMem.Rel.mk
       (InvMem.Unary.mk
          (InvMem.Unary.private invmem0.(InvMem.Rel.src))
          (InvMem.Unary.private_parent invmem0.(InvMem.Rel.src))
          (InvMem.Unary.mem_parent invmem0.(InvMem.Rel.src))
          (InvMem.Unary.unique_parent invmem0.(InvMem.Rel.src))
          (InvMem.Unary.nextblock invmem1.(InvMem.Rel.src)))
       (InvMem.Unary.mk
          (InvMem.Unary.private invmem0.(InvMem.Rel.tgt))
          (InvMem.Unary.private_parent invmem0.(InvMem.Rel.tgt))
          (InvMem.Unary.mem_parent invmem0.(InvMem.Rel.tgt))
          (InvMem.Unary.unique_parent invmem0.(InvMem.Rel.tgt))
          (InvMem.Unary.nextblock invmem1.(InvMem.Rel.tgt)))
       invmem0.(InvMem.Rel.gmax) invmem1.(InvMem.Rel.inject)).
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
    + econs; eauto.
      inv LE_SRC. ss.
    + econs; eauto.
      inv LE_TGT. ss.
  - econs; ss.
    ii. exploit MAYDIFF; eauto. i.
    erewrite sem_idT_eq_locals.
    { des. esplits; eauto.
      eapply genericvalues_inject.gv_inject_incr; eauto. }
    ss.
  - econs; ss.
Qed.
