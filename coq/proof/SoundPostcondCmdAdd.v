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
Require Import Exprs.
Require Import Hints.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.
Require Import SoundReduceMaydiff.
Require Import memory_props.
Require Import TODOProof.

Set Implicit Arguments.


Definition cmd_is_normal (c:cmd): bool :=
  match c with
  | insn_malloc _ _ _ _
  | insn_free _ _ _
  | insn_alloca _ _ _ _
  | insn_load _ _ _ _
  | insn_store _ _ _ _ _
  | insn_call _ _ _ _ _ _ _ => false
  | _ => true
  end.

Lemma normal_event
      conf st0 st1 evt cmd cmds
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd::cmds)
      (NORMAL: cmd_is_normal cmd):
  evt = events.E0.
Proof.
  inv STEP; ss. inv CMDS. ss.
Qed.

(* TODO Add To Metatheory?? *)
(* Lemma AtomSetImpl_from_list_inter {X: Type} x l1 l2 *)
(*       (IN1: List.In x l1) *)
(*       (IN2: List.In x l2) *)
(*   : *)
(*     AtomSetImpl.mem x (AtomSetImpl.inter (AtomSetImpl_from_list l1) *)
(*                                          (AtomSetImpl_from_list l2)). *)
(* Proof. *)
(*   apply AtomSetImpl_from_list_spec in IN1. *)
(*   apply AtomSetImpl_from_list_spec in IN2. *)
(*   rewrite AtomSetFacts.inter_b. *)
(*   rewrite IN1. rewrite IN2. ss. *)
(* Qed. *)

(* Lemma AtomSetImpl_mem_is_empty x s: *)
(*   AtomSetImpl.mem x s -> *)
(*   ~(AtomSetImpl.is_empty s). *)
(* Proof. *)
(*   ii. *)
(*   apply AtomSetFacts.is_empty_iff in H0. *)
(*   apply AtomSetFacts.mem_iff in H. *)
(*   exploit H0; eauto. *)
(* Qed. *)

Lemma AtomSetImpl_inter_empty
      a l1 l2
      (EMPTY: AtomSetImpl.Empty (AtomSetImpl.inter l1 l2))
      (IN: a `in` l1)
  :
    <<NOTIN: a `notin` l2>>.
Proof.
  ii. exploit EMPTY; eauto.
Qed.

Lemma AtomSetImpl_from_list_inter_is_empty
      l1 l2
      (INTER_EMPTY: AtomSetImpl.is_empty
                      (AtomSetImpl.inter (AtomSetImpl_from_list l1)
                                         (AtomSetImpl_from_list l2)) = true)
  :
    List.Forall (fun x => List.Forall (fun y => x <> y) l2) l1
    (* List.forallb (fun x => List.forallb (fun y => negb (AtomSetFacts.eqb x y)) l2) l1 *)
.
Proof.
  revert l2 INTER_EMPTY. induction l1; ss. i.
  apply AtomSetFacts.is_empty_iff in INTER_EMPTY.
  exploit IHl1.
  { rewrite <- AtomSetFacts.is_empty_iff.
    ii. eapply INTER_EMPTY.
    eapply AtomSetFacts.inter_s_m_Proper; eauto.
    - ii.
      apply AtomSetFacts.mem_iff, AtomSetImpl_from_list_spec. right.
      apply AtomSetImpl_from_list_spec, AtomSetFacts.mem_iff. ss.
    - reflexivity.
  }
  i. econs; ss. clear -INTER_EMPTY.
  hexploit AtomSetImpl_inter_empty; eauto.
  { apply AtomSetFacts.mem_iff, AtomSetImpl_from_list_spec. left. ss. }
  intro A. des.
  apply AtomSetFacts.not_mem_iff in A.
  apply Forall_forall. ii. subst.
  apply AtomSetImpl_from_list_spec in H. clarify.
Qed.

Ltac simpl_list :=
  repeat match goal with
         | [ H: Forall _ (_ :: _) |- _ ] => inv H
         | [ H: Forall _ [] |- _ ] => clear H
         end.

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

Ltac simpl_ep_set :=
  repeat
    match goal with
    | [H: ExprPairSet.In _ (ExprPairSet.add _ _) |- _] =>
      eapply ExprPairSetFacts.add_iff in H; des; clarify
    end.

Ltac u := autounfold in *.
Hint Unfold InvState.Unary.sem_idT.
Hint Unfold Cmd.get_ids.
Hint Unfold getOperandValue.

Ltac clear_true :=
  repeat match goal with
         | [ H: is_true true |- _ ] => clear H
         | [ H: True |- _ ] => clear H
         | [ H: ?x = ?x |- _ ] => clear H
         end.

Lemma remove_def_from_maydiff_Subset
      id0 inv0
  :
    Invariant.Subset
      inv0
      (remove_def_from_maydiff
         id0 id0
         (Invariant.update_tgt (Invariant.update_unique (add id0))
                               (Invariant.update_src (Invariant.update_unique (add id0)) inv0)))
.
Proof.
  destruct inv0; ss.
  destruct src; ss.
  destruct tgt; ss.
  unfold Invariant.update_src, Invariant.update_tgt,
  remove_def_from_maydiff, Invariant.update_maydiff. ss.
  destruct (id_dec id0 id0); clarify.
  unfold Invariant.update_unique; ss.
  econs; ss; try (econs; try splits; ss).
  -
    ii.
    eapply AtomSetFacts.add_s_m. eauto.
    apply AtomSetFacts.Subset_refl.
    info_eauto. (* SUGOI!!!!!!!!!!!!!!!!!!!!!!!! *)
  -
    ii.
    eapply AtomSetFacts.add_s_m. eauto.
    apply AtomSetFacts.Subset_refl.
    info_eauto. (* SUGOI!!!!!!!!!!!!!!!!!!!!!!!! *)
  -
    ii.
    rewrite IdTSetFacts.mem_iff in *.
    rewrite IdTSetFacts.remove_b in H.
    des_bool; des; ss.
Qed.

(* TODO: let's ignore insn_malloc for now.  Revise the validator so that it rejects any occurence of insn_malloc. *)
Lemma postcond_cmd_add_inject_sound
      m_src conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
      m_tgt conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt
      invst1 invmem1 inv1
      invmem0
      evt
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (POSTCOND_CHECK: Postcond.postcond_cmd_check
                   cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1 inv1)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (MEM_STEP: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1)
      (STEP_SRC: sInsn conf_src st0_src st1_src evt)
      (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt)
      (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
      (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false)
      (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))
      (DEF_TGT: def_tgt = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt)))
      (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src))
      (USES_TGT: uses_tgt = AtomSetImpl_from_list (Cmd.get_ids cmd_tgt))
  :
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt st1_src st1_tgt invst1 invmem1
               (Postcond.postcond_cmd_add_inject cmd_src cmd_tgt inv1)>> /\
    <<POSTCOND: Postcond.postcond_cmd_check
                  cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt
                  (Postcond.postcond_cmd_add_inject cmd_src cmd_tgt inv1)>>
.
Proof.
  remember (st0_src.(Mem).(Memory.Mem.nextblock)) as src_nxt.
  remember (st0_tgt.(Mem).(Memory.Mem.nextblock)) as tgt_nxt.
  assert(ALLOC_INJECT: InvMem.Rel.inject invmem1 src_nxt = Some(tgt_nxt, 0)) by admit.
  destruct (classic (Postcond.postcond_cmd_add_inject cmd_src cmd_tgt inv1 = inv1)).
  { rewrite H in *. esplits; eauto. }
  destruct cmd_src, cmd_tgt; ss.
  - (* alloca, nop *)
    (* roughly, degenerate case for the last one *)
    admit.
  - admit. (* nop, allica *)
  - (* alloca, alloca *)
    (*
     * invmem1 = invmem0 + (newl_src -> newl_tgt)
     * invstate.rel.sem inv0: possible (monotone w.r.t. invmem)
     * invstate.rel.sem unique (added): newl <> old locations
         * newl: st0.mem.nextblock,
           wf: st0's old locations < st0.mem.nextblock (genericvalues_inject.wf_sb_mi)
     * invstate.rel.sem remove_def_from_maydiff (add): possible
     * invmem.rel.sem: adding (newl_src -> newl_tgt)
     * invmem.rel.le: possible
     * postcond_cmd_check: monotonicity
     *)
    (* unfold postcond_cmd_check in POSTCOND_CHECK. des_ifs; des_bool; clarify. *)
    unfold postcond_cmd_check in *. des_ifs; des_bool; clarify.
    {
      erewrite postcond_cmd_inject_event_Subset in Heq1; clarify.
      ss.
      repeat (des_bool; des); des_sumbool; clarify.
      eapply remove_def_from_maydiff_Subset.
    }
    ss. repeat (des_bool; des; des_sumbool). subst.
    clear_true.
    splits; ss.
    unfold remove_def_from_maydiff in *.
    destruct (id_dec id0 id0); [clear_true|ss].
    apply_all_once AtomSetImpl_from_list_inter_is_empty.
    simpl_list.

    inv STATE.

    ((inv STEP_SRC; ss); []).
    inv SRC.
    inv CMDS_SRC.

    ((inv STEP_TGT; ss); []).
    inv TGT.
    inv CMDS_TGT.
    ss.

    rename Mem0 into SRC_MEM.
    rename Mem' into SRC_MEM_STEP.
    rename Mem1 into TGT_MEM.
    rename Mem'0 into TGT_MEM_STEP.

    remember {| CurSystem := S; CurTargetData := TD;
                CurProducts := Ps; Globals := gl; FunTable := fs |} as conf_src.
    remember {| CurSystem := S0; CurTargetData := TD0;
                CurProducts := Ps0; Globals := gl0; FunTable := fs0 |} as conf_tgt.
    remember {|
        EC := {|
               CurFunction := F;
               CurBB := B;
               CurCmds := cmds_src;
               Terminator := tmn;
               Locals := updateAddAL GenericValue lc id0 (blk2GV TD mb);
               Allocas := mb :: als |};
        ECS := ECS0;
        Mem := SRC_MEM_STEP |} as EC_src.
    remember {|
        EC := {|
               CurFunction := F0;
               CurBB := B0;
               CurCmds := cmds_tgt;
               Terminator := tmn0;
               Locals := updateAddAL GenericValue lc0 id0 (blk2GV TD0 mb0);
               Allocas := mb0 :: als0 |};
        ECS := ECS1;
        Mem := TGT_MEM_STEP |} as EC_tgt.

    {
      econs; eauto.
      -
        (* SRC *)
        subst EC_src.
        econs; eauto; [].
        ss.
        (* clear TGT STEP_TGT. *)
        clear MAYDIFF LESSDEF NOALIAS PRIVATE.
        ii.
        apply AtomSetFacts.add_iff in H8.
        des; [clear UNIQUE; subst id0|apply UNIQUE; auto].
        rename x into ___________x____________.
        econs; eauto; ss.
        +
          (* VAL *)
          des_lookupAL_updateAddAL.
        +
          (* LOCALS *)
          admit.
          (* destruct val' eqn:T1; ss. *)
          (* destruct p eqn:T2; ss. *)
          (* destruct v eqn:T3; ss. *)
          (* destruct g eqn:T4; ss. *)
          (* des_lookupAL_updateAddAL. ss. *)
          (* ii. *)
          (* clarify. *)
          (* move ALLOC_INJECT at bottom. *)
          (* move MEM at bottom. *)
          (* rename b into __________BBB__________. *)
          (* (* TODO symmetry; clear dup in n/REG *) clear n. *)
          (* rename Mem0 into Mem__________00000000000. *)
          (* rename Mem' into Mem__________11111111111. *)
          (* inv MEM. *)
          (* rename st0_tgt into st_tgt_____________000000000000. *)
          (* rename st1_tgt into st_tgt_____________111111111111. *)
          (* { *)
          (*   unfold MemProps.wf_lc in *. *)
          (*   ii. *)
          (*   exploit WF_LOCAL; eauto; []; ii; des; clear WF_LOCAL. *)
          (*   red. des_ifs; clarify. *)
          (*   rename b0 into __________AAA__________. *)
          (*   rename b into __________BBB__________. *)
          (*   destruct val' eqn:T1; ss. *)
          (*   destruct p eqn:T2; ss. *)
          (*   destruct v eqn:T3; ss. *)
          (*   destruct g eqn:T4; ss. *)
          (*   clarify. *)
          (*   des; clear_true. *)
          (*   des_lookupAL_updateAddAL. *)
          (* } *)

          (* erewrite VAL' in WF_LOCAL. *)
        +
          (* MEM *)
          {
            move SRC_MEM at bottom.
            move SRC_MEM_STEP at bottom.
            move mb at bottom.
            clear - SRC_MEM_STEP MEM_STEP MEM mb H3 WF_LOCAL
                         ALLOC_INJECT H3 SRC_MEM.
            clear ___________x____________ WF_LOCAL.
            inv MEM_STEP. clear TGT INJECT. rename WF into WF_REL.
            inv SRC. clear GLOBALS PRIVATE PRIVATE_PARENT DISJOINT MEM_PARENT.
            inversion WF as [WF_A WF_B]. clear WF.
            ii.
            exploit WF_A; try apply LOAD; eauto; []; clear WF_A; intros WF_A; des.
            (*
val' is valid in Mem'.nextblock
             *)
            unfold InvState.Unary.sem_diffblock. ss.
            des_ifs.
            unfold not; i; subst.
            (*
val' < Mem'.nextblock
val' = b, i0
b = Mem'.lastblock
             *)
            admit.
          }
          (*   rename mb into ___________newBlock__________. *)
          (*   rename b into __________wfPtr_________. *)
          (*   unfold not. i. subst. *)
          (*   clear - WF H3 LOAD. *)
          (*   apply mload_inv in LOAD. des. clarify. *)

          (*   (* remember (mload_aux Mem' mc b (Integers.Int.signed 31 ofs)) as tmp. *) *)
          (*   (* generalize dependent val'. *) *)
          (*   (* induction mc; ii; ss; subst; clarify. *) *)

          (*   remember (mload_aux Mem' mc b (Integers.Int.signed 31 ofs)) as tmp. *)
          (*   generalize dependent mc. *)
          (*   induction val'; ii; ss; subst. *)
          (*   - destruct mc; ss. *)
          (*   - *)
          (*   unfold MemProps.valid_ptrs in WF. *)
          (*   induction val'; ss. *)
          (*   unfold mload in LOAD. ss. des_ifs. *)
          (* } *)
          (* { *)
          (*   assert(LLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLLINEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEEE: True) *)
          (*     by auto. *)
          (*   move Mem' at bottom. *)
          (*   move mb at bottom. *)
          (*   inversion MEM; clear MEM. clear TGT INJECT. *)
          (*   inversion SRC; clear SRC. clear GLOBALS PRIVATE PRIVATE_PARENT DISJOINT MEM_PARENT. *)
          (*   inversion WF0 as [WF_A WF_B]; clear WF0. *)
          (*   ii. *)
          (*   exploit WF_A; try apply LOAD; eauto; []; ii; des; clear WF_A. rename x into WF_A. *)
          (*   unfold InvState.Unary.sem_diffblock. *)
          (*   ss. *)
          (*   destruct val' eqn:T1; ss. *)
          (*   destruct p eqn:T2; ss. *)
          (*   destruct v eqn:T3; ss. *)
          (*   destruct g eqn:T4; ss. *)
          (*   des. *)
          (*   exploit MemProps.nextblock_malloc; try apply H3; []; ii; des. *)
          (*   exploit MemProps.malloc_result; try apply H3; []; ii; des. *)
          (*   subst mb. subst b. *)
          (*   remember (Memory.Mem.nextblock Mem0) as Mem0Plus1. *)
          (*   clear - x2 x. *)
          (*   omega. *)









            (* ii. *)
            (* move mb at bottom. *)
            (* unfold mload in *. des_ifs; ss. *)
            (* unfold InvState.Unary.sem_diffblock. des_ifs; ss. *)
            (* rename b0 into _______________B0_________________. *)
            (* rename b1 into _______________B1_________________. *)
            (* inv Heq1. *)
            (* destruct val' eqn:T1; ss. *)
            (* destruct p eqn:T2. *)
            (* destruct v eqn:T3; ss. *)
            (* destruct val' eqn:T4; ss. *)
            (* destruct g eqn:T5; ss. *)
            (* inv Heq2. *)
            (* inv T1. *)
            (* unfold not. ii. *)
            (* clarify. *)
            (* move typ0 at bottom. *)
            (* assert(exists mcs, flatten_typ TD typ0 = Some mcs) by admit. des. *)
            (* exploit MemProps.malloc_mload_aux_undef; try apply H3; eauto. *)
            (* { unfold const2GV. unfold _const2GV. unfold gundef. rewrite H8. eauto. } *)
            (* ii. *)


            (* exploit MemProps.mload_aux_malloc_same'; eauto. *)
            (* move typ0 at bottom. *)
            (* admit. *)
            (* ii. des. *)
          (* unfold getTypeAllocSize in H5. *)
          (* des_ifs. *)
          (* exploit MemProps.malloc_mload_aux_undef. try apply LOAD; eauto. *)
          (* MemProps.malloc_mload_aux_undef: *)
          (* MemProps.mload_aux_malloc_same': *)
          (* } *)
          (* { *)
          (* ii. *)
          (* unfold InvState.Unary.sem_diffblock. *)
          (* unfold mload in LOAD. *)
          (* (* des_ifs will ruin premisses *) *)
          (* des_ifs. ss. *)
          (* rename b into ___________A___________. *)
          (* rename b0 into ___________B___________. *)
          (* idtac. *)
          (* clarify. *)
          (* unfold MemProps.wf_lc in *. *)
          (* move WF_LOCAL0 at bottom. *)
          (* move Mem0 at bottom. *)
          (* rename Mem0 into _______________MemA______________. *)
          (* rename Mem' into _______________MemA222222222______________. *)

          (* rename Heq0 into BDefine. *)
          (* rename H3 into ADefine. *)
          (* move BDefine at bottom. *)
          (* unfold GV2ptr in BDefine. *)
          (* des_ifs. *)
          (* rename LOAD into BDefine. *)

          (* exploit MemProps.nextblock_malloc; try apply ADefine; []; ii; des. *)
          (* exploit MemProps.malloc_result; try apply ADefine; []; ii; des. *)
          (* subst. *)

          (* des_lookupAL_updateAddAL. *)
          (* } *)

          (* destruct mptr0 eqn:T1; ss. *)
          (* destruct p eqn:T2; ss. *)
          (* destruct v eqn:T3; ss. *)
          (* destruct m eqn:T4; ss. *)

          (* destruct val' eqn:T5; ss. *)
          (* destruct p0 eqn:T6; ss. *)
          (* destruct v0 eqn:T7; ss. *)
          (* destruct g eqn:T8; ss. *)
          (* destruct  *)
        +
          (* GLOBALS *)
          move MEM_STEP at bottom.
          inversion MEM_STEP; clear MEM_STEP. (* Using inv will ruin order of premisses *)
          inversion SRC; clear SRC.
          idtac.
          move mb at bottom.
          clear - GLOBALS H3.
          induction (Globals conf_src); ii; ss.
          destruct a. des_ifs.
          * des.
            induction val'; ii; ss.
            unfold InvState.Unary.sem_diffblock.
            ss.
            destruct a; ss.
            destruct v; ss.
            destruct val'; ss.
            rename b into bbbbbb.
            admit.
          *
            admit.


          (* unfold genericvalues_inject.wf_globals in GLOBALS. *)
          (* admit. *)
      -
        (* TGT *)
        admit.
      -
        (* MAYDIFF *)
        ii.
        simpl in NOTIN.
        rewrite IdTSetFacts.remove_b in NOTIN. repeat (des_bool; des).
        { eapply MAYDIFF; eauto. }
        unfold IdTSetFacts.eqb in NOTIN.
        destruct (IdTSetFacts.eq_dec (IdT.lift Tag.physical id0) id1); [|ss].
        clear_true. clarify.
        u. ss.

        des_lookupAL_updateAddAL.
        clarify. clear_true.

        esplits; eauto.
        move H3 at bottom.
        move H7 at bottom.
        idtac.
        unfold blk2GV.
        unfold ptr2GV.
        unfold val2GV.
        Fail eapply genericvalues_inject.gv_inject_cons.
        move CONF at bottom.
        inv CONF. inv INJECT. simpl in TARGETDATA. clarify.
        econs; eauto.
        rename mb into _____________mb______________.
        rename mb0 into _____________mb0______________.
        move WF_LOCAL0 at bottom.
        move H7 at bottom.
        move ALLOC_INJECT at bottom.

        (* exploit MemProps.nextblock_malloc; try apply H3; []; ii; des. *)
        (* exploit MemProps.nextblock_malloc; try apply H7; []; ii; des. *)
        exploit MemProps.malloc_result; try apply H3; []; ii; des.
        exploit MemProps.malloc_result; try apply H7; []; ii; des.
        rewrite x0. rewrite x1. (* subst, clarify ruin ordering of premisses *)
        unfold InvMem.Rel.inject in ALLOC_INJECT.
        destruct invmem1. ss.
        econs; eauto.
    }
Admitted.
    (* { *)
    (* destruct inv0. ss. *)
    (* unfold Invariant.update_src. ss. *)
    (* unfold Invariant.update_tgt. ss. *)
    (* unfold Invariant.update_maydiff. ss. *)

    (* econs; eauto; ss. *)
    (* + *)
    (*   { *)
    (*     clear TGT MAYDIFF. *)
    (*     inv SRC. econs; eauto. clear LESSDEF NOALIAS PRIVATE. *)
    (*     ii. *)
    (*     apply AtomSetFacts.add_iff in H0. *)
    (*     des; [|apply UNIQUE; auto]. *)
    (*     subst. *)
    (*     move ALLOC_INJECT at bottom. *)
    (*     unfold MemProps.wf_lc in WF_LOCAL. *)
    (*     (* econs; eauto. *) *)
    (*     ((inv STEP_SRC; ss); []). *)
    (*     ((inv STEP_TGT; ss); []). *)
    (*     exploit WF_LOCAL; des_lookupAL_updateAddAL; eauto; []; ii; des. *)
    (*     inv x0. inv H9. *)
    (*     econs; ss; eauto. *)
    (*     - (* VAL *) des_lookupAL_updateAddAL. *)
    (*     - (* LOCALS *) ii. des_lookupAL_updateAddAL. *)
    (*       unfold InvState.Unary.sem_diffblock. ss. *)
    (*       { *)
    (*         des_ifs. *)
    (*         rename b into bbbbbbbbbbbbbbb. *)
    (*         rename mb into mmmmmmmmmmmmmmmmmm. *)
    (*         unfold AtomSetImpl.For_all in UNIQUE. *)
    (*       } *)
    (*       { *)
    (*         destruct val' eqn:VAL; ss. *)
    (*         destruct p; ss. *)
    (*         destruct v; ss. *)
    (*         destruct g; ss. *)
    (*         unfold GV2ptr. ss. *)
    (*         rename b into bbbbbbbbbbbbbbb. *)
    (*         rename mb into mmmmmmmmmmmmmmmmmm. *)
    (*         admit. *)
    (*       } *)
    (*     - ii. *)
    (*       destruct val' eqn:VAL; ss. *)
    (*       destruct p; ss. *)
    (*       destruct v1; ss. *)
    (*       cbn. *)
    (*       destruct g; ss. *)
    (*       des_ifs. *)
    (*       admit. *)
    (*   } *)
    (* + admit. *)
    (* + *)
    (*   { *)
    (*     ((inv STEP_SRC; ss); []). *)
    (*     ((inv STEP_TGT; ss); []). *)
    (*     i. *)
    (*     rewrite IdTSetFacts.remove_b in NOTIN. *)
    (*     repeat (des_bool; des). *)
    (*     { apply MAYDIFF; auto. } *)
    (*     unfold IdTSetFacts.eqb in NOTIN. *)
    (*     des_ifs; []. *)
    (*     clear_true. *)
    (*     (* econs. (* DONT USE econs HERE!! Early Binding !! *) *) *)
    (*     unfold InvState.Rel.sem_inject. *)
    (*     i. *)
    (*     u; ss. *)
    (*     des_lookupAL_updateAddAL. *)
    (*     esplits; eauto. *)
    (*     clear_true. *)
    (*     move H7 at bottom. *)
    (*     move H3 at bottom. *)
    (*     simpl. *)
    (*     (* compute *) *)
    (*     unfold blk2GV. unfold ptr2GV. cbn. *)
    (*     unfold getPointerSize. *)
    (*     unfold getPointerSize0. *)
    (*     cbn. *)
    (*     hnf. *)
    (*     simpl. *)
    (*     destruct TD; simpl. *)
    (*     destruct TD0; simpl. *)
    (*     unfold val2GV. *)
    (*     move ALLOC_INJECT at bottom. *)
    (*     exploit MemProps.malloc_result; try apply H7; eauto; []; ii; des. *)
    (*     exploit MemProps.malloc_result; try apply H3; eauto; []; ii; des. *)
    (*     subst. *)

    (*     econs; eauto. *)

(* MemProps.nextblock_malloc: *)
(* MemProps.malloc_result: *)
(*       } *)

(* Admitted. *)

Lemma postcond_cmd_inject_event_Subset src tgt inv0 inv1
      (INJECT_EVENT: postcond_cmd_inject_event src tgt inv0)
      (SUBSET_SRC: ExprPairSet.Subset
                 (inv0.(Invariant.src).(Invariant.lessdef))
                 (inv1.(Invariant.src).(Invariant.lessdef)))
      (SUBSET_TGT: ExprPairSet.Subset
                 (inv0.(Invariant.tgt).(Invariant.lessdef))
                 (inv1.(Invariant.tgt).(Invariant.lessdef)))
  :
    <<INJECT_EVENT: postcond_cmd_inject_event src tgt inv1>>
.
Proof.
  red.
  destruct src, tgt; ss.
  -
    apply ExprPairSetFacts.exists_iff; try by solve_compat_bool.
    apply ExprPairSetFacts.exists_iff in INJECT_EVENT; try by solve_compat_bool.
    unfold ExprPairSet.Exists in *.
    des.
    esplits; eauto.
  - repeat (des_bool; des).
    clarify. repeat des_bool.
    apply andb_true_iff; splits; [auto|]. (* TODO Why des_bool does not clear this?????? *)
    admit.
Admitted.

Lemma lessdef_add
      conf st invst lessdef lhs rhs
      (FORALL: ExprPairSet.For_all
                 (InvState.Unary.sem_lessdef conf st invst)
                 lessdef)
      (EQ: InvState.Unary.sem_expr conf st invst lhs = InvState.Unary.sem_expr conf st invst rhs):
  ExprPairSet.For_all
    (InvState.Unary.sem_lessdef conf st invst)
    (ExprPairSet.add (lhs, rhs) (ExprPairSet.add (rhs, lhs) lessdef)).
Proof.
  ii. simpl_ep_set; ss; cycle 2.
  - apply FORALL; ss.
  - rewrite <- EQ. esplits; eauto. apply GVs.lessdef_refl. (* TODO: reflexivity *)
  - rewrite EQ. esplits; eauto. apply GVs.lessdef_refl. (* TODO: reflexivity *)
Qed.

(* TODO Move to InvState? Unity with InvState.Unary.sem_valueT_physical? *)
Lemma sem_list_valueT_physical
      conf state invst0 sz_values1 lc gl
      __INSN_ID__ mp'
  (STATE: Locals (EC state) = updateAddAL GenericValue lc __INSN_ID__ mp')
  (CONFIG: (Globals conf) = gl)
  (* (POSTCOND_CHECK: Forall (fun y => __INSN_ID__ <> y) *)
  (*                         (filter_map (Value.get_ids <*> snd) sz_values1)) *)
  (POSTCOND_CHECK: Forall (fun y => __INSN_ID__ <> y)
                          (filter_map Value.get_ids (List.map snd sz_values1)))
  :
    <<EQUIV: values2GVs (CurTargetData conf) sz_values1 lc gl =
             InvState.Unary.sem_list_valueT
               conf state invst0
               (List.map (fun elt => (fst elt,
                                      ValueT.lift Tag.physical (snd elt))) sz_values1)>>
.
Proof.
  red.
  generalize dependent lc.
  generalize dependent gl.
  generalize dependent POSTCOND_CHECK.
  induction sz_values1; ii; ss.
  destruct a; ss.
  rewrite IHsz_values1; auto; cycle 1.
  { unfold compose in *. ss. destruct t; ss; simpl_list; ss. }
  clear IHsz_values1.
  remember
    (InvState.Unary.sem_list_valueT
       conf state invst0
       (List.map (fun elt => (fst elt, ValueT.lift Tag.physical (snd elt))) sz_values1)) as
      X.
  clear HeqX.
  destruct X eqn:T; ss; des_ifs;
    try (erewrite InvState.Unary.sem_valueT_physical in Heq0; eauto; []; ii; des);
    try rewrite STATE in *; u; ss;
    des_ifs; simpl_list; des_lookupAL_updateAddAL.
Qed.

Lemma postcond_cmd_add_lessdef_unary_sound_alloca
      conf st0 st1 cmd cmds def uses
      invst0 invmem0 inv0 gmax public
      evt
      (POSTCOND_CHECK: AtomSetImpl.is_empty (AtomSetImpl.inter def uses))
      (STATE: InvState.Unary.sem conf st1 invst0 invmem0 inv0)
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0)
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd :: cmds)
      (NONCALL: Instruction.isCallInst cmd = false)
      (DEF: def = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))
      (USES: uses = AtomSetImpl_from_list (Cmd.get_ids cmd))
      id1 typ1 value1 align1
      (GEP: cmd = insn_alloca id1 typ1 value1 align1)
  :
    <<STATE: InvState.Unary.sem
               conf st1 invst0 invmem0
               (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd) inv0)>>
.
Proof.
  (inv NONCALL; []); (inv STATE; []); ss; ((inv STEP; ss); []).
  econs; eauto; [].
  unfold postcond_cmd_add_lessdef. ss.
  apply AtomSetImpl_from_list_inter_is_empty in POSTCOND_CHECK.
  (* clear LESSDEF NOALIAS UNIQUE PRIVATE. *)
  remember
    {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}
    as conf.
  assert(CONF1: conf.(CurTargetData) = TD).
  { rewrite Heqconf. auto. }
  assert(CONF2: conf.(Globals) = gl).
  { rewrite Heqconf. auto. }
  remember {|
    EC := {|
           CurFunction := F;
           CurBB := B;
           CurCmds := cs;
           Terminator := tmn;
           Locals := updateAddAL GenericValue lc id0 (blk2GV TD mb);
           Allocas := mb :: als |};
    ECS := ECS0;
    Mem := Mem' |} as state.
  assert(STATE1: state.(EC).(Locals) = updateAddAL GenericValue lc id0 (blk2GV TD mb)).
  { rewrite Heqstate. auto. }
  assert(STATE2: state.(Mem) = Mem').
  { rewrite Heqstate. auto. }
  clear Heqconf Heqstate.

  inv CMDS.
  (* clear MEM. *)
  simpl_list.
  rename id1 into __INSN_ID__.
  ss. u. ss.

  destruct (Decs.align_dec align1 Align.One) eqn:T; ss.
  -
    apply lessdef_add; [apply LESSDEF|]; [].
    {
      ss. u. ss.
      rewrite STATE1. des_lookupAL_updateAddAL.
      exploit memory_props.MemProps.nextblock_malloc; eauto; []; ii; des.
      exploit memory_props.MemProps.malloc_result; eauto; []; ii; des.
      subst. ss.
      unfold const2GV. unfold _const2GV.
      unfold gundef.
      unfold mload.
      destruct (flatten_typ (CurTargetData conf) typ1) eqn:T2; ss.
      erewrite MemProps.malloc_mload_aux_undef; eauto.
      unfold const2GV. unfold _const2GV. unfold gundef. rewrite T2. ss.
    }
  -
    apply lessdef_add.
    +
      apply lessdef_add; [apply LESSDEF|]; [].
      {
        ss. u. ss.
        rewrite STATE1. des_lookupAL_updateAddAL.
        exploit memory_props.MemProps.nextblock_malloc; eauto; []; ii; des.
        exploit memory_props.MemProps.malloc_result; eauto; []; ii; des.
        subst. ss.
        unfold const2GV. unfold _const2GV.
        unfold gundef.
        unfold mload.
        destruct (flatten_typ (CurTargetData conf) typ1) eqn:T2; ss.
        erewrite MemProps.malloc_mload_aux_undef; eauto.
        unfold const2GV. unfold _const2GV. unfold gundef. rewrite T2. ss.
      }
    +
      {
        ss. u. ss.
        rewrite STATE1. des_lookupAL_updateAddAL.
        exploit memory_props.MemProps.nextblock_malloc; eauto; []; ii; des.
        exploit memory_props.MemProps.malloc_result; eauto; []; ii; des.
        subst. ss.
        unfold const2GV. unfold _const2GV.
        unfold gundef.
        unfold mload.
        destruct (flatten_typ (CurTargetData conf) typ1) eqn:T2; ss.
        erewrite MemProps.malloc_mload_aux_undef; eauto.
        unfold const2GV. unfold _const2GV. unfold gundef. rewrite T2. ss.
      }
Unshelve.
eauto.
eauto.
eauto.
Qed.

Lemma postcond_cmd_add_lessdef_unary_sound_gep
      conf st0 st1 cmd cmds def uses
      invst0 invmem0 inv0 gmax public
      evt
      (POSTCOND_CHECK: AtomSetImpl.is_empty (AtomSetImpl.inter def uses))
      (STATE: InvState.Unary.sem conf st1 invst0 invmem0 inv0)
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0)
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd :: cmds)
      (NONCALL: Instruction.isCallInst cmd = false)
      (DEF: def = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))
      (USES: uses = AtomSetImpl_from_list (Cmd.get_ids cmd))
      id1 inbounds1 typ1 value1 sz_values1 typ2
      (GEP: cmd = insn_gep id1 inbounds1 typ1 value1 sz_values1 typ2)
  :
    <<STATE: InvState.Unary.sem
               conf st1 invst0 invmem0
               (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd) inv0)>>
.
Proof.
  (inv NONCALL; []); (inv STATE; []); ss; ((inv STEP; ss); []).
  econs; eauto; [].
  unfold postcond_cmd_add_lessdef. ss.
  apply AtomSetImpl_from_list_inter_is_empty in POSTCOND_CHECK.
  apply lessdef_add; [apply LESSDEF|]; [].
  clear LESSDEF NOALIAS UNIQUE PRIVATE.
  remember
    {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}
    as conf.
  assert(CONF1: conf.(CurTargetData) = TD).
  { rewrite Heqconf. auto. }
  assert(CONF2: conf.(Globals) = gl).
  { rewrite Heqconf. auto. }
  remember
    {|
      EC := {|
             CurFunction := F;
             CurBB := B;
             CurCmds := cs;
             Terminator := tmn;
             Locals := updateAddAL GenericValue lc id0 mp';
             Allocas := als |};
      ECS := ECS0;
      Mem := Mem0 |} as state.
  assert(STATE: state.(EC).(Locals) = updateAddAL GenericValue lc id0 mp').
  { rewrite Heqstate. auto. }
  clear Heqconf Heqstate.
  inv CMDS.
  clear MEM.
  simpl_list.
  rename id1 into __INSN_ID__.
  ss. u. ss.
  rewrite STATE. des_lookupAL_updateAddAL.
  clear e.
  rewrite <- H2. clear H2.
  exploit sem_list_valueT_physical; eauto.
  { destruct value1; ss; simpl_list; eauto. }
  ii; des.
  rewrite <- x0.
  rewrite InvState.Unary.sem_valueT_physical in *.
  destruct value1; ss.
  - rewrite STATE; simpl_list; des_lookupAL_updateAddAL.
    rewrite H.
    rewrite H1.
    ss.
  - rewrite H.
    rewrite H1.
    ss.
Qed.

Lemma postcond_cmd_add_lessdef_unary_sound_select
      conf st0 st1 cmd cmds def uses
      invst0 invmem0 inv0 gmax public
      evt
      (POSTCOND_CHECK: AtomSetImpl.is_empty (AtomSetImpl.inter def uses))
      (STATE: InvState.Unary.sem conf st1 invst0 invmem0 inv0)
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0)
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd :: cmds)
      (NONCALL: Instruction.isCallInst cmd = false)
      (DEF: def = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))
      (USES: uses = AtomSetImpl_from_list (Cmd.get_ids cmd))
      id1 value_cond typ1 value1 value2
      (GEP: cmd = insn_select id1 value_cond typ1 value1 value2)
  :
    <<STATE: InvState.Unary.sem
               conf st1 invst0 invmem0
               (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd) inv0)>>
.
Proof.
  (inv NONCALL; []); (inv STATE; []); ss; ((inv STEP; ss); []).
  econs; eauto; [].
  unfold postcond_cmd_add_lessdef. ss.
  apply AtomSetImpl_from_list_inter_is_empty in POSTCOND_CHECK.
  apply lessdef_add; [apply LESSDEF|]; [].
  clear LESSDEF NOALIAS UNIQUE PRIVATE.
  remember
    {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}
    as conf.
  assert(CONF1: conf.(CurTargetData) = TD).
  { rewrite Heqconf. auto. }
  assert(CONF2: conf.(Globals) = gl).
  { rewrite Heqconf. auto. }
  remember
  {|
    EC := {|
           CurFunction := F;
           CurBB := B;
           CurCmds := cs;
           Terminator := tmn;
           Locals := updateAddAL GenericValue lc id0 (if decision then gvs1 else gvs2);
           Allocas := als |};
    ECS := ECS0;
    Mem := Mem0 |} as state.
  assert(STATE: state.(EC).(Locals) =
                updateAddAL GenericValue lc id0 (if decision then gvs1 else gvs2)).
  { rewrite Heqstate. auto. }
  clear Heqconf Heqstate.
  inv CMDS.
  clear MEM.
  simpl_list.
  rename id1 into __INSN_ID__.
  ss. u. ss.
  rewrite STATE. des_lookupAL_updateAddAL.
  clear e.
  rewrite ? InvState.Unary.sem_valueT_physical in *.
  inv H3.
  destruct value_cond, value1, value2; simpl in *;
    try rewrite STATE; simpl_list; des_lookupAL_updateAddAL;
      try rewrite H; try rewrite H1; try rewrite H2; try rewrite INT; ss.
Qed.

Lemma postcond_cmd_add_lessdef_unary_sound
      conf st0 st1 cmd cmds def uses
      invst0 invmem0 inv0 gmax public
      evt
      (POSTCOND_CHECK: AtomSetImpl.is_empty (AtomSetImpl.inter def uses))
      (STATE: InvState.Unary.sem conf st1 invst0 invmem0 inv0)
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0)
      (STEP: sInsn conf st0 st1 evt)
      (CMDS: st0.(EC).(CurCmds) = cmd :: cmds)
      (NONCALL: Instruction.isCallInst cmd = false)
      (DEF: def = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))
      (USES: uses = AtomSetImpl_from_list (Cmd.get_ids cmd))
  :
    <<STATE: InvState.Unary.sem
               conf st1 invst0 invmem0
               (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd) inv0)>>
.
Proof.
  destruct cmd;
    try (eapply postcond_cmd_add_lessdef_unary_sound_alloca; eauto; fail);
    try (eapply postcond_cmd_add_lessdef_unary_sound_gep; eauto; fail);
    try (eapply postcond_cmd_add_lessdef_unary_sound_select; eauto; fail);
    ss; (inv NONCALL; []); (inv STATE; []); ss; ((inv STEP; ss); []);
      try (econs; eauto; []; apply lessdef_add; [apply LESSDEF|]; ss;
           rewrite ? InvState.Unary.sem_valueT_physical in *; ss;
           apply AtomSetImpl_from_list_inter_is_empty in POSTCOND_CHECK; [];
           repeat match goal with
                  | [ v: value |- _ ] => destruct v
                  end; u; ss; simpl_list; des_lookupAL_updateAddAL; des_ifs; fail).
  - (* load *)
    econs; eauto; [].
    unfold postcond_cmd_add_lessdef. ss.
    des_ifs;
      repeat apply lessdef_add; ss;
        (rewrite ? InvState.Unary.sem_valueT_physical in *; ss; [];
         apply AtomSetImpl_from_list_inter_is_empty in POSTCOND_CHECK; [];
         repeat match goal with
                | [ v: value |- _ ] => destruct v
                end; u; ss; simpl_list; des_lookupAL_updateAddAL; des_ifs).
  - (* store *)
    econs; eauto; [].
    unfold postcond_cmd_add_lessdef. ss.
    apply AtomSetImpl_from_list_inter_is_empty in POSTCOND_CHECK.
    simpl_list.
    des_ifs.
    +
      apply lessdef_add; [apply LESSDEF|].
      clear LESSDEF NOALIAS UNIQUE PRIVATE.
      ss.
      destruct value1, value2; ss; u; ss; rewrite H; rewrite H0; des_lookupAL_updateAddAL;
        erewrite mstore_mload_same; eauto.
    +
      apply lessdef_add.
      apply lessdef_add; [apply LESSDEF|].
      clear LESSDEF NOALIAS UNIQUE PRIVATE.
      ss.
      destruct value1, value2; ss; u; ss; rewrite H; rewrite H0; des_lookupAL_updateAddAL;
        erewrite mstore_mload_same; eauto.
      ss.
      destruct value1, value2; ss; u; ss; rewrite H; rewrite H0; des_lookupAL_updateAddAL;
        erewrite mstore_mload_same; eauto.
Qed.

Lemma postcond_cmd_add_lessdef_src_sound
      conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
      conf_tgt st1_tgt cmd_tgt def_tgt uses_tgt
      invst0 invmem0 inv0
      evt
      (POSTCOND: Postcond.postcond_cmd_check
                   cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv0)
      (STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem0)
      (STEP_SRC: sInsn conf_src st0_src st1_src evt)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
      (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
      (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))
      (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src))
  :
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt st1_src st1_tgt invst0 invmem0
               (Invariant.update_src
                  (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd_src)) inv0)>> /\
    <<POSTCOND: Postcond.postcond_cmd_check
                  cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt
                  (Invariant.update_src
                     (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd_src)) inv0)>>
.
Proof.
  unfold postcond_cmd_check in POSTCOND. des_ifs. des_bool.
  (* clear Heq0. *) (* later used to rebuild POSTCOND *)
  move Heq0 at top.
  inv STATE.
  inv MEM.
  destruct invst0. destruct invmem0. ss.
  exploit postcond_cmd_add_lessdef_unary_sound;
    try apply SRC; try apply SRC0; try apply STEP_SRC; eauto; []; ii; des.
  splits; eauto; ss.
  - unfold postcond_cmd_check. des_ifs. des_bool.
    exfalso.
    eapply postcond_cmd_inject_event_Subset in Heq1.
    des. unfold is_true in Heq1.
    rewrite Heq1 in Heq3. ss.
    ss.
    eapply postcond_cmd_add_lessdef_Subset.
    ss.
Qed.

Lemma postcond_cmd_add_lessdef_tgt_sound
      conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
      conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt
      invst0 invmem0 inv0
      evt
      (POSTCOND: Postcond.postcond_cmd_check cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv0)
      (STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem0)
      (STEP_SRC: sInsn conf_src st0_src st1_src evt)
      (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
      (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt)
      (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
      (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false)
      (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))
      (DEF_TGT: def_tgt = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt)))
      (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src))
      (USES_TGT: uses_tgt = AtomSetImpl_from_list (Cmd.get_ids cmd_tgt)):
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt st1_src st1_tgt invst0 invmem0
               (Invariant.update_tgt
                  (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd_tgt)) inv0)>> /\
    <<POSTCOND: Postcond.postcond_cmd_check
                  cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt
                  (Invariant.update_tgt
                     (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd_tgt)) inv0)>>
.
Proof.
  unfold postcond_cmd_check in POSTCOND. des_ifs. des_bool.
  (* clear Heq0. *) (* later used to rebuild POSTCOND *)
  move Heq1 at top.
  inv STATE.
  inv MEM.
  destruct invst0. destruct invmem0. ss.
  exploit postcond_cmd_add_lessdef_unary_sound;
    try apply TGT; try apply TGT0; try apply STEP_TGT; eauto; []; ii; des.
  splits; eauto; ss.
  - unfold postcond_cmd_check. des_ifs. des_bool.
    exfalso.
    eapply postcond_cmd_inject_event_Subset in Heq1.
    des. unfold is_true in Heq1.
    rewrite Heq1 in Heq3. ss.
    ss.
    eapply postcond_cmd_add_lessdef_Subset.
Qed.

(* Lemma postcond_cmd_add_remove_def_from_maydiff_sound *)
(*       conf_src st0_src st1_src cmd_src cmds_src def_src uses_src *)
(*       conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt *)
(*       invst0 invmem0 inv0 *)
(*       evt *)
(*       (POSTCOND: Postcond.postcond_cmd_check cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv0) *)
(*       (STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0 inv0) *)
(*       (MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem0) *)
(*       (STEP_SRC: sInsn conf_src st0_src st1_src evt) *)
(*       (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt) *)
(*       (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src) *)
(*       (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt) *)
(*       (NONCALL_SRC: Instruction.isCallInst cmd_src = false) *)
(*       (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false) *)
(*       (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src))) *)
(*       (DEF_TGT: def_tgt = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt))) *)
(*       (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src)) *)
(*       (USES_TGT: uses_tgt = AtomSetImpl_from_list (Cmd.get_ids cmd_tgt)): *)
(*     <<STATE: InvState.Rel.sem *)
(*                conf_src conf_tgt st1_src st1_tgt invst0 invmem0 *)
(*                (remove_def_from_maydiff cmd_src cmd_tgt inv0)>> *)
(* . *)
(* Proof. *)
(* Admitted. *)

Theorem postcond_cmd_add_sound
        m_src conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
        m_tgt conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt
        invst1 invmem1 inv1
        invmem0
        evt
        (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
        (POSTCOND: Postcond.postcond_cmd_check cmd_src cmd_tgt
                                               def_src def_tgt uses_src uses_tgt inv1)
        (STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1 inv1)
        (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
        (MEM_STEP: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1)
        (STEP_SRC: sInsn conf_src st0_src st1_src evt)
        (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt)
        (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
        (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt)
        (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
        (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false)
        (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))
        (DEF_TGT: def_tgt = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt)))
        (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src))
        (USES_TGT: uses_tgt = AtomSetImpl_from_list (Cmd.get_ids cmd_tgt)):
  exists invst2 invmem2,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst2 invmem2
                              (Postcond.postcond_cmd_add cmd_src cmd_tgt inv1)>> /\
             <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem2>> /\
                    <<MEMLE: InvMem.Rel.le invmem1 invmem2>>.
Proof.
  unfold postcond_cmd_add.
  exploit postcond_cmd_add_inject_sound; try apply CONF;
    try apply STEP_SRC; try apply STEP_TGT; eauto; []; ii; des.
  exploit x0; eauto; ii; des; clear x0.
  exploit postcond_cmd_add_lessdef_src_sound; try apply STATE0; eauto; []; ii; des.
  exploit postcond_cmd_add_lessdef_tgt_sound; try apply STATE1; eauto; []; ii; des.
  exploit reduce_maydiff_sound; try apply STATE2; eauto; []; ii; des.
  esplits; eauto.
  reflexivity.
Qed.
