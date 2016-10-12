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
Require Import SoundForget.

Set Implicit Arguments.


Inductive mem_change : Type :=
| mem_change_alloc
    (def_var:id) (ty:typ) (s:sz) (gn:GenericValue) (a:align)
| mem_change_store
    (ptr:GenericValue) (ty:typ) (gv:GenericValue) (a:align)
| mem_change_free
    (ptr:GenericValue)
| mem_change_none
.

Inductive mem_change_inject (conf_src conf_tgt:Config) invmem: mem_change -> mem_change -> Prop :=
| mem_change_inject_alloc_alloc
    gsz gn0 gn1 a
    ty dv
    (N_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gn0 gn1)
  : mem_change_inject conf_src conf_tgt invmem (mem_change_alloc dv ty gsz gn0 a) (mem_change_alloc dv ty gsz gn1 a)
| mem_change_inject_alloc_none
    gsz gn a ty dv
  : mem_change_inject conf_src conf_tgt invmem (mem_change_alloc dv ty gsz gn a) mem_change_none
| mem_change_inject_none_alloc
    gsz gn a ty dv
  : mem_change_inject conf_src conf_tgt invmem mem_change_none (mem_change_alloc dv ty gsz gn a)
| mem_change_inject_store_store
    ptr0 ptr1 gv0 gv1 ty a
    (PTR_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) ptr0 ptr1)
    (VAL_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gv0 gv1)
  : mem_change_inject conf_src conf_tgt invmem (mem_change_store ptr0 ty gv0 a) (mem_change_store ptr1 ty gv1 a)
| mem_change_inject_store_nop
    ptr gv ty a b ofs
    (GV2PTR: GV2ptr conf_src.(CurTargetData) (getPointerSize conf_src.(CurTargetData)) ptr = Some (Values.Vptr b ofs))
    (IN: In b invmem.(InvMem.Rel.src).(InvMem.Unary.private))
  : mem_change_inject conf_src conf_tgt invmem (mem_change_store ptr ty gv a) mem_change_none
| mem_change_inject_free
    ptr0 ptr1
    (PTR_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) ptr0 ptr1)
    : mem_change_inject conf_src conf_tgt invmem (mem_change_free ptr0) (mem_change_free ptr1)
| mem_change_inject_none
    : mem_change_inject conf_src conf_tgt invmem mem_change_none mem_change_none
.

Inductive states_mem_change conf mem0 mem1: mem_change -> Prop :=
| states_mem_change_alloc
    ty bsz gn a dv mb
    (MALLOC: Some (mem1, mb) = malloc conf.(CurTargetData) mem0 bsz gn a)
  : states_mem_change conf mem0 mem1 (mem_change_alloc dv ty bsz gn a)
| states_mem_change_store
    ptr ty gv a
    (STORE: Some mem1 = mstore conf.(CurTargetData) mem0 ptr ty gv a)
  : states_mem_change conf mem0 mem1 (mem_change_store ptr ty gv a)
| states_mem_change_free
    ptr
    (FREE: Some mem1 = free conf.(CurTargetData) mem0 ptr)
  : states_mem_change conf mem0 mem1 (mem_change_free ptr)
| states_mem_change_none
    (MEM_EQ: mem0 = mem1)
  : states_mem_change conf mem0 mem1 mem_change_none
.

(* Relation between mem_change and cmd *)

Definition mem_change_of_cmd conf cmd lc: option mem_change :=
  match cmd with
  | insn_alloca x ty v a =>
    match getTypeAllocSize conf.(CurTargetData) ty,
          getOperandValue conf.(CurTargetData) v lc conf.(Globals) with
      | Some tsz, Some gn => Some (mem_change_alloc x ty tsz gn a)
      | _, _ => None
    end
  | insn_store _ ty v_val v_ptr a =>
    match getOperandValue conf.(CurTargetData) v_val lc conf.(Globals),
          getOperandValue conf.(CurTargetData) v_ptr lc conf.(Globals) with
    | Some gv_val, Some gv_ptr => Some (mem_change_store gv_ptr ty gv_val a)
    | _, _ => None
    end
  | insn_free x _ v_ptr =>
    match getOperandValue conf.(CurTargetData) v_ptr lc conf.(Globals) with
    | Some gv_ptr => Some (mem_change_free gv_ptr)
    | _ => None
    end
  | _ => Some mem_change_none
  end.

Definition mem_change_cmd_after conf st mc cmd inv0: Prop :=
  match cmd with
  | insn_alloca dv ty v a =>
    exists tsz gn,
    <<TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz>> /\
    <<FORGET: inv_unary_forgot inv0 (AtomSetImpl_from_list [dv])>> /\
    <<MEM_CH: mc = mem_change_alloc dv ty tsz gn a>>
  | insn_store _ ty v_val v_ptr a =>
    exists gv_val gv_ptr,
    <<VAL: getOperandValue conf.(CurTargetData) v_val st.(EC).(Locals) conf.(Globals) = Some gv_val>> /\
    <<PTR: getOperandValue conf.(CurTargetData) v_ptr st.(EC).(Locals) conf.(Globals) = Some gv_ptr>> /\
    <<MEM_CH: mc = mem_change_store gv_ptr ty gv_val a>>
  | insn_free dv _ v_ptr =>
    exists gv_ptr,
    <<PTR: getOperandValue conf.(CurTargetData) v_ptr st.(EC).(Locals) conf.(Globals) = Some gv_ptr>> /\
    <<MEM_CH: mc = mem_change_free gv_ptr>>
  | _ => mc = mem_change_none
  end.

(* proof for private_parent *)

Definition mem_change_no_private_parent conf mc pp: Prop :=
  match mc with
  | mem_change_store ptr _ _ _
  | mem_change_free ptr =>
    forall b ofs
           (PTR: GV2ptr conf.(CurTargetData) conf.(CurTargetData).(getPointerSize) ptr =
                 Some (Values.Vptr b ofs)),
      ~ In b pp
  | _ => True
  end.

Lemma gv_inject_ptr_public_src
      invmem ptr0 ptr1 b ofs conf_src
      (PTR_INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) ptr0 ptr1)
      (PTR : GV2ptr (CurTargetData conf_src) (getPointerSize (CurTargetData conf_src)) ptr0 = Some (Values.Vptr b ofs))
  : InvMem.Rel.public_src (InvMem.Rel.inject invmem) b.
Proof.
  exploit genericvalues_inject.simulation__GV2ptr; try exact PTR; eauto. i. des.
  ii. inv x1. clarify.
Qed.

Lemma mem_change_inject_no_private_parent_src
      conf_src mc_src mem_src
      conf_tgt mc_tgt mem_tgt
      invmem
      (SEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt invmem)
      (INJECT: mem_change_inject conf_src conf_tgt invmem mc_src mc_tgt)
  : mem_change_no_private_parent conf_src mc_src invmem.(InvMem.Rel.src).(InvMem.Unary.private_parent).
Proof.
  inv SEM.
  inv SRC.
  inv INJECT; try econs; ii.
  - exploit PRIVATE_PARENT; eauto. i. des.
    hexploit gv_inject_ptr_public_src; try apply PTR; eauto.
  - rewrite PTR in GV2PTR. clarify.
    exploit PRIVATE; eauto. i. des.
    exploit DISJOINT; eauto.
  - exploit PRIVATE_PARENT; eauto. i. des.
    hexploit gv_inject_ptr_public_src; try apply PTR; eauto.
Qed.

Lemma simulation__GV2ptr_tgt
     : forall (mi : Values.meminj) (TD : TargetData) (gv1 gv1' : GenericValue) (v' : Values.val),
       genericvalues_inject.gv_inject mi gv1 gv1' ->
       GV2ptr TD (getPointerSize TD) gv1' = Some v' ->
       exists v : Values.val, GV2ptr TD (getPointerSize TD) gv1 = Some v /\ memory_sim.MoreMem.val_inject mi v v'.
Proof.
  i.
  unfold GV2ptr in *.
  destruct gv1'; clarify.
  destruct p. destruct v; clarify.
  destruct gv1'; clarify.
  destruct gv1; inv H.
  destruct v1; inv H3.
  inv H6.
  esplits; eauto.
Qed.

Lemma gv_inject_ptr_public_tgt
      ptr_src
      ptr_tgt conf_tgt b_tgt ofs_tgt
      invmem
      (PTR_INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) ptr_src ptr_tgt)
      (PTR_TGT : GV2ptr (CurTargetData conf_tgt) (getPointerSize (CurTargetData conf_tgt)) ptr_tgt = Some (Values.Vptr b_tgt ofs_tgt))
  : InvMem.Rel.public_tgt (InvMem.Rel.inject invmem) b_tgt.
Proof.
  exploit simulation__GV2ptr_tgt; try exact PTR_TGT; eauto. i. des.
  inv x1. unfold InvMem.Rel.public_tgt. esplits; eauto.
Qed.

Lemma mem_change_inject_no_private_parent_tgt
      conf_src mc_src mem_src
      conf_tgt mc_tgt mem_tgt
      invmem
      (SEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt invmem)
      (INJECT: mem_change_inject conf_src conf_tgt invmem mc_src mc_tgt)
  : mem_change_no_private_parent conf_tgt mc_tgt invmem.(InvMem.Rel.tgt).(InvMem.Unary.private_parent).
Proof.
  inv SEM.
  inv TGT.
  inv INJECT; try econs; ii.
  - exploit PRIVATE_PARENT; eauto. i. des.
    hexploit gv_inject_ptr_public_tgt; try apply PTR; eauto.
  - exploit PRIVATE_PARENT; eauto. i. des.
    hexploit gv_inject_ptr_public_tgt; try apply PTR; eauto.
Qed.

(* Subset *)

Lemma forget_memory_unary_Subset
      def_mem inv0
  : Invariant.Subset_unary (ForgetMemory.unary def_mem inv0) inv0.
Proof.
  unfold ForgetMemory.unary.
  econs; ss; ii; des_ifs; try econs; ss.
  eapply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool.
  des. eauto.
Qed.

Lemma forget_memory_Subset
      def_mem_src def_mem_tgt  inv0
  : Invariant.Subset (ForgetMemory.t def_mem_src def_mem_tgt inv0) inv0.
Proof.
  unfold ForgetMemory.t; des_ifs;
    econs; ss; try reflexivity; apply forget_memory_unary_Subset.
Qed.

(* specs for equiv_except *)

Lemma sem_idT_eq_locals
      st0 st1 invst0 x
      (LOCALS_EQ : Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_idT st0 invst0 x = InvState.Unary.sem_idT st1 invst0 x.
Proof.
  destruct x as [[] x]; unfold InvState.Unary.sem_idT in *; ss.
  rewrite LOCALS_EQ; eauto.
Qed.

Lemma sem_valueT_eq_locals
      conf st0 st1 invst0 v
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_valueT conf st1 invst0 v = InvState.Unary.sem_valueT conf st0 invst0 v.
Proof.
  destruct v; eauto.
  eapply sem_idT_eq_locals; eauto.
Qed.

Lemma sem_list_valueT_eq_locals
      conf st0 st1 invst0 lsv
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_list_valueT conf st1 invst0 lsv = InvState.Unary.sem_list_valueT conf st0 invst0 lsv.
Proof.
  induction lsv; ss; i.
  destruct a as [s v].
  exploit sem_valueT_eq_locals; eauto. intro EQ_VAL.
  rewrite EQ_VAL. rewrite IHlsv. eauto.
Qed.

(* Lemma sem_expr_equiv_except_mem *)
(*       conf st0 st1 invst0 invmem0 inv0 *)
(*       (* cmd  *)mc def_memory e *)
(*       (STATE : InvState.Unary.sem conf st0 invst0 invmem0 inv0) *)
(*       (* (MEM_CHANGE : mem_change_cmd2 conf st0 mc cmd) *) *)
(*       (* (DEF_MEM : Cmd.get_def_memory cmd = Some def_memory) *) *)
(*       (MEM_EQUIV: state_equiv_except_mem conf st0 st1 mc) *)
(*       (DEF_MEM_SEP: mem_change_noalias_expr mc e = true) *)
(*       InvState.Unary.sem_valueT conf st0 invst0 *)
(*       InvState. *)
(*       Ptr.t *)
(*                     (* Invariant.is_unique_ptr inv0 def_memory = true \/ *) *)
(*                     (* ForgetMemory.is_noalias_Expr inv0 def_memory e = true) *) *)
(*   : InvState.Unary.sem_expr conf st0 invst0 e = InvState.Unary.sem_expr conf st1 invst0 e. *)
(* Proof. *)
(*   ii. inv MEM_EQUIV. *)
(*   destruct e; ss; *)
(*     sem_value_st; eauto. *)
(*   des_ifs. *)
(*   destruct mc. *)
(*   - inv MEM_CHANGE_EQUIV. *)
(*     inv STATE. *)
(*     des. *)
(*     + unfold Invariant.is_unique_ptr in *. *)
(*       unfold Invariant.is_unique_value in *. *)
(*       destruct def_memory as [[[[] x]|] ty]; ss. *)
(*       exploit UNIQUE. *)
(*       { apply AtomSetFacts.mem_iff; eauto. } *)
(*       i. *)
(*       inv x0. *)

(*       InvState.Unary.sem_noalias conf g _ t _ *)


(* for same locals and memories *)
Lemma sem_expr_eq_locals_mem
      conf st0 st1 invst0 e
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
      (MEM_EQ: Mem st0 = Mem st1)
  : InvState.Unary.sem_expr conf st1 invst0 e = InvState.Unary.sem_expr conf st0 invst0 e.
Proof.
  Ltac sem_value_st :=
      let H' := fresh in
      repeat
        match goal with
        | [LOCALS_EQ: Locals (EC ?st0) = Locals (EC ?st1) |-
           context[ InvState.Unary.sem_valueT ?conf ?st1 ?invst0 ?v ] ] =>
          exploit sem_valueT_eq_locals; try exact LOCALS_EQ; intro H';
          rewrite H'; clear H'
        | [LOCALS_EQ: Locals (EC ?st0) = Locals (EC ?st1) |-
           context[ InvState.Unary.sem_list_valueT ?conf ?st1 ?invst0 ?lsv ] ] =>
          exploit sem_list_valueT_eq_locals; try exact LOCALS_EQ; intro H';
          rewrite H'; clear H'
        end.
  destruct e; ss; try rewrite <- MEM_EQ; sem_value_st; eauto.
Qed.

Lemma unary_sem_eq_locals_mem
      conf st0 st1 invst0 invmem0 inv0
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
      (MEM_EQ : Mem st0 = Mem st1)
  : <<SEM_ST0: InvState.Unary.sem conf st0 invst0 invmem0 inv0>> <->
    <<SEM_ST1: InvState.Unary.sem conf st1 invst0 invmem0 inv0>>.
Proof.
  split; intro STATE.
  { inv STATE.
    econs.
    - ii.
      exploit LESSDEF; eauto.
      { erewrite sem_expr_eq_locals_mem; eauto. }
      i. des.
      esplits; eauto.
      erewrite sem_expr_eq_locals_mem; eauto.
    - inv NOALIAS.
      econs; i; [exploit DIFFBLOCK | exploit NOALIAS0]; eauto;
        erewrite sem_valueT_eq_locals; eauto.
    - ii. exploit UNIQUE; eauto. intro UNIQ_X. inv UNIQ_X.
      econs; try rewrite <- LOCALS_EQ; try rewrite <- MEM_EQ; eauto.
    - ii. exploit PRIVATE; eauto.
      erewrite sem_idT_eq_locals; eauto.
  }
  { inv STATE.
    econs.
    - ii.
      exploit LESSDEF; eauto.
      { erewrite sem_expr_eq_locals_mem; eauto. }
      i. des.
      esplits; eauto.
      erewrite sem_expr_eq_locals_mem; eauto.
    - inv NOALIAS.
      econs; i; [exploit DIFFBLOCK | exploit NOALIAS0]; eauto;
        erewrite sem_valueT_eq_locals; eauto.
    - ii. exploit UNIQUE; eauto. intro UNIQ_X. inv UNIQ_X.
      econs; try rewrite  LOCALS_EQ; try rewrite MEM_EQ; eauto.
    - ii. exploit PRIVATE; eauto.
      erewrite sem_idT_eq_locals; eauto.
  }
Qed.

(* soundness proof *)

Definition unique_preserved_mem conf st inv: Prop :=
  forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true),
    InvState.Unary.sem_unique conf st u.

Definition alloc_inject conf_src conf_tgt st1_src st1_tgt cmd_src cmd_tgt invmem1 : Prop :=
  forall x ty v_src v_tgt a
         (ALLOCA_SRC: cmd_src = insn_alloca x ty v_src a)
         (ALLOCA_TGT: cmd_tgt = insn_alloca x ty v_tgt a),
    exists b_src b_tgt gptr_src gptr_tgt,
      lookupAL _ st1_src.(EC).(Locals) x = Some gptr_src /\
      lookupAL _ st1_tgt.(EC).(Locals) x = Some gptr_tgt /\
      GV2ptr conf_src.(CurTargetData) conf_src.(CurTargetData).(getPointerSize) gptr_src =
      Some (Values.Vptr b_src (Integers.Int.zero 31)) /\
      GV2ptr conf_tgt.(CurTargetData) conf_tgt.(CurTargetData).(getPointerSize) gptr_tgt =
      Some (Values.Vptr b_tgt (Integers.Int.zero 31)) /\
      invmem1.(InvMem.Rel.inject) b_src = Some (b_tgt, 0).

Lemma step_mem_change
      st0 st1 invst0 invmem0 inv0 inv1
      cmd cmds
      conf evt
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
      (CMD: st0.(EC).(CurCmds) = cmd::cmds)
      (NONCALL: Instruction.isCallInst cmd = false)
      (STEP: sInsn conf st0 st1 evt)
      (FORGET_DEFS: inv_unary_forgot inv1 (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd))))
  : exists mc,
    <<MC_SOME: mem_change_of_cmd conf cmd st0.(EC).(Locals) = Some mc>> /\
    <<MC_AFTER: mem_change_cmd_after conf (mkState st1.(EC) st1.(ECS) st0.(Mem)) mc cmd inv1>> /\
    <<STATE_EQUIV: states_mem_change conf st0.(Mem) st1.(Mem) mc>>.
Proof.
  inv STEP; ss;
    try by inv CMD;
    esplits; ss; econs; eauto.
  - admit. (* not malloc *)
  - inv CMD.
    esplits; ss.
    + des_ifs.
    + esplits; eauto.
    + econs; eauto.
  - inv CMD.
    esplits; ss.
    + des_ifs.
    + esplits; eauto.
    + econs; eauto.
  - inv CMD.
    esplits; ss.
    + des_ifs.
    + esplits; eauto.
    + econs; eauto.
Admitted.

Lemma malloc_nextblock
      TD mem mem' sz gn a mb
      (MALLOC: malloc TD mem sz gn a = Some (mem', mb))
  : <<ALLOC_BLOCK: mb = mem.(Memory.Mem.nextblock)>> /\
    <<NEXT_BLOCK: mem'.(Memory.Mem.nextblock) = Pos.succ mem.(Memory.Mem.nextblock)>>
.
Proof.
  unfold malloc in *.
  des_ifs.
Qed.

Lemma inject_mem_change
      conf_src cmd_src mc_src st0_src
      conf_tgt cmd_tgt mc_tgt st0_tgt
      inv0 invmem0 invst0
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (INJECT_EVENT : postcond_cmd_inject_event cmd_src cmd_tgt inv0)
      (MC_SRC : mem_change_of_cmd conf_src cmd_src st0_src.(EC).(Locals) = Some mc_src)
      (MC_TGT : mem_change_of_cmd conf_tgt cmd_tgt st0_tgt.(EC).(Locals) = Some mc_tgt)
  : mem_change_inject conf_src conf_tgt invmem0 mc_src mc_tgt.
Proof.
Admitted.

Lemma inject_invmem
      conf_src st0_src st1_src cmd_src cmds_src evt_src
      conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt evt_tgt
      invst0 invmem0 inv0 inv1
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM : InvMem.Rel.sem conf_src conf_tgt (Mem st0_src) (Mem st0_tgt) invmem0)
      (CMD_SRC : CurCmds (EC st0_src) = cmd_src :: cmds_src)
      (CMD_TGT : CurCmds (EC st0_tgt) = cmd_tgt :: cmds_tgt)
      (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
      (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false)
      (STEP_SRC : sInsn conf_src st0_src st1_src evt_src)
      (STEP_TGT : sInsn conf_tgt st0_tgt st1_tgt evt_tgt)
      (INJECT_EVENT : postcond_cmd_inject_event cmd_src cmd_tgt inv0)
      (FORGOT_SRC: inv_unary_forgot inv1.(Invariant.src) (AtomSetImpl_from_list (Cmd.get_def cmd_src)))
      (FORGOT_TGT: inv_unary_forgot inv1.(Invariant.tgt) (AtomSetImpl_from_list (Cmd.get_def cmd_tgt)))
  : exists invmem1,
    <<ALLOC_INJECT: alloc_inject conf_src conf_tgt st1_src st1_tgt cmd_src cmd_tgt invmem1>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt (Mem st1_src) (Mem st1_tgt) invmem1 >> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1 >>.
Proof.
  (* TODO: mc ~ mc0 *)
Admitted.

Lemma forget_memory_equiv_except_mem
      conf_src mem0_src st1_src mc_src cmd_src lc_src
      conf_tgt mem0_tgt st1_tgt mc_tgt cmd_tgt lc_tgt
      inv1 invst0 invmem0
      (STATE_FORGET : InvState.Rel.sem conf_src conf_tgt
                                       (mkState st1_src.(EC) st1_src.(ECS) mem0_src)
                                       (mkState st1_tgt.(EC) st1_tgt.(ECS) mem0_tgt)
                                       invst0 invmem0 inv1)
      (MC_SOME_SRC : mem_change_of_cmd conf_src cmd_src lc_src = Some mc_src)
      (MC_SOME_TGT : mem_change_of_cmd conf_tgt cmd_tgt lc_tgt = Some mc_tgt)
      (STATE_EQUIV_SRC : states_mem_change conf_src mem0_src st1_src.(Mem) mc_src)
      (STATE_EQUIV_TGT : states_mem_change conf_tgt mem0_tgt st1_tgt.(Mem) mc_tgt)
  : InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0
                     (ForgetMemory.t (Cmd.get_def_memory cmd_src) (Cmd.get_def_memory cmd_tgt) inv1).
Proof.
Admitted.

Lemma forget_memory_sound
      m_src conf_src st0_src st1_src cmd_src cmds_src evt_src
      m_tgt conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt evt_tgt
      invst0 invmem0 inv0 inv1
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (CMD_SRC: st0_src.(EC).(CurCmds) = cmd_src::cmds_src)
      (CMD_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt::cmds_tgt)
      (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
      (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false)
      (STEP_SRC: sInsn conf_src st0_src st1_src evt_src)
      (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt_tgt)
      (INJECT_EVENT: postcond_cmd_inject_event cmd_src cmd_tgt inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (FORGOT_SRC: inv_unary_forgot inv1.(Invariant.src)
                                                (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src))))
      (FORGOT_TGT: inv_unary_forgot inv1.(Invariant.tgt)
                                                (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt))))
      (STATE_FORGET: InvState.Rel.sem conf_src conf_tgt
                                      (mkState st1_src.(EC) st1_src.(ECS) st0_src.(Mem))
                                      (mkState st1_tgt.(EC) st1_tgt.(ECS) st0_tgt.(Mem))
                                      invst0 invmem0 inv1)
      (UNIQUE_PRSV_SRC: unique_preserved_mem conf_src st1_src inv1.(Invariant.src))
      (UNIQUE_PRSV_TGT: unique_preserved_mem conf_tgt st1_tgt inv1.(Invariant.tgt))
  :
    exists invmem1,
      <<ALLOC_INJECT: alloc_inject conf_src conf_tgt st1_src st1_tgt cmd_src cmd_tgt invmem1>> /\
      <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem1
                                (ForgetMemory.t (Cmd.get_def_memory cmd_src) (Cmd.get_def_memory cmd_tgt) inv1) >> /\
      <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
      <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  exploit step_mem_change.
  { inv STATE. exact SRC. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  exploit step_mem_change.
  { inv STATE. exact TGT. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  i. des.

  exploit inject_invmem; try exact INJECT_EVENT; eauto.
  i. des.
  esplits; eauto.

  eapply forget_memory_equiv_except_mem; eauto.
  admit. (* InvState.Rel.mem monotone w.r.t. invmem1 *)
Admitted.

(* until here *)



(* Lemma forget_memory_unary_sound_with_def_memory *)
(*       conf st0 invst0 invmem0 inv0 *)
(*       cmd st1 public gmax mem_change def_memory *)
(*       (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0) *)
(*       (DEF_MEM: Cmd.get_def_memory cmd = Some def_memory) *)
(*       (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0) *)
(*       (MEM_EQUIV: state_equiv_except_mem conf st0 st1 mem_change) *)
(*       (MEM_CHANGE: mem_change_cmd_after conf st0 mem_change cmd inv0) *)
(*       (NO_PRIVATE_PARENT: mem_change_no_private_parent conf mem_change invmem0.(InvMem.Unary.private_parent)) *)
(*       (UNIQUE_PRSV: unique_preserved_mem conf st1 inv0) *)
(*   : <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem0 (ForgetMemory.unary def_memory inv0)>> /\ *)
(*                    <<MEM_UNARY: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0>>. *)
(* Proof. *)
(*   destruct mem_change; *)
(*     try by (destruct cmd; ss; des; congruence). *)
(*   - splits. *)
(*     admit. *)
(*     admit. *)
    
    
(*     (* + econs. *) *)
(*     (*   { ii. ss. unfold ForgetMemory.unary in *. *) *)
(*     (*     exploit forget_memory_def_sep_mem; eauto. i. *) *)
(*     (*     exploit sem_expr_equiv_except_mem; eauto. *) *)
(*     (*     { instantiate (1:= (fst x)). *) *)
(*     (*       des; try by left; eauto. *) *)
(*     (*       right. unfold ForgetMemory.is_noalias_ExprPair in *. des_bool. des. ss. *) *)
(*     (*     } *) *)
(*     (*     exploit sem_expr_equiv_except_mem; eauto. *) *)
(*     (*     { instantiate (1:= (snd x)). *) *)
(*     (*       des; try by left; eauto. *) *)
(*     (*       right. unfold ForgetMemory.is_noalias_ExprPair in *. des_bool. des. ss. *) *)
(*     (*     } *) *)
(*     (*     i. *) *)
(*     (*     inv STATE. *) *)
(*     (*     exploit LESSDEF. *) *)
(*     (*     { des_ifs; eauto. *) *)
(*     (*       ss. eapply ExprPairSetFacts.filter_iff in H; eauto; try by solve_compat_bool. inv H; eauto. *) *)
(*     (*     } *) *)
(*     (*     { rewrite x0. eauto. } *) *)
(*     (*     i. rewrite <- x2. eauto. *) *)
(*     (*   } *) *)
(*     (*   { admit. (* alias *) } *) *)
(*     (*   { admit. } *) *)
(*     (*   { admit. } *) *)
(*     (* + inv MEM_EQUIV. *) *)
(*     (*   inv MEM_CHANGE_EQUIV. *) *)
(*     (*   inv MEM. *) *)
(*     (*   econs; eauto. *) *)
(*     (*   { i. exploit PRIVATE; eauto. i. des. *) *)
(*     (*     split; eauto. *) *)
(*     (*     admit. (* nextblock preserved after mstore *) } *) *)
(*     (*   { i. exploit PRIVATE_PARENT; eauto. i. des. *) *)
(*     (*     split; eauto. *) *)
(*     (*     admit. (* same *) } *) *)
(*     (*   { unfold mem_change_no_private_parent in *. *) *)
(*     (*     i. exploit MEM_PARENT; eauto. *) *)
(*     (*     i. rewrite x. *) *)
(*     (*     (* STORE: (Mem st1) = mstore (Mem st0) ptr .. *) *) *)
(*     (*     (* mstore says GV2ptr ptr = Some Vptr .. *) *) *)
(*     (*     (* NO_PRIVATE_PARENT tells us ~In b_ptr (private_parent) *) *) *)
(*     (*     (* since b is In private_parent, mload_aux ?mem b should be preserved *) *) *)
(*     (*     admit. *) *)
(*     (*   } *) *)
  
(*   - admit. (* free case - almost same as above *) *)
(* Admitted. *)

(* Lemma forget_memory_unary_sound_without_def_memory *)
(*       conf st0 st1 mem_change *)
(*       cmd invst0 invmem0 inv0 gmax public *)
(*       (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0) *)
(*       (DEF_MEM: Cmd.get_def_memory cmd = None) *)
(*       (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0) *)
(*       (MEM_EQUIV : state_equiv_except_mem conf st0 st1 mem_change) *)
(*       (MEM_CHANGE : mem_change_cmd_after conf st0 mem_change cmd inv0) *)
(*       (NO_PRIVATE_PARENT: mem_change_no_private_parent conf mem_change invmem0.(InvMem.Unary.private_parent)) *)
(*       (UNIQUE_PRSV: unique_preserved_mem conf st1 inv0) *)
(*   : <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem0 inv0>> /\ *)
(*     <<MEM_UNARY: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0>>. *)
(* Proof. *)
(*   destruct mem_change. *)
(*   - destruct cmd; ss. *)
(*     admit. (* TODO: for alloca *) *)
(*   - destruct cmd; ss; des; congruence. *)
(*   - destruct cmd; ss; des; congruence. *)
(*   - inv MEM_EQUIV. inv STATES_MEM_CHANGE. *)
(*     rewrite <- MEM_EQ. *)
(*     esplits; eauto. *)
(*     eapply unary_sem_eq_locals_mem; try (symmetry in LOCALS_EQ; exact LOCALS_EQ); eauto. *)
(* Admitted. *)

(* Lemma forget_memory_maydiff_preserved *)
(*       conf_src st0_src st1_src mem_change_src def_mem_src *)
(*       conf_tgt st0_tgt st1_tgt mem_change_tgt def_mem_tgt *)
(*       invst0 invmem0 inv0 *)
(*       (MEM_EQUIV_SRC : state_equiv_except_mem conf_src st0_src st1_src mem_change_src) *)
(*       (MEM_EQUIV_TGT : state_equiv_except_mem conf_tgt st0_tgt st1_tgt mem_change_tgt) *)
(*       (MAYDIFF : forall id : Tag.t * id, *)
(*           IdTSet.mem id (Invariant.maydiff inv0) = false -> *)
(*           InvState.Rel.sem_inject st0_src st0_tgt invst0 (InvMem.Rel.inject invmem0) id) *)
(*   : <<RES: forall id : Tag.t * id, *)
(*       IdTSet.mem id (Invariant.maydiff (ForgetMemory.t def_mem_src def_mem_tgt inv0)) = false -> *)
(*       InvState.Rel.sem_inject st1_src st1_tgt invst0 (InvMem.Rel.inject invmem0) id>>. *)
(* Proof. *)
(*   ii. *)
(*   assert (DROP_FORGET_MEMORY:IdTSet.mem id0 (Invariant.maydiff inv0) = false). *)
(*   { destruct def_mem_src; destruct def_mem_tgt; ss. } *)
(*   exploit MAYDIFF; eauto. *)
(*   { inv MEM_EQUIV_SRC. *)
(*     unfold InvState.Unary.sem_idT in *. *)
(*     destruct id0 as [[] x]; eauto. *)
(*     ss. rewrite LOCALS_EQ. eauto. *)
(*   } *)
(*   i. des. *)
(*   esplits; eauto. *)
(*   inv MEM_EQUIV_TGT. *)
(*   unfold InvState.Unary.sem_idT in *. *)
(*   destruct id0 as [[] x]; eauto. *)
(*   ss. rewrite <- LOCALS_EQ. eauto. *)
(* Qed. *)

(* Lemma some_injective A (a b:A): *)
(*   Some a = Some b -> a = b. *)
(* Proof. *)
(*   congruence. *)
(* Qed. *)

(* (* Lemma mem_inject_change *) *)
(* (*       conf_src st0_src st1_src cmd_src mem_change_src *) *)
(* (*       conf_tgt st0_tgt st1_tgt cmd_tgt mem_change_tgt *) *)
(* (*       invmem0 *) *)
(* (*       (mem_change_of_cmd conf_src st0_src cmd_src = Some mem_change_src) *) *)
(* (*       () *) *)
(* (*       (MEM_CHANGE_EQUIV_SRC : states_mem_change conf_src st0_src st1_src mem_change_src) *) *)
(* (*       (MEM_CHANGE_EQUIV_TGT : states_mem_change conf_tgt st0_tgt st1_tgt mem_change_tgt) *) *)
(* (*       (MEM_CHANGE_INJECT : mem_change_inject conf_src conf_tgt invmem0 mem_change_src mem_change_tgt) *) *)
(* (*       (INJECT : memory_sim.MoreMem.mem_inj (InvMem.Rel.inject invmem0) (Mem st0_src) (Mem st0_tgt)) *) *)
(* (*   : exists invmem1, *) *)
(* (*     <<ALLOC_INJECT: alloc_inject conf_src conf_tgt st1_src st1_tgt cmd_src cmd_tgt invmem1>> /\ *) *)
(* (*     <<MEM_INJ: memory_sim.MoreMem.mem_inj (InvMem.Rel.inject invmem1) (Mem st1_src) (Mem st1_tgt)>>. *) *)
(* (* Proof. *) *)
(* (* Admitted. *) *)

(* (*   inv MEM_CHANGE_INJECT. *) *)
(* (*   - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT. *) *)
(* (*     unfold malloc in *. *) *)
(* (*     apply some_injective in MALLOC. *) *)
(* (*     apply some_injective in MALLOC0. *) *)
(* (*     econs. *) *)
(* (*     + eapply Memory.Mem.alloc_right_inj; eauto. *) *)
(* (*       eapply Memory.Mem.alloc_left_unmapped_inj; eauto. *) *)
(* (*       apply mi_freeblocks. *) *)
(* (*       eapply Memory.Mem.fresh_block_alloc; eauto. *) *)
(* (*     + i. apply mi_freeblocks. ii. *) *)
(* (*       exploit Memory.Mem.valid_block_alloc; try (symmetry; exact MALLOC); eauto. *) *)
(* (*     + ii. exploit mi_mappedblocks; eauto. i. *) *)
(* (*       eapply Memory.Mem.valid_block_alloc; eauto. *) *)
(* (*     + ii. exploit mi_no_overlap; eauto. *) *)
(* (*       * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto. *) *)
(* (*         ii. subst. *) *)
(* (*         hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i. *) *)
(* (*         exploit mi_freeblocks; eauto. i. clarify. *) *)
(* (*       * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto. *) *)
(* (*         ii. subst. *) *)
(* (*         hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i. *) *)
(* (*         exploit mi_freeblocks; eauto. i. clarify. *) *)
(* (*     + ii. exploit mi_representable; eauto. des. *) *)
(* (*       * left. *) *)
(* (*         eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto. *) *)
(* (*         ii. subst. *) *)
(* (*         hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i. *) *)
(* (*         exploit mi_freeblocks; eauto. i. clarify. *) *)
(* (*       * right. *) *)
(* (*         eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto. *) *)
(* (*         ii. subst. *) *)
(* (*         hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i. *) *)
(* (*         exploit mi_freeblocks; eauto. i. clarify. *) *)
(* (*   - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT. *) *)
(* (*     rewrite <- MEM_EQ; clear MEM_EQ. *) *)
(* (*     unfold malloc in *. *) *)
(* (*     apply some_injective in MALLOC. *) *)
(* (*     econs. *) *)
(* (*     + eapply Memory.Mem.alloc_left_unmapped_inj; eauto. *) *)
(* (*       apply mi_freeblocks. *) *)
(* (*       eapply Memory.Mem.fresh_block_alloc; eauto. *) *)
(* (*     + i. apply mi_freeblocks. ii. *) *)
(* (*       exploit Memory.Mem.valid_block_alloc; try (symmetry; exact MALLOC); eauto. *) *)
(* (*     + ii. exploit mi_mappedblocks; eauto. *) *)
(* (*     + ii. exploit mi_no_overlap; eauto. *) *)
(* (*       * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto. *) *)
(* (*         ii. subst. *) *)
(* (*         hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i. *) *)
(* (*         exploit mi_freeblocks; eauto. i. clarify. *) *)
(* (*       * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto. *) *)
(* (*         ii. subst. *) *)
(* (*         hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i. *) *)
(* (*         exploit mi_freeblocks; eauto. i. clarify. *) *)
(* (*     + ii. exploit mi_representable; eauto. des. *) *)
(* (*       * left. *) *)
(* (*         eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto. *) *)
(* (*         ii. subst. *) *)
(* (*         hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i. *) *)
(* (*         exploit mi_freeblocks; eauto. i. clarify. *) *)
(* (*       * right. *) *)
(* (*         eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto. *) *)
(* (*         ii. subst. *) *)
(* (*         hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i. *) *)
(* (*         exploit mi_freeblocks; eauto. i. clarify. *) *)
(* (*   - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT. *) *)
(* (*     rewrite <- MEM_EQ; clear MEM_EQ. *) *)
(* (*     unfold malloc in *. *) *)
(* (*     apply some_injective in MALLOC. *) *)
(* (*     econs. *) *)
(* (*     + eapply Memory.Mem.alloc_right_inj; eauto. *) *)
(* (*     + i. apply mi_freeblocks. eauto. *) *)
(* (*     + ii. exploit mi_mappedblocks; eauto. i. *) *)
(* (*       eapply Memory.Mem.valid_block_alloc; eauto. *) *)
(* (*     + ii. exploit mi_no_overlap; eauto. *) *)
(* (*     + ii. exploit mi_representable; eauto. *) *)
(* (*   - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT. *) *)
(* (*     unfold mstore in *. des_ifs. *) *)
(* (*     (* exploit genericvalues_inject.mem_inj_mstore_aux; eauto. *) *) *)
    
(* (*     (* Memory.Mem.mem_inj *) *) *)
(* (*     (*   memory_sim.MoreMem.mem_inj *) *) *)
(* (*     admit. (* store - store *) *) *)
(* (*   - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT. *) *)
(* (*     unfold mstore in *. des_ifs. *) *)
(* (*     admit. (* store to private *) *) *)

(* (*   - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT. *) *)
(* (*     unfold free in *. des_ifs. *) *)
(* (*     eapply Memory.Mem.free_left_inject; eauto. *) *)
(* (*     eapply Memory.Mem.free_right_inject; eauto. *) *)
(* (*     admit. (* free - free *) *) *)
(* (*   - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT. *) *)
(* (*     eauto. *) *)
(* (* Admitted. *) *)

  

(*   exploit inject_mem_change; try exact INJECT_EVENT; eauto. intro MC_INJECT. *)

(*   Lemma mem_change_inject_invmem *)
(*         (MEM : InvMem.Rel.sem conf_src conf_tgt (Mem st0_src) (Mem st0_tgt) invmem0) *)
(*         (MC_INJECT: mem_change_inject conf_src conf_tgt invmem0 mc_src mc_tgt) *)
(*         (STATES_MC_SRC: states_mem_change conf_src mem0 mem1 mc_src) *)
(*         (STATES_MC_TGT: states_mem_change conf_tgt mem0 mem1 mc_tgt) *)

(*         (STATE_EQUIV_SRC : state_equiv_except_mem conf_src {| EC := EC st1_src; ECS := ECS st1_src; Mem := Mem st0_src |} st1_src mc) *)
(*         (STATE_EQUIV_TGT : state_equiv_except_mem conf_tgt {| EC := EC st1_tgt; ECS := ECS st1_tgt; Mem := Mem st0_tgt |} st1_tgt mc) *)
(*     : exists invmem1, *)
(*       <<ALLOC_INJECT: alloc_inject conf_src conf_tgt st1_src st1_tgt cmd_src cmd_tgt invmem1>> /\ *)
(*       <<MEM_INJ: memory_sim.MoreMem.mem_inj (InvMem.Rel.inject invmem1) (Mem st1_src) (Mem st1_tgt)>>.         *)
  
    
                                          
(*         mem_change_cmd_after *)


(*         (* Lemma step_equiv_except_mem *) *)
(* (*       conf st0 st1 evt *) *)
(* (*       cmd cmds *) *)
(* (*       invst0 invmem0 inv0 inv1 *) *)
(* (*       public gmax *) *)
(* (*       (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0) *) *)
(* (*       (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0) *) *)
(* (*       (NONCALL: Instruction.isCallInst cmd = false) *) *)
(* (*       (CMDS: CurCmds st0.(EC) = cmd :: cmds) *) *)
(* (*       (FORGET: inv_unary_forgot inv1 (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))) *) *)
(* (*       (STEP: sInsn conf st0 st1 evt) *) *)
(* (*   : exists mc, *) *)
(* (*     <<MEM_CH_REL: mem_change_cmd conf st0 mc cmd>> /\ *) *)
(* (*     <<STATE_EQUIV: state_equiv_except_mem conf (mkState st1.(EC) st1.(ECS) st0.(Mem)) st1 mc>>. *) *)
(* (* Proof. *) *)
(* (*   inv STEP; destruct cmd; inv CMDS; ss; *) *)
(* (*     try by esplits; eauto; econs; eauto; econs; eauto. *) *)
(* (*   - admit. (* malloc , should know newly allocated block is unique *) *) *)
(* (*   - admit. (* alloca *) *) *)
(* (* Admitted. *) *)

(* (* Lemma step_unique_preserved_mem *) *)
(* (*       conf st0 st1 evt *) *)
(* (*       cmd cmds inv0 *) *)
(* (*       (STATE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf (mkState st1.(EC) st1.(ECS) st0.(Mem))) *) *)
(* (*                                   inv0.(Invariant.unique)) *) *)
(* (*       (NONCALL: Instruction.isCallInst cmd = false) *) *)
(* (*       (CMDS: CurCmds st0.(EC) = cmd :: cmds) *) *)
(* (*       (STEP: sInsn conf st0 st1 evt) *) *)
(* (*       (UNIQUE_NOT_LEAKED: forall x (MEM:AtomSetImpl.mem x inv0.(Invariant.unique) = true), *) *)
(* (*                                  AtomSetImpl.mem x (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd)) = false) *) *)
(* (*   : unique_preserved_mem conf st1 inv0. *) *)
(* (* Proof. *) *)
(* (*   inv STEP; ss; *) *)
(* (*     try (inv CMDS; ss; *) *)
(* (*          ii; specialize_unique; eauto). *) *)
(* (*   { admit. (* load malloc -> undef *) } *) *)
(* (*   { admit. (* load after free: use Memory.Mem.load_free_2 maybe *) } *) *)
(* (*   { admit. (* load alloca *) } *) *)
(* (*   { admit. (* load after store *) } *) *)
(* (* Admitted. *) *)

(* (* Lemma mem_change_cmd_state_transition *) *)
(* (*       conf st0 st1 evt cmd cmds mc inv0 *) *)
(* (*       (CMD: CurCmds (EC st0) = cmd :: cmds) *) *)
(* (*       (NONCALL: Instruction.isCallInst cmd = false) *) *)
(* (*       (STEP: sInsn conf st0 st1 evt) *) *)
(* (*       (MEM_CH_REL: mem_change_cmd conf st0 mc cmd) *) *)
(* (*       (FORGET: inv_unary_forgot inv0 (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))) *) *)
(* (*   : mem_change_cmd_after conf {| EC := EC st1; ECS := ECS st1; Mem := Mem st0 |} mc cmd inv0. *) *)
(* (* Proof. *) *)
(* (*   destruct cmd; ss; *) *)
(* (*     inv STEP; ss; *) *)
(* (*       des; esplits; eauto. *) *)
(* (*   admit. (* easy *) *) *)
(* (* Admitted. *) *)


  
(* Admitted. *)

(* (* Lemma forget_memory_sound *) *)
(* (*       m_src conf_src st0_src st1_src mem_change_src cmd_src *) *)
(* (*       m_tgt conf_tgt st0_tgt st1_tgt mem_change_tgt cmd_tgt *) *)
(* (*       invst0 invmem0 inv0 *) *)
(* (*       (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt) *) *)
(* (*       (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0) *) *)
(* (*       (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0) *) *)
(* (*       (MEM_EQUIV_SRC: state_equiv_except_mem *) *)
(* (*                         conf_src *) *)
(* (*                         st0_src st1_src *) *)
(* (*                         mem_change_src) *) *)
(* (*       (MEM_EQUIV_TGT: state_equiv_except_mem *) *)
(* (*                         conf_tgt *) *)
(* (*                         st0_tgt st1_tgt *) *)
(* (*                         mem_change_tgt) *) *)
(* (*       (MEM_CHANGE_SRC: mem_change_cmd_after conf_src st0_src mem_change_src cmd_src inv0.(Invariant.src)) *) *)
(* (*       (MEM_CHANGE_TGT: mem_change_cmd_after conf_tgt st0_tgt mem_change_tgt cmd_tgt inv0.(Invariant.tgt)) *) *)
(* (*       (MEM_CHANGE_INJECT: mem_change_inject conf_src conf_tgt invmem0 mem_change_src mem_change_tgt) *) *)
(* (*       (UNIQUE_PRSV_SRC: unique_preserved_mem conf_src st1_src inv0.(Invariant.src)) *) *)
(* (*       (UNIQUE_PRSV_TGT: unique_preserved_mem conf_tgt st1_tgt inv0.(Invariant.tgt)) *) *)
(* (*   : *) *)
(* (*     exists invmem1, *) *)
(* (*       <<ALLOC_INJECT: alloc_inject conf_src conf_tgt st1_src st1_tgt cmd_src cmd_tgt invmem1>> /\ *) *)
(* (*       <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem1 *) *)
(* (*                                 (ForgetMemory.t (Cmd.get_def_memory cmd_src) (Cmd.get_def_memory cmd_tgt) inv0) >> /\ *) *)
(* (*       <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\ *) *)
(* (*       <<MEMLE: InvMem.Rel.le invmem0 invmem1>>. *) *)
(* (* Proof. *) *)
(* (*   exploit mem_change_inject_no_private_parent_src; eauto. intro NO_PRIVATE_PARENT_SRC. *) *)
(* (*   exploit mem_change_inject_no_private_parent_tgt; eauto. intro NO_PRIVATE_PARENT_TGT. *) *)
(* (*   inv STATE. inv MEM. *) *)

(* (*   destruct (Cmd.get_def_memory cmd_src) eqn:DEF_MEM_SRC; *) *)
(* (*     destruct (Cmd.get_def_memory cmd_tgt) eqn:DEF_MEM_TGT. *) *)
(* (*   - hexploit forget_memory_unary_sound_with_def_memory; try exact SRC; try exact DEF_MEM_SRC; eauto. i. des. *) *)
(* (*     hexploit forget_memory_unary_sound_with_def_memory; try exact TGT; try exact DEF_MEM_TGT; eauto. i. des. *) *)
(* (*     hexploit forget_memory_maydiff_preserved; try exact MAYDIFF; eauto. i. des. *) *)
(* (*     inv MEM_EQUIV_SRC. inv MEM_EQUIV_TGT. *) *)
(* (*     hexploit mem_inject_change; try exact MEM_CHANGE_INJECT; eauto. i. *) *)
(* (*     esplits; econs; eauto. *) *)
(* (*   - hexploit forget_memory_unary_sound_with_def_memory; try exact SRC; try exact DEF_MEM_SRC; eauto. i. des. *) *)
(* (*     hexploit forget_memory_unary_sound_without_def_memory; try exact TGT; try exact DEF_MEM_TGT; eauto. i. des. *) *)
(* (*     hexploit forget_memory_maydiff_preserved; try exact MAYDIFF; eauto. i. des. *) *)
(* (*     inv MEM_EQUIV_SRC. inv MEM_EQUIV_TGT. *) *)
(* (*     hexploit mem_inject_change; try exact MEM_CHANGE_INJECT; eauto. i. *) *)
(* (*     esplits; econs; eauto. *) *)
(* (*   - hexploit forget_memory_unary_sound_without_def_memory; try exact SRC; try exact DEF_MEM_SRC; eauto. i. des. *) *)
(* (*     hexploit forget_memory_unary_sound_with_def_memory; try exact TGT; try exact DEF_MEM_TGT; eauto. i. des. *) *)
(* (*     hexploit forget_memory_maydiff_preserved; try exact MAYDIFF; eauto. i. des. *) *)
(* (*     inv MEM_EQUIV_SRC. inv MEM_EQUIV_TGT. *) *)
(* (*     hexploit mem_inject_change; try exact MEM_CHANGE_INJECT; eauto. i. *) *)
(* (*     esplits; econs; eauto. *) *)
(* (*   - hexploit forget_memory_unary_sound_without_def_memory; try exact SRC; try exact DEF_MEM_SRC; eauto. i. des. *) *)
(* (*     hexploit forget_memory_unary_sound_without_def_memory; try exact TGT; try exact DEF_MEM_TGT; eauto. i. des. *) *)
(* (*     hexploit forget_memory_maydiff_preserved; try exact MAYDIFF; eauto. i. des. *) *)
(* (*     inv MEM_EQUIV_SRC. inv MEM_EQUIV_TGT. *) *)
(* (*     hexploit mem_inject_change; try exact MEM_CHANGE_INJECT; eauto. i. *) *)
(* (*     esplits; econs; eauto. *) *)
(* (* Qed. *) *)
