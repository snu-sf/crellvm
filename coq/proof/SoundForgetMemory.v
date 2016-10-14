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

(* TODO: move *)
Lemma some_injective A (a b:A):
  Some a = Some b -> a = b.
Proof.
  congruence.
Qed.

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

Definition is_mem_change_updating (mc:mem_change): option GenericValue :=
  match mc with
  | mem_change_store ptr _ _ _
  | mem_change_free ptr => Some ptr
  | _ => None
  end.

Definition mem_change_no_private_parent conf mc pp: Prop :=
  forall ptr b ofs
         (UPDATE: is_mem_change_updating mc = Some ptr)
         (PTR: GV2ptr conf.(CurTargetData) conf.(CurTargetData).(getPointerSize) ptr =
                 Some (Values.Vptr b ofs)),
    ~ In b pp.

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
  inv INJECT; try econs; ii; ss; inv UPDATE.
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
  inv SEM. inv TGT.
  inv INJECT; try econs; ii; ss; inv UPDATE;
    exploit PRIVATE_PARENT; eauto; i; des;
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
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
  : InvState.Unary.sem conf st1 invst0 invmem0 inv0.
Proof.
  inv STATE.
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
    try (by inv CMD;
         esplits; ss; econs; eauto);
    try (by inv CMD;
         esplits; ss; [des_ifs | esplits | econs]; eauto).
  admit. (* not malloc *)
Admitted.

Ltac exploit_inject_value :=
  repeat (match goal with
       | [H1: Invariant.inject_value ?inv ?vt1 ?vt2 = true |- _] =>
         exploit InvState.Rel.inject_value_spec; try exact H1; eauto; clear H1
       end;
       (try by
           match goal with
           | [H: getOperandValue (CurTargetData ?conf) ?v (Locals (EC ?st)) (Globals ?conf) = Some ?gv1 |-
              InvState.Unary.sem_valueT ?conf ?st ?invst (ValueT.lift Tag.physical ?v) = Some ?gv2] =>
             destruct v; [ss; unfold IdT.lift; solve_sem_idT; eauto | ss]
           end); i; des).

Ltac inv_conf :=
  match goal with
  | [H: InvState.valid_conf _ _ ?conf_src ?conf_tgt |- _] =>
    let TD := fresh in
    let GL := fresh in
    destruct H as [[TD GL]]; rewrite TD in *; rewrite GL in *
  end.

Lemma inject_mem_change
      m_src conf_src cmd_src mc_src st0_src
      m_tgt conf_tgt cmd_tgt mc_tgt st0_tgt
      inv0 invmem0 invst0
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM : InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (INJECT_EVENT : postcond_cmd_inject_event cmd_src cmd_tgt inv0)
      (MC_SRC : mem_change_of_cmd conf_src cmd_src st0_src.(EC).(Locals) = Some mc_src)
      (MC_TGT : mem_change_of_cmd conf_tgt cmd_tgt st0_tgt.(EC).(Locals) = Some mc_tgt)
  : mem_change_inject conf_src conf_tgt invmem0 mc_src mc_tgt.
Proof.
  destruct cmd_src; destruct cmd_tgt; ss; clarify;
    (try by simtac; econs); (* cases including none *)
    try by simtac;
    unfold is_true in *;
    repeat (des_bool; des);
    inject_clarify;
    exploit_inject_value;
    inv_conf;
    inject_clarify;
    econs; eauto.
  unfold Invariant.is_private in *. des_ifs.
  destruct x as [t x]; unfold ValueT.lift in *. des_ifs.
  inv STATE. inv SRC.
  exploit PRIVATE.
  { apply IdTSet.mem_2; eauto. }
  { inv_conf. inject_clarify. }
  i. des_ifs.
  econs; eauto.
Qed.

(* lemmas for malloc *)
Lemma malloc_result
      TD mem mem' sz gn a mb
      (MALLOC: malloc TD mem sz gn a = Some (mem', mb))
  : <<ALLOC_BLOCK: mb = mem.(Memory.Mem.nextblock)>> /\
    <<NEXT_BLOCK: mem'.(Memory.Mem.nextblock) = Pos.succ mem.(Memory.Mem.nextblock)>>
.
Proof.
  unfold malloc in *.
  des_ifs.
Qed.

Lemma valid_access_malloc_same
      TD mem0 mem1 bsz gn a mb p chunk ofs
      (MALLOC: malloc TD mem0 bsz gn a = Some (mem1, mb))
      (OFS: 0 <= ofs /\
               ofs + Memdata.size_chunk chunk <=
               Size.to_Z bsz *
               (get_or_else (GV2int TD Size.ThirtyTwo gn) 0) /\
               (Memdata.align_chunk chunk | ofs))
  : Memory.Mem.valid_access mem1 chunk mb ofs p.
Proof.
  unfold malloc in *.
  des_ifs; des; ss.
  - eapply Memory.Mem.valid_access_implies;
      try apply Memtype.perm_F_any.
    eapply Memory.Mem.valid_access_alloc_same; eauto.
  - rewrite Z.mul_0_r in *.
    specialize (Memdata.size_chunk_pos chunk). i.
    omega.
Qed.

Lemma valid_access_malloc_inv
      TD mem0 mem1 bsz gn a b mb p chunk ofs
      (MALLOC: malloc TD mem0 bsz gn a = Some (mem1, mb))
      (VALID: Memory.Mem.valid_access mem1 chunk b ofs p)
  : if Values.eq_block b mb
    then 0 <= ofs /\
         ofs + Memdata.size_chunk chunk <=
         Size.to_Z bsz * get_or_else (GV2int TD Size.ThirtyTwo gn) 0 /\
         (Memdata.align_chunk chunk | ofs)
    else Memory.Mem.valid_access mem0 chunk b ofs p.
Proof.
  unfold malloc in *.
  exploit Memory.Mem.valid_access_alloc_inv; eauto.
  des_ifs. ss. rewrite Z.mul_0_r in *. eauto.
Qed.

Lemma valid_access_malloc_other
      TD mem0 bsz gn a mem1 mb b' ofs p chunk
      (MALLOC: malloc TD mem0 bsz gn a = Some (mem1, mb))
      (VALID: Memory.Mem.valid_access mem0 chunk b' ofs p)
  : Memory.Mem.valid_access mem1 chunk b' ofs p.
Proof.
  unfold malloc in *.
  apply some_injective in MALLOC.
  eapply Memory.Mem.valid_access_alloc_other; eauto.
Qed.

Ltac clarify_malloc :=
  unfold malloc in *;
  repeat match goal with
         | [H: Some (Memory.Mem.alloc _ _ _) = Some (_, _) |- _] =>
           apply some_injective in H
         | [H: Some (_, _) = Some (Memory.Mem.alloc _ _ _) |- _] =>
           apply some_injective in H
         end.

Lemma malloc_contents_same
      TD mem0 mem1 gsz gn a
      mb ofs
      (MALLOC: malloc TD mem0 gsz gn a = Some (mem1, mb))
  : Maps.ZMap.get ofs (Maps.PMap.get mb (Memory.Mem.mem_contents mem1)) = Memdata.Undef.
Proof.
  clarify_malloc.
  erewrite <- Memory.Mem.alloc_mem_contents; eauto.
  rewrite (Memory.Mem.alloc_result _ _ _ _ _ MALLOC).
  rewrite Maps.PMap.gss.
  apply Maps.ZMap.gi.
Qed.

Lemma malloc_contents_other
      TD mem0 mem1 gsz gn a
      mb b ofs
      (MALLOC: malloc TD mem0 gsz gn a = Some (mem1, mb))
      (DIFF: b <> mb)
  : Maps.ZMap.get ofs (Maps.PMap.get b (Memory.Mem.mem_contents mem1)) =
    Maps.ZMap.get ofs (Maps.PMap.get b (Memory.Mem.mem_contents mem0)).
Proof.
  clarify_malloc.
  erewrite <- Memory.Mem.alloc_mem_contents; eauto.
  rewrite (Memory.Mem.alloc_result _ _ _ _ _ MALLOC) in DIFF.
  rewrite Maps.PMap.gsspec.
  des_ifs.
Qed.

(* end of malloc *)

Lemma invmem_unary_src_alloc_preserved
      conf invmem0 mem0 mem1
      public gmax mb
      gsz gn a
      (SRC : InvMem.Unary.sem conf gmax public mem0 invmem0)
      (MALLOC : Some (mem1, mb) = malloc (CurTargetData conf) mem0 gsz gn a)
  : InvMem.Unary.sem conf gmax public mem1 invmem0.
Proof.
  exploit malloc_result; eauto. i. des.
  inv SRC.
  econs; eauto.
  - i. exploit PRIVATE; eauto. i. des.
    split; eauto.
    eapply Pos.lt_trans; eauto.
    rewrite NEXT_BLOCK. apply Plt_succ'.
  - i. exploit PRIVATE_PARENT; eauto. i. des.
    split; eauto.
    eapply Pos.lt_trans; eauto.
    rewrite NEXT_BLOCK. apply Plt_succ'.
  - i. exploit MEM_PARENT; eauto. i.
    rewrite x.
    admit. (* We can deduce b <> (mem0.nextblock) so mload_aux is preserved *)
Admitted.

(* TODO: simplify proof script *)

Lemma inject_invmem
      m_src conf_src st0_src st1_src cmd_src cmds_src evt_src
      m_tgt conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt evt_tgt
      invst0 invmem0 inv0 inv1
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
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
  hexploit step_mem_change; try (inv STATE; exact SRC); eauto. intro MCS. destruct MCS as [mc_src [MC_SOME_SRC [MC_AFTER_SRC STATE_EQUIV_SRC]]]. des.
  hexploit step_mem_change; try (inv STATE; exact TGT); eauto. intro MCS. destruct MCS as [mc_tgt [MC_SOME_TGT [MC_AFTER_TGT STATE_EQUIV_TGT]]]. des.

  exploit inject_mem_change; eauto. intro MC_INJECT.

  inv MC_INJECT.
  - (* alloc - alloc *)
    inv STEP_SRC; inv CMD_SRC; ss; try by des; congruence.
    rename Mem0 into mem0_src. rename Mem' into mem1_src. rename mb into mb_src.
    match goal with
    | [H: malloc _ _ _ _ _ = _ |- _] => rename H into MALLOC_SRC
    end.
    inv STEP_TGT; inv CMD_TGT; ss; try by des; congruence.
    rename Mem0 into mem0_tgt. rename Mem' into mem1_tgt. rename mb into mb_tgt.
    match goal with
    | [H: malloc _ _ _ _ _ = _ |- _] => rename H into MALLOC_TGT
    end.
    eexists.
    instantiate (1:= InvMem.Rel.mk _ _ _ (fun b => if Values.eq_block b mb_src then Some (mb_tgt, 0%Z) else invmem0.(InvMem.Rel.inject) b)).
    esplits.
    + (* alloc_inject *)
      ii. ss.
      inv ALLOCA_SRC. inv ALLOCA_TGT.
      esplits; try apply lookupAL_updateAddAL_eq; ss.
      destruct (Values.eq_block mb_src mb_src); ss.
    + (* InvMem sem *)
      inv MEM; ss.
      econs; ss; eauto.
      { (* SRC *)
        inv SRC.
        hexploit (@malloc_result TD mem0_src); eauto. i. des.
        econs; eauto.
        { 
          i. exploit PRIVATE; eauto. i.
          des.
          destruct (Values.eq_block b mb_src) eqn:EQ_MB.
          - subst.
            exploit Pos.lt_irrefl; eauto. contradiction.
          - split.
            + ii.
              match goal with
              | [H: ~ InvMem.Rel.public_src _ _ |- False] =>
                apply H
              end.
              unfold InvMem.Rel.public_src in *. rewrite EQ_MB in *. eauto.
            + eapply Pos.lt_trans; eauto.
              apply Pos.le_succ_l. rewrite NEXT_BLOCK. apply Pos.le_refl.
        }
        { i. exploit PRIVATE_PARENT; eauto. i. des.
          destruct (Values.eq_block b mb_src) eqn:EQ_MB.
          - subst.
            exploit Pos.lt_irrefl; eauto. contradiction.
          - split.
            + ii. apply x.
              unfold InvMem.Rel.public_src in *. rewrite EQ_MB in *. eauto.
            + eapply Pos.lt_trans; eauto.
              apply Pos.le_succ_l. rewrite NEXT_BLOCK. apply Pos.le_refl.
        }
        { i. exploit MEM_PARENT; eauto. i.
          match goal with
          | [H: mload_aux (InvMem.Unary.mem_parent _) _ b _ = _ |- _] =>
            rewrite H
          end.
          exploit PRIVATE_PARENT; eauto. i. des.
          admit. (* b is less than Mem0's nextblock, and Mem0 -alloc-> Mem' so mload_aux is preserved *)
        }
      }
      { (* TGT *)
        inv TGT.
        hexploit (@malloc_result TD0 mem0_tgt); eauto. i. des.
        econs; eauto.
        { 
          i. exploit PRIVATE; eauto. i.
          des.
          split.
          { ii.
            match goal with
            | [H: ~ InvMem.Rel.public_tgt _ _ |- False] =>
              apply H
            end.
            unfold InvMem.Rel.public_tgt in *. des.
            destruct (Values.eq_block b_src mb_src).
            { clarify. exfalso. eapply Pos.lt_irrefl; eauto. }
            { esplits; eauto. }
          }
          { eapply Pos.lt_trans; eauto.
            apply Pos.le_succ_l. rewrite NEXT_BLOCK. apply Pos.le_refl.
          }
        }
        { i. exploit PRIVATE_PARENT; eauto. i. des.
          split.
          { ii.
            match goal with
            | [H: ~ InvMem.Rel.public_tgt _ _ |- False] =>
              apply H
            end.
            unfold InvMem.Rel.public_tgt in *. des.
            destruct (Values.eq_block b_src mb_src).
            { clarify. exfalso. eapply Pos.lt_irrefl; eauto. }
            { esplits; eauto. }
          }
          { eapply Pos.lt_trans; eauto.
            apply Pos.le_succ_l. rewrite NEXT_BLOCK. apply Pos.le_refl.
          }
        }
        { i. exploit MEM_PARENT; eauto. i.
          match goal with
          | [H: mload_aux (InvMem.Unary.mem_parent _) _ b _ = _ |- _] =>
            rewrite H
          end.
          exploit PRIVATE_PARENT; eauto. i. des.
          admit. (* b is less than Mem0's nextblock, and Mem0 -alloc-> Mem' so mload_aux is preserved *)
        }
      }
      { (* inject *)
        inv INJECT.
        unfold is_true in *.
        repeat rewrite andb_true_iff in INJECT_EVENT.
        destruct INJECT_EVENT as [[[ID_EQ TYP_EQ] INJECT_VALUE] DEC_EQ].
        unfold proj_sumbool in *. des_ifs.
        econs.
        { (* mi_access *)
          ii. exploit valid_access_malloc_inv; try exact MALLOC_SRC; eauto. i.
          destruct (Values.eq_block b1 mb_src).
          { clarify.
            eapply valid_access_malloc_same; eauto.
            admit. (* gn >= gn2 *)
          }
          { exploit mi_access; eauto.
            eapply valid_access_malloc_other; eauto.
          }
        }
        { (* mi_memval *)
          i. destruct (Values.eq_block b1 mb_src).
          - clarify.
            rewrite Z.add_0_r.
            erewrite malloc_contents_same; eauto.
            erewrite malloc_contents_same; eauto.
            apply memory_sim.MoreMem.memval_inject_undef.
          - eapply memory_sim.MoreMem.memval_inject_incr.
            { assert (DIFF_BLK_TGT: b2 <> mb_tgt).
              { exploit genericvalues_inject.Hmap2; eauto. i.
                exploit (Memory.Mem.alloc_result mem0_tgt); eauto.
                { clarify_malloc. eauto. }
                ii. subst.
                eapply Pos.lt_irrefl. eauto.
              }
              eapply malloc_contents_other in DIFF_BLK_TGT; eauto.
              rewrite DIFF_BLK_TGT.
              erewrite malloc_contents_other; eauto.
              apply mi_memval; eauto.
              exploit Memory.Mem.perm_alloc_inv.
              { clarify_malloc. exact MALLOC_SRC. }
              { eauto. }
              i. des_ifs.
            }
            { ii.
              destruct (Values.eq_block b mb_src).
              { subst. exfalso.
                exploit genericvalues_inject.Hmap1; eauto.
                { instantiate (1:=mb_src).
                  clarify_malloc.
                  exploit (Memory.Mem.alloc_result mem0_src); eauto. i.
                  subst. apply Pos.le_ge. apply Pos.le_refl. }
                i. congruence.
              }
              eauto.
            }
        }
      }
      { (* wf_sb_mi *)
        inv WF.
        exploit malloc_result; try exact MALLOC_SRC. intros [ALLOC_BLOCK_SRC NEXT_BLOCK_SRC]. des.
        exploit malloc_result; try exact MALLOC_TGT. intros [ALLOC_BLOCK_TGT NEXT_BLOCK_TGT]. des.
        econs.
        - (* no_overlap *)
          ii.
          destruct (Values.eq_block b1 mb_src);
            destruct (Values.eq_block b2 mb_src); clarify.
          + exploit Hmap2; eauto. i.
            eapply Pos.lt_irrefl; eauto.
          + exploit Hmap2; eauto. i.
            eapply Pos.lt_irrefl; eauto.
          + eapply Hno_overlap with (b1:=b1) (b2:=b2); eauto.
        - (* destruct (Values.eq_block Memory.Mem.nullptr mb_src). *)
          (* - subst. *)
          (*   hexploit Memory.Mem.alloc_result. *)
          (*   { clarify_malloc. exact MALLOC_SRC. } *)
          (*   i. *)
          (* - done. *)
          admit. (* nullptr will be removed *)
        - (* Hmap1 *)
          i. destruct (Values.eq_block b mb_src).
          + subst.
            rewrite NEXT_BLOCK_SRC in *.
            exfalso.
            eapply Pos.lt_nle.
            { apply Plt_succ'. }
            apply Pos.ge_le.
            eauto.
          + apply Hmap1.
            apply Pos.le_ge.
            eapply Pos.le_trans.
            { apply Ple_succ. }
            { rewrite NEXT_BLOCK_SRC in *.
              apply Pos.ge_le. eauto.
            }
        - (* Hmap2 *)
          i. destruct (Values.eq_block b1 mb_src).
          + clarify.
            subst. rewrite NEXT_BLOCK_TGT in *.
            apply Plt_succ'.
          + exploit Hmap2; eauto. i.
            eapply Pos.lt_trans; eauto.
            rewrite NEXT_BLOCK_TGT.
            apply Plt_succ'.
        - (* mi_freeblocks *)
          intros b NOT_VALID_BLOCK.
          destruct (Values.eq_block b mb_src).
          + subst.
            exfalso.
            apply NOT_VALID_BLOCK.
            unfold Memory.Mem.valid_block.
            rewrite NEXT_BLOCK_SRC.
            eapply Plt_succ'.
          + apply mi_freeblocks. intros VALID_BLOCK.
            apply NOT_VALID_BLOCK.
            unfold Memory.Mem.valid_block in *.
            rewrite NEXT_BLOCK_SRC.
            eapply Pos.lt_trans; eauto.
            apply Plt_succ'.
        - (* mi_mappedblocks *)
          i. destruct (Values.eq_block b mb_src).
          + clarify.
            unfold Memory.Mem.valid_block in *.
            rewrite NEXT_BLOCK_TGT.
            apply Plt_succ'.
          + eapply Memory.Mem.valid_block_alloc.
            { clarify_malloc. eauto. }
            eapply mi_mappedblocks; eauto.
        - (* mi_range_blocks *)
          ii. destruct (Values.eq_block b mb_src).
          + subst. clarify.
          + eapply mi_range_block; eauto.
        - (* mi_bounds *)
          ii. destruct (Values.eq_block b mb_src).
          + clarify.
            erewrite Memory.Mem.bounds_alloc_same; cycle 1.
            { clarify_malloc. exact MALLOC_SRC. }
            erewrite Memory.Mem.bounds_alloc_same; cycle 1.
            { clarify_malloc. exact MALLOC_TGT. }
            apply injective_projections; ss.
            admit. (* GV2int returns 0 => malloc 0-sized space *)
          + erewrite Memory.Mem.bounds_alloc_other with (b':=b); eauto; cycle 1.
            { clarify_malloc. exact MALLOC_SRC. }
            assert (NEQ_BLK_TGT: b' <> mb_tgt).
            { exploit Hmap2; eauto. ii. subst.
              eapply Plt_irrefl. eauto. }
            erewrite Memory.Mem.bounds_alloc_other with (b':=b'); try exact NEQ_BLK_TGT; cycle 1.
            { clarify_malloc. exact MALLOC_TGT. }
            eapply mi_bounds; eauto.
        - (* mi_globals *)
          i. destruct (Values.eq_block b mb_src).
          + subst.
            exploit mi_globals; eauto. i.
            exploit Hmap1.
            { apply Pos.le_ge.
              apply Pos.le_refl.
            }
            i. congruence.
          + exploit mi_globals; eauto.
      }
    + (* le *)
      econs; try (econs; ss).
      (* incr *)
      ii. ss.
      exploit malloc_result; try exact MALLOC_SRC. intros [ALLOC_BLOCK_SRC NEXT_BLOCK_SRC]. des.
      exploit malloc_result; try exact MALLOC_TGT. intros [ALLOC_BLOCK_TGT NEXT_BLOCK_TGT]. des.
      destruct (Values.eq_block b mb_src); eauto.
      subst.
      inv MEM. inv WF.
      exploit Hmap1.
      { apply Pos.le_ge. apply Pos.le_refl. }
      i. congruence.
  - (* alloc - none *)
    esplits; eauto.
    + ii.
      Ltac solve_alloc_inject :=
        match goal with
        | [ALLOCA: ?cmd = insn_alloca _ _ _ _,
                 MC_SOME: mem_change_of_cmd _ ?cmd _ = Some mem_change_none |- _] =>
          rewrite ALLOCA in MC_SOME; ss; des_ifs
        end.
      solve_alloc_inject.
    + inv MEM.
      inv STATE_EQUIV_TGT. rewrite <- MEM_EQ in *.
      inv STATE_EQUIV_SRC.
      econs; eauto.
      * eapply invmem_unary_src_alloc_preserved; eauto.
      * inv INJECT.
        econs.
        { (* mi-access *)
          i. exploit mi_access; eauto.
          (* we can deduce b1 is less than nextblock *)
          (* then valid_access_malloc_inv trivially solves the problem *)
          admit.
        }
        { (* mi_memval *)
          i. exploit mi_memval; eauto.
          { (* use Memory.Mem.perm_alloc_inv *)
            admit. }
          i. (* b1 is less then nextblock *)
          exploit malloc_contents_other; eauto.
          { admit. }
          intro CONTENTS.
          rewrite CONTENTS. eauto.
        }
      * inv WF.
        econs; eauto.
        { (* Hmap1 *)
          (* b >= nextblock mem1 >= nextblock mem0 *)
          admit. }
        { (* same *)
          admit. }
        { (* b >= nextblock, so bounds preserved *)
          (* Memory.Mem.bounds_alloc *)
          admit. }
    + reflexivity.
  - (* none - alloc *)
    admit.
  - (* store - store *)
    admit.
  - (* store - none *)
    admit.
  - (* free - free *)
    admit.
  - (* none - none *)
    admit.
Admitted.

(* We use this as an axiom for now *)
Lemma mstore_noalias_mload
      conf mem0 mem1 TD
      sptr sty gv sa
      lptr lty la
      (STORE: Some mem1 = mstore TD mem0 sptr sty gv sa)
      (NOALIAS: InvState.Unary.sem_noalias conf sptr lptr sty lty)
  : mload TD mem1 lptr lty la = mload TD mem0 lptr lty la.
Proof.
Admitted.

Lemma diffblock_comm
      conf gv1 gv2
      (DIFFBLOCK: InvState.Unary.sem_diffblock conf gv1 gv2)
  : InvState.Unary.sem_diffblock conf gv2 gv1.
Proof.
  unfold InvState.Unary.sem_diffblock in *. des_ifs. eauto.
Qed.

Lemma noalias_comm
      conf gv1 gv2 ty1 ty2
      (NOALIAS: InvState.Unary.sem_noalias conf gv1 gv2 ty1 ty2)
  : InvState.Unary.sem_noalias conf gv2 gv1 ty2 ty1.
Proof.
  unfold InvState.Unary.sem_noalias in *. des_ifs. eauto.
Qed.  

Lemma diffblock_implies_noalias
      conf gv1 gv2 ty1 ty2
      (DIFFBLOCK: InvState.Unary.sem_diffblock conf gv1 gv2)
  : InvState.Unary.sem_noalias conf gv1 gv2 ty1 ty2.
Proof.
  unfold InvState.Unary.sem_diffblock, InvState.Unary.sem_noalias in *. des_ifs.
Qed.

(* TODO: prove this after adding unique<>globals*)
Lemma const_unique_diffblock
      conf c gv_c
      st1 x_inv gv_inv val
      (FORGET_PTR : const2GV (CurTargetData conf) (Globals conf) c = Some gv_c)
      (VAL : lookupAL GenericValue (Locals (EC st1)) x_inv = Some gv_inv)
      (XX : forall (gid : atom) (gptr : GenericValue),
          lookupAL GenericValue (Globals conf) gid = Some gptr -> InvState.Unary.sem_diffblock conf val gptr)
  : InvState.Unary.sem_diffblock conf gv_c gv_inv.
Proof.
(* destruct c. *)
(* - unfold InvState.Unary.sem_diffblock. *)
(*   des_ifs. *)
(*   unfold const2GV in *. des_ifs. *)
(*   unfold _const2GV in *. des_ifs. *)
(*   unfold zeroconst2GV in *. des_ifs. ss. *)
(*   unfold zeroconst2GV_aux in *. *)
(*   unfold GV2ptr in *. des_ifs. *)
Admitted.

Lemma is_diffblock_sem
      conf st invst invmem inv
      v1 ty1 v2 ty2 gv1 gv2
      (STATE : InvState.Unary.sem conf st invst invmem inv)
      (IS_DIFFBLOCK : Invariant.is_diffblock inv (v1, ty1) (v2, ty2) = true)
      (VAL1 : InvState.Unary.sem_valueT conf st invst v1 = Some gv1)
      (VAL2 : InvState.Unary.sem_valueT conf st invst v2 = Some gv2)
  : InvState.Unary.sem_diffblock conf gv1 gv2.
Proof.
  inv STATE.
  destruct NOALIAS as [DIFFBLOCK NOALIAS].
  unfold Invariant.is_diffblock in *.
  unfold flip in *.
  apply ValueTPairSetFacts.exists_iff in IS_DIFFBLOCK; try by solve_compat_bool.
  inv IS_DIFFBLOCK.
  destruct x as [p1 p2].
  des. des_bool. des.
  - des_bool. des. ss.
    unfold proj_sumbool in *; des_ifs.
    rewrite ValueTPairSetFacts.mem_iff in *.
    exploit DIFFBLOCK; eauto.
  - des_bool. des. ss.
    unfold proj_sumbool in *; des_ifs.
    rewrite ValueTPairSetFacts.mem_iff in *.
    exploit DIFFBLOCK; eauto.
    apply diffblock_comm.
Qed.

Lemma is_noalias_sem
      conf st invst invmem inv
      v1 ty1 v2 ty2 gv1 gv2
      (STATE : InvState.Unary.sem conf st invst invmem inv)
      (IS_NOALIAS : Invariant.is_noalias inv (v1, ty1) (v2, ty2) = true)
      (VAL1 : InvState.Unary.sem_valueT conf st invst v1 = Some gv1)
      (VAL2 : InvState.Unary.sem_valueT conf st invst v2 = Some gv2)
  : InvState.Unary.sem_noalias conf gv1 gv2 ty1 ty2.
Proof.
  inv STATE.
  destruct NOALIAS as [DIFFBLOCK NOALIAS].
  unfold Invariant.is_noalias in *.
  unfold flip in *.
  apply PtrPairSetFacts.exists_iff in IS_NOALIAS; try by solve_compat_bool.
  inv IS_NOALIAS.
  destruct x as [p1 p2].
  Opaque PtrSetFacts.eq_dec.
  unfold proj_sumbool in *.
  des. des_bool. des.
  - des_bool. des. ss. des_ifs.
    rewrite PtrPairSetFacts.mem_iff in *.
    exploit NOALIAS; subst; eauto.
  - des_bool. des. ss. des_ifs.
    rewrite PtrPairSetFacts.mem_iff in *.
    exploit NOALIAS; subst; eauto.
    apply noalias_comm.
Qed.

(* TODO: simplify proof script *)
Lemma forget_memory_is_noalias_expr
      conf st1 invst0 invmem0 inv1 mem0
      vt_inv ty_inv gv_inv
      v_forget ty_forget gv_forget
      (STATE : InvState.Unary.sem conf (mkState st1.(EC) st1.(ECS) mem0) invst0 invmem0 inv1)
      (NOALIAS_PTR: ForgetMemory.is_noalias_Ptr inv1 (ValueT.lift Tag.physical v_forget, ty_forget) (vt_inv, ty_inv) = true)
      (FORGET_PTR: getOperandValue (CurTargetData conf) v_forget (Locals (EC st1)) (Globals conf) = Some gv_forget)
      (INV_PTR: InvState.Unary.sem_valueT conf st1 invst0 vt_inv = Some gv_inv)
  : InvState.Unary.sem_noalias conf gv_forget gv_inv ty_forget ty_inv.
Proof.
  unfold ForgetMemory.is_noalias_Ptr in *.
  do 4 (des_bool; des).
  - rename NOALIAS_PTR0 into DIFFBLOCK_FROM_UNIQUE.
    des_bool. des. des_bool.
    rename NOALIAS_PTR0 into INV_UNIQUE.
    unfold proj_sumbool in *. des_ifs. ss.

    unfold Invariant.is_unique_ptr in *.
    unfold Invariant.is_unique_value in *.
    unfold proj_sumbool in *.
    ss. des_ifs. des_bool. des.
    destruct x as [[] x_inv]; ss.

    inv STATE.
    exploit UNIQUE; eauto.
    { apply AtomSetFacts.mem_iff; eauto. }
    intro UNIQUE_X. inv UNIQUE_X.

    unfold Invariant.values_diffblock_from_unique in *.
    destruct v_forget as [x_forget| c_forget]; ss.
    + assert (IDS_NEQ: x_forget <> x_inv).
      { unfold IdT.lift in *.
        match goal with
        | [H: _ <> _ |- _] =>
          ii; subst; apply H; reflexivity
        end. }
      apply diffblock_implies_noalias.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      apply diffblock_comm.
      
      eapply LOCALS; eauto.
    + assert (XX:
                forall gid gptr,
                  lookupAL _ conf.(Globals) gid = Some gptr ->
                  InvState.Unary.sem_diffblock conf val gptr).
      { admit. (* sem_unique seems to have to guarantee this *) }
      apply diffblock_implies_noalias.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      eapply const_unique_diffblock; eauto.
  - rename NOALIAS_PTR0 into DIFFBLOCK_FROM_UNIQUE.
    des_bool. des. des_bool.
    rename NOALIAS_PTR0 into INV_UNIQUE.
    unfold proj_sumbool in *. des_ifs. ss.

    unfold Invariant.is_unique_ptr in *.
    unfold Invariant.is_unique_value in *.
    unfold proj_sumbool in *.
    ss. des_ifs. des_bool. des.

    destruct x as [[] x_forget]; ss.
    destruct v_forget; ss.
    clarify.

    inv STATE.
    exploit UNIQUE; eauto.
    { apply AtomSetFacts.mem_iff; eauto. }
    intro UNIQUE_X. inv UNIQUE_X.

    unfold Invariant.values_diffblock_from_unique in *.
    destruct vt_inv as [[[] x_inv]| c_inv]; ss.
    + assert (IDS_NEQ: x_forget <> x_inv).
      { unfold IdT.lift in *.
        match goal with
        | [H: _ <> _ |- _] =>
          ii; subst; apply H; reflexivity
        end. }
      apply diffblock_implies_noalias.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      
      eapply LOCALS; eauto.
    + assert (XX:
                forall gid gptr,
                  lookupAL _ conf.(Globals) gid = Some gptr ->
                  InvState.Unary.sem_diffblock conf val gptr).
      { admit. (* sem_unique seems to have to guarantee this *) }
      apply diffblock_implies_noalias.
      apply diffblock_comm.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      eapply const_unique_diffblock; eauto.
  - exploit is_noalias_sem.
    { eauto. }
    { eauto. }
    { eauto. }
    { unfold ValueT.lift. des_ifs; eauto. }
    i. apply noalias_comm. eauto.
  - exploit is_diffblock_sem.
    { eauto. }
    { eauto. }
    { eauto. }
    { destruct v_forget as [x_forget|c_forget]; eauto. }
    i. apply diffblock_implies_noalias.
    apply diffblock_comm. eauto.
Admitted.

Lemma forget_memory_is_noalias_exprpair
      conf st1 invst0 invmem0 inv1 mem0
      p a e2
      vt_inv ty_inv gv_inv
      v_forget ty_forget gv_forget
      (STATE : InvState.Unary.sem conf (mkState st1.(EC) st1.(ECS) mem0) invst0 invmem0 inv1)
      (PAIR : p = (Expr.load vt_inv ty_inv a, e2) \/ p = (e2, Expr.load vt_inv ty_inv a))
      (FORGET_MEMORY_IN : ExprPairSet.In p (Invariant.lessdef inv1))
      (FORGET_MEMORY_NOALIAS : ForgetMemory.is_noalias_ExprPair inv1 (ValueT.lift Tag.physical v_forget, ty_forget) p = true)
      (FORGET_PTR: getOperandValue (CurTargetData conf) v_forget (Locals (EC st1)) (Globals conf) = Some gv_forget)
      (INV_PTR: InvState.Unary.sem_valueT conf st1 invst0 vt_inv = Some gv_inv)
  : InvState.Unary.sem_noalias conf gv_forget gv_inv ty_forget ty_inv.
Proof.
  unfold ForgetMemory.is_noalias_ExprPair in *.
  des; des_bool; des; subst; ss;
    eapply forget_memory_is_noalias_expr; eauto.
Qed.

Lemma exprpair_forget_memory_disjoint
      conf st1 mem0 invst0 invmem0 inv1
      cmd mc ptr
      p e1 e2
      (STATE: InvState.Unary.sem conf (mkState st1.(EC) st1.(ECS) mem0) invst0 invmem0 inv1)
      (* (UNIQUE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf (mkState st1.(EC) st1.(ECS) mem0)) *)
      (*                                                         (Invariant.unique inv1)) *)
      (MC_SOME : mem_change_of_cmd conf cmd st1.(EC).(Locals) = Some mc)
      (STATE_EQUIV : states_mem_change conf mem0 st1.(Mem) mc)
      (DEF_MEMORY: Cmd.get_def_memory cmd = Some ptr)
      (PAIR: p = (e1, e2) \/ p = (e2, e1))
      (FORGET_MEMORY : ExprPairSet.In p
                                      (Invariant.lessdef
                                         (ForgetMemory.unary ptr inv1)))
  : InvState.Unary.sem_expr conf st1 invst0 e1 =
    InvState.Unary.sem_expr conf (mkState st1.(EC) st1.(ECS) mem0) invst0 e1.
Proof.
  destruct mc.
  - (* alloc *)
    destruct cmd; ss; des_ifs.
  - (* store *)
    destruct cmd; ss; des_ifs.
    inv STATE_EQUIV.
    destruct e1; ss.
    + replace (InvState.Unary.sem_list_valueT conf {| EC := EC st1; ECS := ECS st1; Mem := mem0 |} invst0 lsv)
              with (InvState.Unary.sem_list_valueT conf st1 invst0 lsv); ss.
      clear.
      induction lsv; ss.
      destruct a. rewrite <- IHlsv. ss.
    + erewrite sem_valueT_eq_locals with (st1:=mkState st1.(EC) st1.(ECS) mem0); [| ss].
      des_ifs.
      apply ExprPairSetFacts.filter_iff in FORGET_MEMORY; try by solve_compat_bool.
      destruct FORGET_MEMORY as [FORGET_MEMORY_IN FORGET_MEMORY_NOALIAS].
      eapply mstore_noalias_mload; eauto.
      exploit forget_memory_is_noalias_exprpair; eauto.
  - (* free *)
    admit.
  - (* none *)
    inv STATE_EQUIV. destruct st1; eauto.
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
  (* inv STATE_FORGET. *)
  (* econs. *)
  (* { (* SRC *) *)
  (*   inv SRC. *)
  (*   econs. *)
  (*   - ii. *)
  
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
  assert (STATE2:= STATE).
  inv STATE2.
  exploit step_mem_change; try exact SRC; eauto. i. des.
  exploit step_mem_change; try exact TGT; eauto. i. des.
  exploit inject_invmem; try exact INJECT_EVENT; eauto. i. des.
  esplits; eauto.

  eapply forget_memory_equiv_except_mem; eauto.
  admit. (* InvState.Rel.mem monotone w.r.t. invmem1 *)
Admitted.

(* until here *)

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




(* from postcond cmd *)


(* Lemma step_equiv_except_mem *)
(*       conf st0 st1 evt *)
(*       cmd cmds *)
(*       invst0 invmem0 inv0 inv1 *)
(*       public gmax *)
(*       (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0) *)
(*       (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0) *)
(*       (NONCALL: Instruction.isCallInst cmd = false) *)
(*       (CMDS: CurCmds st0.(EC) = cmd :: cmds) *)
(*       (FORGET: inv_unary_forgot inv1 (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))) *)
(*       (STEP: sInsn conf st0 st1 evt) *)
(*   : exists mc, *)
(*     <<MEM_CH_REL: mem_change_cmd conf st0 mc cmd>> /\ *)
(*     <<STATE_EQUIV: state_equiv_except_mem conf (mkState st1.(EC) st1.(ECS) st0.(Mem)) st1 mc>>. *)
(* Proof. *)
(*   inv STEP; destruct cmd; inv CMDS; ss; *)
(*     try by esplits; eauto; econs; eauto; econs; eauto. *)
(*   - admit. (* malloc , should know newly allocated block is unique *) *)
(*   - admit. (* alloca *) *)
(* Admitted. *)

(* Lemma step_unique_preserved_mem *)
(*       conf st0 st1 evt *)
(*       cmd cmds inv0 *)
(*       (STATE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf (mkState st1.(EC) st1.(ECS) st0.(Mem))) *)
(*                                   inv0.(Invariant.unique)) *)
(*       (NONCALL: Instruction.isCallInst cmd = false) *)
(*       (CMDS: CurCmds st0.(EC) = cmd :: cmds) *)
(*       (STEP: sInsn conf st0 st1 evt) *)
(*       (UNIQUE_NOT_LEAKED: forall x (MEM:AtomSetImpl.mem x inv0.(Invariant.unique) = true), *)
(*                                  AtomSetImpl.mem x (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd)) = false) *)
(*   : unique_preserved_mem conf st1 inv0. *)
(* Proof. *)
(*   inv STEP; ss; *)
(*     try (inv CMDS; ss; *)
(*          ii; specialize_unique; eauto). *)
(*   { admit. (* load malloc -> undef *) } *)
(*   { admit. (* load after free: use Memory.Mem.load_free_2 maybe *) } *)
(*   { admit. (* load alloca *) } *)
(*   { admit. (* load after store *) } *)
(* Admitted. *)

(* Lemma mem_change_cmd_state_transition *)
(*       conf st0 st1 evt cmd cmds mc inv0 *)
(*       (CMD: CurCmds (EC st0) = cmd :: cmds) *)
(*       (NONCALL: Instruction.isCallInst cmd = false) *)
(*       (STEP: sInsn conf st0 st1 evt) *)
(*       (MEM_CH_REL: mem_change_cmd conf st0 mc cmd) *)
(*       (FORGET: inv_unary_forgot inv0 (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))) *)
(*   : mem_change_cmd_after conf {| EC := EC st1; ECS := ECS st1; Mem := Mem st0 |} mc cmd inv0. *)
(* Proof. *)
(*   destruct cmd; ss; *)
(*     inv STEP; ss; *)
(*       des; esplits; eauto. *)
(*   admit. (* easy *) *)
(* Admitted. *)



(* Lemma inject_event_implies_mem_change_inject *)
(*       m_src conf_src st0_src mc_src cmd_src *)
(*       m_tgt conf_tgt st0_tgt mc_tgt cmd_tgt *)
(*       invst0 invmem0 inv0 *)
(*       (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt) *)
(*       (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0) *)
(*       (MEM : InvMem.Rel.sem conf_src conf_tgt (Mem st0_src) (Mem st0_tgt) invmem0) *)
(*       (INJECT: postcond_cmd_inject_event cmd_src cmd_tgt inv0 = true) *)
(*       (MEM_CH_REL_SRC: mem_change_cmd conf_src st0_src mc_src cmd_src) *)
(*       (MEM_CH_REL_TGT: mem_change_cmd conf_tgt st0_tgt mc_tgt cmd_tgt) *)
(*   : mem_change_inject conf_src conf_tgt invmem0 mc_src mc_tgt. *)
(* Proof. *)
(*   destruct cmd_src; destruct cmd_tgt; ss; *)
(*     (try by des; subst; econs); des; subst; simtac; *)
(*       (try by exploit_inject_value; inv_conf; inject_clarify; econs; eauto). *)
(*   unfold Invariant.is_private in *. des_ifs. *)
(*   destruct x as [t x]; unfold ValueT.lift in *. des_ifs. *)
(*   inv STATE. inv SRC. *)
(*   exploit PRIVATE. *)
(*   { apply IdTSet.mem_2; eauto. } *)
(*   { inv_conf. *)
(*     inject_clarify. *)
(*   } *)
(*   i. des_ifs. *)
(*   econs; eauto. *)
(* Qed. *)


(* Lemma step_mem_change_inject *)
(*       m_src conf_src st0_src st1_src evt_src cmd_src cmds_src  *)
(*       m_tgt conf_tgt st0_tgt st1_tgt evt_tgt cmd_tgt cmds_tgt  *)
(*       invst0 invmem0 inv0 inv1 *)
(*       (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt) *)
(*       (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0) *)
(*       (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem)invmem0) *)
(*       (NONCALL_SRC: Instruction.isCallInst cmd_src = false) *)
(*       (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false) *)
(*       (CMDS_SRC: CurCmds st0_src.(EC) = cmd_src :: cmds_src) *)
(*       (CMDS_TGT: CurCmds st0_tgt.(EC) = cmd_tgt :: cmds_tgt) *)
(*       (FORGET_SRC: inv_unary_forgot inv1.(Invariant.src) (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))) *)
(*       (FORGET_TGT: inv_unary_forgot inv1.(Invariant.tgt) (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt)))) *)
(*       (STEP_SRC: sInsn conf_src st0_src st1_src evt_src) *)
(*       (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt_tgt) *)
(*       (INJECT: postcond_cmd_inject_event cmd_src cmd_tgt inv0 = true) *)
(*   : exists mc_src mc_tgt, *)
(*     <<MEM_CH_INJECT: mem_change_inject conf_src conf_tgt invmem0 mc_src mc_tgt>> /\ *)
(*     <<MEM_CH_CMD_SRC: mem_change_cmd_after conf_src (mkState st1_src.(EC) st1_src.(ECS) st0_src.(Mem)) mc_src cmd_src inv1.(Invariant.src)>> /\ *)
(*     <<MEM_CH_CMD_TGT: mem_change_cmd_after conf_tgt (mkState st1_tgt.(EC) st1_tgt.(ECS) st0_tgt.(Mem)) mc_tgt cmd_tgt inv1.(Invariant.tgt)>> /\ *)
(*     <<STATE_EQUIV_SRC: state_equiv_except_mem conf_src (mkState st1_src.(EC) st1_src.(ECS) st0_src.(Mem)) st1_src mc_src>> /\ *)
(*     <<STATE_EQUIV_TGT: state_equiv_except_mem conf_tgt (mkState st1_tgt.(EC) st1_tgt.(ECS) st0_tgt.(Mem)) st1_tgt mc_tgt>>. *)
(* Proof. *)
(*   destruct cmd_src; inv STEP_SRC; ss. *)
(*   Time destruct cmd_src eqn:CMD_SRC; destruct cmd_tgt eqn:CMD_TGT; ss; *)
(*     destruct st0_src; destruct EC0; inv STEP_SRC. *)
(*     inv STEP_SRC. *)
  
(*   destruct st0_src; ss. destruct EC0; ss. inv STEP_SRC; ss. *)
(*     try inv STEP_SRC; ss; inv STEP_TGT; ss. *)
(*       esplits; auto; *)
(*         econs; ss; econs; ss. *)
(*       - inv STEP_SRC; ss; inv STEP_TGT; ss; *)
(*       esplits; auto; *)
(*         econs; ss; econs; ss. *)
(*       - inv STEP_SRC; ss; inv STEP_TGT; ss; *)
(*       esplits; auto; *)
(*         econs; ss; econs; ss. *)
  
(*     try by inv STEP_SRC; ss; inv STEP_TGT; ss; *)
(*       esplits; auto; *)
(*         econs; ss; econs; ss. *)
(*     esplits; eauto. *)
(*     + econs. *)
(*     + econs; ss. *)
(*       inv STEP_SRC; ss. *)
(*       econs; ss. *)
(*     + econs; ss. *)
(*       inv STEP_TGT; ss. *)
(*       econs; ss. *)

(*     admit. (* nop nop *) *)
(*   - *)
(*   unfold postcond_cmd_inject_event in *. *)
  
(* Admitted. *)


(* Lemma step_equiv_except_mem *)
(*       conf st0 st1 evt *)
(*       cmd cmds *)
(*       invst0 invmem0 inv0 inv1 *)
(*       public gmax *)
(*       (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0) *)
(*       (STATE_FORGET: InvState.Unary.sem conf (mkState st1.(EC) st1.(ECS) st0.(Mem)) invst0 invmem0 inv1) *)
(*       (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0) *)
(*       (NONCALL: Instruction.isCallInst cmd = false) *)
(*       (CMDS: CurCmds st0.(EC) = cmd :: cmds) *)
(*       (FORGET: inv_unary_forgot inv1 (AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd)))) *)
(*       (STEP: sInsn conf st0 st1 evt) *)
(*   : exists mc, *)
(*     <<MEM_CH_CMD: mem_change_cmd_after conf (mkState st1.(EC) st1.(ECS) st0.(Mem)) mc cmd inv1>> /\ *)
(*                   <<STATE_EQUIV: state_equiv_except_mem conf (mkState st1.(EC) st1.(ECS) st0.(Mem)) st1 mc>>. *)
(* Proof. *)
(*   inv STEP; destruct cmd; inv CMDS; ss; *)
(*     try by esplits; eauto; econs; eauto; econs; eauto. *)
(*   - admit. (* malloc *) *)
(*   - esplits; eauto. *)
(*     econs; eauto. *)
(*     econs; eauto. *)
(*     + admit. (* malloc , should know newly allocated block is unique *) *)
(*     + ss. apply lookupAL_updateAddAL_eq. *)
(* Admitted. *)
