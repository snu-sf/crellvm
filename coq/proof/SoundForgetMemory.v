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
Require Import memory_props.

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

Inductive mem_change_inject (conf conf_tgt:Config) invmem: mem_change -> mem_change -> Prop :=
| mem_change_inject_alloc_alloc
    gsz gn0 gn1 a
    ty dv
    (N_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gn0 gn1)
  : mem_change_inject conf conf_tgt invmem (mem_change_alloc dv ty gsz gn0 a) (mem_change_alloc dv ty gsz gn1 a)
| mem_change_inject_alloc_none
    gsz gn a ty dv
  : mem_change_inject conf conf_tgt invmem (mem_change_alloc dv ty gsz gn a) mem_change_none
| mem_change_inject_none_alloc
    gsz gn a ty dv
  : mem_change_inject conf conf_tgt invmem mem_change_none (mem_change_alloc dv ty gsz gn a)
| mem_change_inject_store_store
    ptr0 ptr1 gv0 gv1 ty a
    (PTR_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) ptr0 ptr1)
    (VAL_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gv0 gv1)
  : mem_change_inject conf conf_tgt invmem (mem_change_store ptr0 ty gv0 a) (mem_change_store ptr1 ty gv1 a)
| mem_change_inject_store_nop
    ptr gv ty a b ofs
    (GV2PTR: GV2ptr conf.(CurTargetData) (getPointerSize conf.(CurTargetData)) ptr = Some (Values.Vptr b ofs))
    (IN: In b invmem.(InvMem.Rel.src).(InvMem.Unary.private))
  : mem_change_inject conf conf_tgt invmem (mem_change_store ptr ty gv a) mem_change_none
| mem_change_inject_free
    ptr0 ptr1
    (PTR_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) ptr0 ptr1)
  : mem_change_inject conf conf_tgt invmem (mem_change_free ptr0) (mem_change_free ptr1)
| mem_change_inject_none
  : mem_change_inject conf conf_tgt invmem mem_change_none mem_change_none
.

Inductive states_mem_change conf mem0 mem1: mem_change -> Prop :=
| states_mem_change_alloc
    ty bsz gn a dv mb
    (MALLOC: malloc conf.(CurTargetData) mem0 bsz gn a = Some (mem1, mb))
  : states_mem_change conf mem0 mem1 (mem_change_alloc dv ty bsz gn a)
| states_mem_change_store
    ptr ty gv a
    (VALID_PTRS: MemProps.valid_ptrs mem0.(Memory.Mem.nextblock) gv)
    (STORE: mstore conf.(CurTargetData) mem0 ptr ty gv a = Some mem1)
  : states_mem_change conf mem0 mem1 (mem_change_store ptr ty gv a)
| states_mem_change_free
    ptr
    (FREE: free conf.(CurTargetData) mem0 ptr = Some mem1)
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

Lemma gv_inject_ptr_public_src
      invmem ptr0 ptr1 b ofs conf_src
      (PTR_INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) ptr0 ptr1)
      (PTR : GV2ptr (CurTargetData conf_src) (getPointerSize (CurTargetData conf_src)) ptr0 = Some (Values.Vptr b ofs))
  : InvMem.Rel.public_src (InvMem.Rel.inject invmem) b.
Proof.
  exploit genericvalues_inject.simulation__GV2ptr; try exact PTR; eauto. i. des.
  ii. inv x1. clarify.
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
      ptr
      ptr_tgt conf_tgt b_tgt ofs_tgt
      invmem
      (PTR_INJECT : genericvalues_inject.gv_inject (InvMem.Rel.inject invmem) ptr ptr_tgt)
      (PTR_TGT : GV2ptr (CurTargetData conf_tgt) (getPointerSize (CurTargetData conf_tgt)) ptr_tgt = Some (Values.Vptr b_tgt ofs_tgt))
  : InvMem.Rel.public_tgt (InvMem.Rel.inject invmem) b_tgt.
Proof.
  exploit simulation__GV2ptr_tgt; try exact PTR_TGT; eauto. i. des.
  inv x1. unfold InvMem.Rel.public_tgt. esplits; eauto.
Qed.

(* Subset *)

Lemma forget_memory_unary_Subset
      def_mem leaks_mem inv0
  : Invariant.Subset_unary (ForgetMemory.unary def_mem leaks_mem inv0) inv0.
Proof.
  unfold ForgetMemory.unary.
  destruct leaks_mem; destruct def_mem.
  - econs; ss; ii; des_ifs; try econs; ss.
    + eapply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool. des. eauto.
    + eapply AtomSetFacts.remove_iff in H; try by solve_compat_bool. des. eauto.
  - econs; ss; ii; des_ifs; try econs; ss.
    eapply AtomSetFacts.remove_iff in H; try by solve_compat_bool. des. eauto.
  - econs; ss; ii; des_ifs; try econs; ss.
    eapply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool. des. eauto.
  - econs; ss; ii; des_ifs; try econs; ss.
Qed.

Lemma forget_memory_Subset
      def_mem_src def_mem_tgt
      leaks_mem_src leaks_mem_tgt
      inv0
  : Invariant.Subset (ForgetMemory.t def_mem_src def_mem_tgt leaks_mem_src leaks_mem_tgt inv0) inv0.
Proof.
  unfold ForgetMemory.t; des_ifs;
    econs; ss; try reflexivity; apply forget_memory_unary_Subset.
Qed.

(* soundness proof *)

Definition alloc_private_unary conf conf' cmd cmd' st b invmem: Prop :=
  forall x ty v a lc'
    (ALLOCA: cmd = insn_alloca x ty v a)
    (NOP: mem_change_of_cmd conf' cmd' lc' = Some mem_change_none),
  exists gptr,
    <<PRIVATE: In b invmem.(InvMem.Unary.private)>> /\
    <<PTR: lookupAL _ st.(EC).(Locals) x = Some gptr>> /\
    <<GV2PTR: GV2ptr conf.(CurTargetData) conf.(CurTargetData).(getPointerSize) gptr =
              Some (Values.Vptr b (Integers.Int.zero 31))>>.

Definition alloc_private conf_src conf_tgt cmd_src cmd_tgt
           st0_src st0_tgt st1_src st1_tgt invmem : Prop :=
  alloc_private_unary conf_src conf_tgt cmd_src cmd_tgt st1_src st0_src.(Mem).(Memory.Mem.nextblock) invmem.(InvMem.Rel.src) /\
  alloc_private_unary conf_tgt conf_src cmd_tgt cmd_src st1_tgt st0_tgt.(Mem).(Memory.Mem.nextblock) invmem.(InvMem.Rel.tgt).

Definition alloc_inject_unary conf st1 x b :=
  exists gptr,
  lookupAL _ st1.(EC).(Locals) x = Some gptr /\
  GV2ptr conf.(CurTargetData) conf.(CurTargetData).(getPointerSize) gptr =
  Some (Values.Vptr b (Integers.Int.zero 31)).

Definition alloc_inject conf_src conf_tgt st0_src st0_tgt
           st1_src st1_tgt cmd_src cmd_tgt invmem1 : Prop :=
  forall x ty v_src v_tgt a
         (ALLOCA_SRC: cmd_src = insn_alloca x ty v_src a)
         (ALLOCA_TGT: cmd_tgt = insn_alloca x ty v_tgt a),
    alloc_inject_unary conf_src st1_src x st0_src.(Mem).(Memory.Mem.nextblock) /\
    alloc_inject_unary conf_tgt st1_tgt x st0_tgt.(Mem).(Memory.Mem.nextblock) /\
    invmem1.(InvMem.Rel.inject) st0_src.(Mem).(Memory.Mem.nextblock) =
    Some (st0_tgt.(Mem).(Memory.Mem.nextblock), 0).

(* Lemma getOperandValue_wf_lc_valid_ptrs *)
(*       TD lc gl *)
(*       mem v gv *)
(*       (VAL : getOperandValue TD v lc gl = Some gv) *)
(*       (WF_LOCAL : MemProps.wf_lc mem lc) *)
(*   : MemProps.valid_ptrs mem.(Memory.Mem.nextblock) gv. *)
(* Proof. *)
(*   apply WF_LOCAL in VAL. *)
(* (* hope MemProps.operand__lt_nextblock helps *) *)
(* Admitted. *)

Lemma step_mem_change
      st0 st1 invst0 invmem0 inv0
      cmd cmds
      conf evt gmax public
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
      (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0)
      (CMD: st0.(EC).(CurCmds) = cmd::cmds)
      (NONCALL: Instruction.isCallInst cmd = false)
      (STEP: sInsn conf st0 st1 evt)
  : <<UNIQUE_PARENT_MEM:
      forall mptr typ align val'
        (LOAD: mload conf.(CurTargetData) st1.(Mem) mptr typ align = Some val'),
        InvMem.gv_diffblock_with_blocks conf val' invmem0.(InvMem.Unary.unique_parent)>> /\
        exists mc,
          <<MC_SOME: mem_change_of_cmd conf cmd st0.(EC).(Locals) = Some mc>> /\
          <<STATE_EQUIV: states_mem_change conf st0.(Mem) st1.(Mem) mc>>.
Proof.
  inv MEM.
  inv STEP; destruct cmd; ss; clarify;
    try by esplits; ss; econs; eauto.
  - admit. (* malloc - easy *)
  - split.
    + ii. eapply UNIQUE_PARENT_MEM; eauto.
      eapply MemProps.free_preserves_mload_inv; eauto.
    + esplits; ss.
      * des_ifs.
      * econs; eauto.
  - split.
    + ii.
      exploit MemProps.malloc_preserves_mload_inv; eauto. i. des.
      { eapply UNIQUE_PARENT_MEM; eauto. }
      { ss.
        destruct val'; ss.
        des_ifs.
        exploit x0; eauto. i. congruence.
      }
    + esplits; ss.
      * des_ifs.
      * econs; eauto.
  - split.
    + admit.
      (* exploit MemProps.mstore_preserves_mload_inv; eauto. i. des. *)
      (* mstore *)
    + admit.
Admitted.
  (* inv STEP; ss; *)
  (*   try (by inv CMD; *)
  (*        esplits; ss; econs; eauto); *)
  (*   try (by inv CMD; *)
  (*        esplits; ss; [des_ifs | econs]; eauto). *)
  (* - admit. (* not malloc, easy *) *)
  (* - inv CMD. *)
  (*   esplits; ss. *)
  (*   + des_ifs. *)
  (*   + econs; eauto. *)
  (*     inv STATE. ss. *)
  (*     eapply getOperandValue_wf_lc_valid_ptrs; eauto. *)

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

Lemma malloc_contents_same
      TD mem0 mem1 gsz gn a
      mb ofs
      (MALLOC: malloc TD mem0 gsz gn a = Some (mem1, mb))
  : Maps.ZMap.get ofs (Maps.PMap.get mb (Memory.Mem.mem_contents mem1)) = Memdata.Undef.
Proof.
  exploit malloc_inv; eauto. intro ALLOC.
  erewrite <- Memory.Mem.alloc_mem_contents; eauto.
  rewrite (Memory.Mem.alloc_result _ _ _ _ _ ALLOC).
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
  exploit malloc_inv; eauto. intro ALLOC.
  erewrite <- Memory.Mem.alloc_mem_contents; eauto.
  rewrite (Memory.Mem.alloc_result _ _ _ _ _ ALLOC) in DIFF.
  rewrite Maps.PMap.gsspec.
  des_ifs.
Qed.

Lemma malloc_preserves_mload_aux_other_eq
      TD mem0 bsz gn a mem1 mb
      ch b ofs
      (MALLOC: malloc TD mem0 bsz gn a = Some (mem1, mb))
      (DIFFBLOCK: b <> mb)
  : mload_aux mem0 ch b ofs = mload_aux mem1 ch b ofs.
Proof.
  exploit malloc_inv; eauto. intro ALLOC.
  destruct (mload_aux mem1 ch b ofs) eqn:LOAD1.
  - exploit MemProps.alloc_preserves_mload_aux_inv; eauto. i. des; congruence.
  - destruct (mload_aux mem0 ch b ofs) eqn:LOAD0; eauto.
    exploit MemProps.alloc_preserves_mload_aux; eauto. i. congruence.
Qed.

Lemma malloc_preserves_mload_other_eq
      TD mem0 bsz gn a mem1 mb
      ptr b ofs tyl al
      (MALLOC: malloc TD mem0 bsz gn a = Some (mem1, mb))
      (GV2PTR: GV2ptr TD (getPointerSize TD) ptr = Some (Values.Vptr b ofs))
      (DIFFBLOCK: b <> mb)
  : mload TD mem0 ptr tyl al = mload TD mem1 ptr tyl al.
Proof.
  unfold mload. rewrite GV2PTR.
  destruct (flatten_typ TD tyl); ss.
  eapply malloc_preserves_mload_aux_other_eq; eauto.
Qed.

Lemma mstore_aux_valid_access
      mem0 mem1 gv p
      chunkl b ofs
      chunk' b' ofs'
      (MALLOC: mstore_aux mem0 chunkl gv b ofs = Some mem1)
  : Memory.Mem.valid_access mem0 chunk' b' ofs' p <->
    Memory.Mem.valid_access mem1 chunk' b' ofs' p.
Proof.
  split.
  - revert mem0 mem1 gv ofs MALLOC.
    induction chunkl; ss; i; des_ifs.
    apply IHchunkl in MALLOC; eauto.
    eapply Memory.Mem.store_valid_access_1; eauto.
  - revert mem0 mem1 gv ofs MALLOC.
    induction chunkl; ss; i; des_ifs.
    apply IHchunkl in MALLOC; eauto.
    eapply Memory.Mem.store_valid_access_2; eauto.
Qed.

Lemma mstore_aux_preserves_mload_aux_eq
      Mem Mem' gv
      mc1 b1 ofs1
      mc2 b2 ofs2
      (DIFFBLOCK: b1 <> b2)
      (MSTORE_AUX: mstore_aux Mem mc1 gv b1 ofs1 = Some Mem')
  : mload_aux Mem mc2 b2 ofs2 = mload_aux Mem' mc2 b2 ofs2.
Proof.
  destruct (mload_aux Mem mc2 b2 ofs2) eqn:MLOAD_AUX0.
  - symmetry. eapply MemProps.mstore_aux_preserves_mload_aux; eauto.
  - destruct (mload_aux Mem' mc2 b2 ofs2) eqn:MLOAD_AUX1; ss.
    exploit MemProps.mstore_aux_preserves_mload_aux_inv; eauto.
    i. des. congruence.
Qed.

Lemma mstore_aux_preserves_perm
      M M' mc gv b ofs b' ofs' k p
      (MSTORE: mstore_aux M mc gv b ofs = Some M')
  : Memory.Mem.perm M b' ofs' k p <->
    Memory.Mem.perm M' b' ofs' k p.
Proof.
  split.
  - revert M M' gv ofs MSTORE.
    induction mc; i; ss; des_ifs.
    apply IHmc in MSTORE; eauto.
    eapply Memory.Mem.perm_store_1; eauto.
  - revert M M' gv ofs MSTORE.
    induction mc; i; ss; des_ifs.
    apply IHmc in MSTORE; eauto.
    eapply Memory.Mem.perm_store_2; eauto.
Qed.

Lemma free_preserves_mload_aux_eq
      mem0 blk lo hi mem1 b
      mc ofs
      (FREE: Memory.Mem.free mem0 blk lo hi = Some mem1)
      (DIFFBLOCK: blk <> b)
  : mload_aux mem0 mc b ofs = mload_aux mem1 mc b ofs.
Proof.
  destruct (mload_aux mem0 mc b ofs) eqn:MLOAD0.
  - exploit MemProps.free_preserves_mload_aux; eauto.
  - destruct (mload_aux mem1 mc b ofs) eqn:MLOAD1; eauto.
    exploit MemProps.free_preserves_mload_aux_inv; eauto. i.
    congruence.
Qed.

Lemma mstore_aux_getN_out
      (chunk : list AST.memory_chunk) (m1 : Memory.Mem.mem) (b : Values.block) (ofs : Z)
      (gv : GenericValue) (m2 : Memory.Mem.mem)
      (STORE: mstore_aux m1 chunk gv b ofs = Some m2)
      (blk : Values.block) (ofs1 : Z) (sz : nat)
      (DIFFBLOCK: blk <> b)
  : Memory.Mem.getN sz ofs1 (Maps.PMap.get blk (Memory.Mem.mem_contents m1)) =
    Memory.Mem.getN sz ofs1 (Maps.PMap.get blk (Memory.Mem.mem_contents m2)).
Proof.
  revert m1 ofs gv STORE.
  induction chunk; i; ss; des_ifs.
  eapply IHchunk in STORE. rewrite <- STORE.
  eapply Memory.Mem.store_getN_out; eauto.
Qed.

(* noalias definition change can make this provable *)
Lemma mstore_noalias_mload
      conf mem0 mem1 TD
      sptr sty gv sa
      lptr lty la
      (STORE: Some mem1 = mstore TD mem0 sptr sty gv sa)
      (NOALIAS: InvState.Unary.sem_noalias conf sptr lptr sty lty)
  : mload TD mem1 lptr lty la = mload TD mem0 lptr lty la.
Proof.
  (* destruct (mload TD mem1 lptr lty la) eqn:LOAD1. *)
  (* - exploit MemProps.mstore_preserves_mload_inv'; eauto. *)
  (* MemProps.mstore_preserves_mload *)

  (* MemProps.no_alias is diffblock for us, so we cannot prove this right now *)
Admitted.

Lemma mfree_noalias_mload
      conf mem0 mem1 TD
      ptr ty lptr lty la
      (FREE: free TD mem0 ptr = Some mem1)
      (NOALIAS: InvState.Unary.sem_noalias conf ptr lptr ty lty)
  : mload TD mem1 lptr lty la = mload TD mem0 lptr lty la.
Proof.
Admitted.

Lemma mstore_aux_valid_ptrs_preserves_wf_Mem
      gmax conf mem0 mem1
      b ofs ch gv
      (WF_MEM : MemProps.wf_Mem gmax conf.(CurTargetData) mem0)
      (VALID_PTRS: MemProps.valid_ptrs mem0.(Memory.Mem.nextblock) gv)
      (STORE : mstore_aux mem0 ch gv b ofs = Some mem1)
  : MemProps.wf_Mem gmax (CurTargetData conf) mem1.
Proof.
Admitted.

Lemma mstore_const_leak_no_unique
      conf st0 u gv c
      ptr ty a mem1
      (UNIQUE_U : InvState.Unary.sem_unique conf st0 u)
      (* (DIFF_ID: x <> u) *)
      (* (PTR: lookupAL GenericValue st0.(EC).(Locals) x = Some gv) *)
      (PTR: const2GV conf.(CurTargetData) conf.(Globals) c = Some gv)
      (STORE : mstore conf.(CurTargetData) st0.(Mem) ptr ty gv a = Some mem1)
  : InvState.Unary.sem_unique conf (mkState st0.(EC) st0.(ECS) mem1) u.
Proof.
Admitted.

Lemma mstore_register_leak_no_unique
      conf st0 x u gv
      ptr ty a mem1
      (UNIQUE_U : InvState.Unary.sem_unique conf st0 u)
      (DIFF_ID: x <> u)
      (PTR: lookupAL GenericValue st0.(EC).(Locals) x = Some gv)
      (STORE : mstore conf.(CurTargetData) st0.(Mem) ptr ty gv a = Some mem1)
  : InvState.Unary.sem_unique conf (mkState st0.(EC) st0.(ECS) mem1) u.
Proof.
Admitted.

(* tactic for positive. TODO: can we use Hint instead this? *)
Ltac psimpl :=
  unfold Ple, Plt in *;
  subst;
  try repeat match goal with
             | [H1: ?y = Pos.succ ?x |- _] =>
               let le := fresh "PLE" in
               let lt := fresh "PLT" in
               assert(le : (x <= y)%positive);
               [by rewrite H1; apply Ple_succ|];
               assert(lt : (x < y)%positive);
               [by rewrite H1; apply Plt_succ|];
               clear H1
             end;
  repeat
    match goal with
    | [H: ~ (?x < ?y)%positive |- _] =>
      apply Pos.le_nlt in H
    | [H: (?a >= ?b)%positive |- _] =>
      apply Pos.ge_le in H
    | [H: _ |- (?a >= ?b)%positive] =>
      apply Pos.le_ge
    end;
  try (by apply Ple_refl);
  try (by assumption);
  match goal with
  | [H: (?x < ?x)%positive |- _] =>
      by apply Pos.lt_irrefl in H; inv H
  | [H1: (?x <= ?y)%positive,
         H2: (?y <= ?z)%positive |-
     (?x <= ?z)%positive ] =>
      by eapply Pos.le_trans; eauto
  | [H1: (?x < ?y)%positive,
         H2: (?y < ?z)%positive |-
     (?x < ?z)%positive ] =>
      by eapply Pos.lt_trans; eauto
  | [H: (Pos.succ ?x <= ?x)%positive |- _] =>
      by generalize H; apply Pos.lt_nle; apply Plt_succ'
  end.

(* invmem *)

Lemma invmem_unary_alloc_private_preserved
      conf invmem0 mem0 mem1
      gmax public mb
      gsz gn a
      (STATE : InvMem.Unary.sem conf gmax public mem0 invmem0)
      (MALLOC : malloc (CurTargetData conf) mem0 gsz gn a = Some (mem1, mb))
      (PUBLIC: ~ public mb)
  : InvMem.Unary.sem conf gmax public mem1 (InvMem.Unary.mk
                                              (mb::invmem0.(InvMem.Unary.private))
                                              invmem0.(InvMem.Unary.private_parent)
                                              invmem0.(InvMem.Unary.mem_parent)
                                              invmem0.(InvMem.Unary.unique_parent)
                                              mem1.(Memory.Mem.nextblock)).
Proof.
  exploit malloc_result; eauto. i. des.
  inv STATE.
  econs; eauto.
  - eapply MemProps.malloc_preserves_wf_Mem; eauto.
  - i. ss. des.
    + subst. split; eauto. psimpl.
    + exploit PRIVATE; eauto. i. des.
      split; eauto. psimpl.
  - i. exploit PRIVATE_PARENT; eauto. i. des.
    split; eauto. psimpl.
  - ss. ii.
    inv H.
    + exploit PRIVATE_PARENT; eauto. i. des.
      subst. psimpl.
    + exploit PRIVATE_DISJOINT; eauto.
  - i. exploit MEM_PARENT; eauto. intro LOAD_AUX.
    rewrite LOAD_AUX.
    eapply malloc_preserves_mload_aux_other_eq; eauto.
    ii. exploit PRIVATE_PARENT; eauto. i. des. psimpl.
  - ss. i.
    unfold mload in LOAD. des_ifs.
    destruct (Values.eq_block b (Memory.Mem.nextblock mem0)); cycle 1.
    + eapply UNIQUE_PARENT_MEM; eauto.
      erewrite malloc_preserves_mload_other_eq; eauto.
      instantiate (1:= align0).
      unfold mload.
      instantiate (1:= typ0).
      des_ifs.
    + subst.
      exploit MemProps.alloc_preserves_mload_aux_inv; eauto.
      { unfold malloc in *. apply some_injective in MALLOC. eauto. }
      intro LOAD_UNDEF. des.
      { congruence. }
      ii. exploit external_intrinsics.GV2ptr_inv; eauto. i. des.
      subst. ss. clarify.
      exploit LOAD_UNDEF; eauto.
      i. congruence.
Qed.

Ltac solve_alloc_inject :=
  by ii;
  match goal with
  | [ALLOCA: ?cmd = insn_alloca _ _ _ _,
             MC_SOME: mem_change_of_cmd _ ?cmd _ = Some mem_change_none |- _] =>
    rewrite ALLOCA in MC_SOME; ss; des_ifs
  | [ALLOCA: ?cmd = insn_alloca _ _ _ _,
             MC_SOME: mem_change_of_cmd _ ?cmd _ = Some (mem_change_store _ _ _ _) |- _] =>
    rewrite ALLOCA in MC_SOME; ss; des_ifs
  | [ALLOCA: ?cmd = insn_alloca _ _ _ _,
             MC_SOME: mem_change_of_cmd _ ?cmd _ = Some (mem_change_free _) |- _] =>
    rewrite ALLOCA in MC_SOME; ss; des_ifs
  end.

Lemma inject_invmem
      m_src conf_src st0_src st1_src cmd_src cmds_src evt_src
      m_tgt conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt evt_tgt
      invst0 invmem0 inv0
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
  : exists invmem1,
    <<ALLOC_INJECT: alloc_inject conf_src conf_tgt st0_src st0_tgt
                                 st1_src st1_tgt cmd_src cmd_tgt invmem1>> /\
    <<ALLOC_PRIVATE: alloc_private conf_src conf_tgt cmd_src cmd_tgt st0_src st0_tgt st1_src st1_tgt invmem1>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt (Mem st1_src) (Mem st1_tgt) invmem1 >> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1 >> /\
    <<PRIVATE_PRESERVED_SRC: forall p, In p invmem0.(InvMem.Rel.src).(InvMem.Unary.private) ->
                                  In p invmem1.(InvMem.Rel.src).(InvMem.Unary.private)>> /\
    <<PRIVATE_PRESERVED_TGT: forall p, In p invmem0.(InvMem.Rel.tgt).(InvMem.Unary.private) ->
                                  In p invmem1.(InvMem.Rel.tgt).(InvMem.Unary.private)>>.
Proof.
  hexploit step_mem_change; try (inv STATE; exact SRC); eauto.
  { inv MEM. exact SRC. }
  intro MCS.
  destruct MCS as [UNIQUE_PRIVATE_SRC [mc_src [MC_SOME_SRC STATE_EQUIV_SRC]]]. des.
  hexploit step_mem_change; try (inv STATE; exact TGT); eauto.
  { inv MEM. exact TGT. }
  intro MCS.
  destruct MCS as [UNIQUE_PRIVATE_TGT [mc_tgt [MC_SOME_TGT STATE_EQUIV_TGT]]]. des.

  exploit inject_mem_change; eauto. intro MC_INJECT.

  inv MC_INJECT.
  - (* alloc - alloc *)
    inv STEP_SRC; inv CMD_SRC; ss; des_ifs.
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
      esplits.
      * unfold alloc_inject_unary.
        esplits; try apply lookupAL_updateAddAL_eq; ss;
          (exploit malloc_result; try exact MALLOC_SRC; eauto; []; ii; des; subst; ss).
      * unfold alloc_inject_unary.
        esplits; try apply lookupAL_updateAddAL_eq; ss;
          (exploit malloc_result; try exact MALLOC_TGT; eauto; []; ii; des; subst; ss).
      *
        (exploit malloc_result; try exact MALLOC_SRC; eauto; []; ii; des; subst; ss).
        (exploit malloc_result; try exact MALLOC_TGT; eauto; []; ii; des; subst; ss).
        destruct (Values.eq_block (Memory.Mem.nextblock mem0_src)(Memory.Mem.nextblock mem0_src)); ss.
    + (* alloc_private *)
      econs; ii; ss; des_ifs.
    + (* InvMem sem *)
      inv MEM; ss.
      econs; ss; eauto.
      { (* SRC *)
        inv SRC.
        hexploit (@malloc_result TD mem0_src); eauto. i. des.
        instantiate (1:= InvMem.Unary.mk _
                                         invmem0.(InvMem.Rel.src).(InvMem.Unary.private_parent)
                                         invmem0.(InvMem.Rel.src).(InvMem.Unary.mem_parent)
                                         invmem0.(InvMem.Rel.src).(InvMem.Unary.unique_parent)
                                         mem1_src.(Memory.Mem.nextblock)).
        econs; eauto.
        { eapply MemProps.malloc_preserves_wf_Mem; eauto. }
        { i. exploit PRIVATE; eauto. i.
          des.
          destruct (Values.eq_block b mb_src) eqn:EQ_MB.
          - subst. psimpl.
          - split.
            + ii.
              match goal with
              | [H: ~ InvMem.Rel.public_src _ _ |- False] =>
                apply H
              end.
              unfold InvMem.Rel.public_src in *. rewrite EQ_MB in *. eauto.
            + psimpl.
        }
        { i. exploit PRIVATE_PARENT; eauto. i. des.
          destruct (Values.eq_block b mb_src) eqn:EQ_MB.
          - subst. psimpl.
          - split.
            + ii. apply x.
              unfold InvMem.Rel.public_src in *. rewrite EQ_MB in *. eauto.
            + psimpl.
        }
        { i. exploit MEM_PARENT; eauto. i. ss.
          match goal with
          | [H: mload_aux (InvMem.Unary.mem_parent _) _ b _ = _ |- _] =>
            rewrite H
          end.
          exploit PRIVATE_PARENT; eauto. i. des.
          eapply malloc_preserves_mload_aux_other_eq; eauto.
          ii. psimpl.
        }
      }
      { (* TGT *)
        inv TGT.
        hexploit (@malloc_result TD0 mem0_tgt); eauto. i. des.
        instantiate (1:= InvMem.Unary.mk _
                                         invmem0.(InvMem.Rel.tgt).(InvMem.Unary.private_parent)
                                         invmem0.(InvMem.Rel.tgt).(InvMem.Unary.mem_parent)
                                         invmem0.(InvMem.Rel.tgt).(InvMem.Unary.unique_parent)
                                         mem1_tgt.(Memory.Mem.nextblock)).
        econs; eauto.
        { eapply MemProps.malloc_preserves_wf_Mem; eauto. }
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
            { clarify. exfalso. psimpl. }
            { esplits; eauto. }
          }
          { psimpl. }
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
            { clarify. exfalso. psimpl. }
            { esplits; eauto. }
          }
          { psimpl. }
        }
        { i. exploit MEM_PARENT; eauto. i.
          match goal with
          | [H: mload_aux (InvMem.Unary.mem_parent _) _ b _ = _ |- _] =>
            rewrite H
          end.
          exploit PRIVATE_PARENT; eauto. i. des.
          eapply malloc_preserves_mload_aux_other_eq; eauto.
          ii. psimpl.
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
            repeat rewrite Z.add_0_r.
            des. splits; eauto.
            exploit genericvalues_inject.simulation__eq__GV2int; eauto. intro GV2INT_INJECT.
            rewrite <- GV2INT_INJECT. eauto.
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
                { eapply malloc_inv; eauto. }
                ii. psimpl.
              }
              eapply malloc_contents_other in DIFF_BLK_TGT; eauto.
              rewrite DIFF_BLK_TGT.
              erewrite malloc_contents_other; eauto.
              apply mi_memval; eauto.
              exploit Memory.Mem.perm_alloc_inv.
              { eapply malloc_inv; try exact MALLOC_SRC. }
              { eauto. }
              i. des_ifs.
            }
            { ii.
              destruct (Values.eq_block b mb_src).
              { subst. exfalso.
                exploit genericvalues_inject.Hmap1; eauto.
                { instantiate (1:=mb_src).
                  exploit malloc_inv; try exact MALLOC_SRC. i.
                  exploit (Memory.Mem.alloc_result mem0_src); eauto. i.
                  psimpl. }
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
          + exploit Hmap2; eauto. i. psimpl.
          + exploit Hmap2; eauto. i. psimpl.
          + eapply Hno_overlap with (b1:=b1) (b2:=b2); eauto.
        - (* Hmap1 *)
          intro b_src. i. destruct (Values.eq_block b_src mb_src).
          + subst.
            rewrite NEXT_BLOCK_SRC in *.
            exfalso. psimpl.
          + apply Hmap1. psimpl.
        - (* Hmap2 *)
          intros b_src b_tgt. i. destruct (Values.eq_block b_src mb_src).
          + clarify.
            subst. rewrite NEXT_BLOCK_TGT in *.
            apply Plt_succ'.
          + exploit Hmap2; eauto. i. psimpl.
        - (* mi_freeblocks *)
          intros b NOT_VALID_BLOCK.
          destruct (Values.eq_block b mb_src).
          + subst.
            exfalso.
            apply NOT_VALID_BLOCK.
            unfold Memory.Mem.valid_block.
            psimpl.
          + apply mi_freeblocks. intros VALID_BLOCK.
            apply NOT_VALID_BLOCK.
            unfold Memory.Mem.valid_block in *.
            psimpl.
        - (* mi_mappedblocks *)
          i. destruct (Values.eq_block b mb_src).
          + clarify.
            unfold Memory.Mem.valid_block in *.
            psimpl.
          + eapply Memory.Mem.valid_block_alloc.
            { eapply malloc_inv ;eauto. }
            eapply mi_mappedblocks; eauto.
        - (* mi_range_blocks *)
          ii. destruct (Values.eq_block b mb_src).
          + subst. clarify.
          + eapply mi_range_block; eauto.
        - (* mi_bounds *)
          ii. destruct (Values.eq_block b mb_src).
          + clarify.
            erewrite Memory.Mem.bounds_alloc_same; cycle 1.
            { eapply malloc_inv; eauto. }
            erewrite Memory.Mem.bounds_alloc_same; cycle 1.
            { eapply malloc_inv; eauto. }
            apply injective_projections; ss.
            solve_match_bool. clarify.
            exploit genericvalues_inject.simulation__eq__GV2int; eauto. intro GV2INT_INJECT.
            rewrite <- GV2INT_INJECT. eauto.
          + erewrite Memory.Mem.bounds_alloc_other with (b':=b); eauto; cycle 1.
            { eapply malloc_inv; eauto. }
            assert (NEQ_BLK_TGT: b' <> mb_tgt).
            { exploit Hmap2; eauto. ii. psimpl. }
            erewrite Memory.Mem.bounds_alloc_other with (b':=b'); try exact NEQ_BLK_TGT; cycle 1.
            { eapply malloc_inv; eauto. }
            eapply mi_bounds; eauto.
        - (* mi_globals *)
          i. destruct (Values.eq_block b mb_src).
          + subst.
            exploit mi_globals; eauto. i.
            exploit Hmap1.
            { psimpl. }
            i. congruence.
          + exploit mi_globals; eauto.
      }
    + (* le *)
      econs; try (econs; ss).
      { inv MEM. inv SRC. rewrite <- NEXTBLOCK.
        exploit malloc_result; try exact MALLOC_SRC; eauto. i. des.
        psimpl. }
      { inv MEM. inv TGT. rewrite <- NEXTBLOCK.
        exploit malloc_result; try exact MALLOC_TGT; eauto. i. des.
        psimpl. }
      (* incr *)
      ii. ss.
      exploit malloc_result; try exact MALLOC_SRC. intros [ALLOC_BLOCK_SRC NEXT_BLOCK_SRC]. des.
      exploit malloc_result; try exact MALLOC_TGT. intros [ALLOC_BLOCK_TGT NEXT_BLOCK_TGT]. des.
      destruct (Values.eq_block b mb_src); eauto.
      subst.
      inv MEM. inv WF.
      exploit Hmap1.
      { psimpl. }
      i. congruence.
    + eauto.
    + eauto.
  - (* alloc - none *)
    Ltac des_matchH H :=
      repeat
        match goal with
        | [ H' : context[match ?X with _ => _ end] |- _ ] => check_equal H' H; destruct X
        end.

    inv STATE_EQUIV_TGT. rewrite <- MEM_EQ in *.

    inv STEP_SRC; destruct cmd_src; ss; clarify;
      des_matchH MC_SOME_SRC; clarify; ss.
    rename Mem0 into mem0_src.
    rename Mem' into mem1_src.
    inv STATE_EQUIV_SRC. ss. clarify.

    exists (InvMem.Rel.mk
         (InvMem.Unary.mk
            (mb::invmem0.(InvMem.Rel.src).(InvMem.Unary.private))
            invmem0.(InvMem.Rel.src).(InvMem.Unary.private_parent)
            invmem0.(InvMem.Rel.src).(InvMem.Unary.mem_parent)
            invmem0.(InvMem.Rel.src).(InvMem.Unary.unique_parent)
            mem1_src.(Memory.Mem.nextblock))
         invmem0.(InvMem.Rel.tgt)
         invmem0.(InvMem.Rel.gmax)
                   invmem0.(InvMem.Rel.inject)).
    esplits; ss; eauto.
    + (* alloc_inject *)
      solve_alloc_inject.
    + (* alloc_private *)
      econs; ii; ss; try by des_ifs.
      clarify.
      exploit malloc_result; eauto. i. des.
      esplits; try apply lookupAL_updateAddAL_eq.
      * left. eauto.
      * ss. rewrite ALLOC_BLOCK. eauto.
    + inv MEM.
      exploit malloc_result; eauto. i. des.
      econs; eauto.
      * ss. eapply invmem_unary_alloc_private_preserved; eauto.
        ii. unfold InvMem.Rel.public_src in *.
        apply H.
        inv WF.
        apply Hmap1. psimpl.
      * inv INJECT.
        econs.
        { (* mi-access *)
          i. exploit mi_access; eauto.
          assert (DIFFBLOCK_ALLOC: b1 <> Memory.Mem.nextblock mem0_src).
          { inv WF.
            ii. exploit Hmap1.
            { instantiate (1:= Memory.Mem.nextblock mem0_src).
              psimpl. }
            i. subst. ss. congruence.
          }
          exploit valid_access_malloc_inv; eauto.
          des_ifs.
        }
        { (* mi_memval *)
          i.
          assert (DIFFBLOCK_ALLOC: b1 <> Memory.Mem.nextblock mem0_src).
          { inv WF.
            ii. exploit Hmap1.
            { instantiate (1:= Memory.Mem.nextblock mem0_src).
              psimpl. }
            i. subst. ss. congruence.
          }
          exploit mi_memval; eauto.
          { hexploit Memory.Mem.perm_alloc_inv; eauto.
            { eapply malloc_inv; eauto. }
            clear INJECT_EVENT.
            des_ifs. eauto.
          }
          i. exploit malloc_contents_other; eauto.
          intro CONTENTS.
          rewrite CONTENTS. eauto.
        }
      * inv WF.
        econs; eauto.
        ++ i. apply Hmap1. psimpl.
        ++ i. apply Hmap1.
           unfold Memory.Mem.valid_block in *. psimpl.
        ++ i.
           assert (ALLOC_PRIVATE: b <> Memory.Mem.nextblock mem0_src).
           { ii. subst.
             exploit Hmap1.
             { psimpl. }
             i. ss. congruence. }
           erewrite Memory.Mem.bounds_alloc_other; try exact ALLOC_PRIVATE; cycle 1.
           { eapply malloc_inv. exact MALLOC. }
           eapply mi_bounds; eauto.
    + econs; eauto.
      * econs; eauto. ss.
        inv MEM. inv SRC.
        rewrite <- NEXTBLOCK.
        exploit malloc_result; eauto. i. des.
        psimpl.
      * econs; eauto. ss.
        inv MEM. inv TGT.
        rewrite <- NEXTBLOCK.
        exploit malloc_result; eauto. i. des.
        psimpl.
  - (* none - alloc *)
    inv STATE_EQUIV_SRC.
    rewrite <- MEM_EQ in *.

    inv STEP_TGT; destruct cmd_tgt; ss; clarify;
      des_matchH MC_SOME_TGT; clarify; ss.
    rename Mem0 into mem0_tgt.
    rename Mem' into mem1_tgt.
    inv STATE_EQUIV_TGT. ss. clarify.

    exists (InvMem.Rel.mk
         invmem0.(InvMem.Rel.src)
         (InvMem.Unary.mk
            (mb::invmem0.(InvMem.Rel.tgt).(InvMem.Unary.private))
            invmem0.(InvMem.Rel.tgt).(InvMem.Unary.private_parent)
            invmem0.(InvMem.Rel.tgt).(InvMem.Unary.mem_parent)
            invmem0.(InvMem.Rel.tgt).(InvMem.Unary.unique_parent)
            mem1_tgt.(Memory.Mem.nextblock))
         invmem0.(InvMem.Rel.gmax)
                   invmem0.(InvMem.Rel.inject)).
    esplits; ss; eauto.
    + (* alloc_inject *)
      solve_alloc_inject.
    + (* alloc_private *)
      econs; ii; ss; try by des_ifs.
      clarify.
      exploit malloc_result; eauto. i. des.
      esplits; try apply lookupAL_updateAddAL_eq.
      * left. eauto.
      * ss. rewrite ALLOC_BLOCK. eauto.
    + inv MEM.
      exploit malloc_result; eauto. i. des.
      econs; eauto.
      * eapply invmem_unary_alloc_private_preserved; eauto.
        ss. ii. unfold InvMem.Rel.public_tgt in *. des.
        inv WF.
        exploit Hmap2; eauto. i.
        psimpl.
      * inv INJECT.
        econs.
        { (* mi-access *)
          i. exploit mi_access; eauto. i.
          assert (DIFFBLOCK_ALLOC: b2 <> Memory.Mem.nextblock mem0_tgt).
          { inv WF.
            ii. exploit Hmap2; eauto.
            i. psimpl. }
          exploit valid_access_malloc_other; eauto.
        }
        { (* mi_memval *)
          i.
          assert (DIFFBLOCK_ALLOC: b2 <> Memory.Mem.nextblock mem0_tgt).
          { inv WF.
            ii. exploit Hmap2; eauto.
            i. psimpl. }
          exploit mi_memval; eauto.
          i. exploit malloc_contents_other; eauto.
          intro CONTENTS.
          rewrite CONTENTS. eauto.
        }
      * inv WF.
        econs; eauto.
        ++ i. exploit Hmap2; eauto. i. psimpl.
        ++ i. exploit Hmap2; eauto. i.
           unfold Memory.Mem.valid_block. psimpl.
        ++ i.
           assert (ALLOC_PRIVATE: b' <> Memory.Mem.nextblock mem0_tgt).
           { ii. subst.
             exploit Hmap2; eauto. i. psimpl. }
           erewrite Memory.Mem.bounds_alloc_other with (b':=b'); try exact ALLOC_PRIVATE; cycle 1.
           { eapply malloc_inv. exact MALLOC. }
           eapply mi_bounds; eauto.
    + econs; eauto.
      * econs; eauto. ss.
        inv MEM. inv SRC. rewrite <- NEXTBLOCK.
        exploit malloc_result; eauto. i. des. psimpl.
      * econs; eauto. ss.
        inv MEM. inv TGT. rewrite <- NEXTBLOCK.
        exploit malloc_result; eauto. i. des. psimpl.
  - (* store - store *)
    esplits; eauto; try reflexivity; try solve_alloc_inject.
    { unfold alloc_private, alloc_private_unary. split.
      - i. subst. ss. des_matchH MC_SOME_SRC; clarify.
      - i. subst. ss. des_matchH MC_SOME_TGT; clarify.
    }
    rename ptr0 into ptr_src. rename gv0 into gv_src.
    rename ptr1 into ptr_tgt. rename gv1 into gv_tgt.
    inv MEM.
    inv STATE_EQUIV_SRC. rename STORE into STORE_SRC.
    unfold mstore in STORE_SRC.
    des_ifs.
    rename b into sb_src. rename i0 into sofs_src. rename Heq into GV2PTR_SRC.
    rename l0 into chunkl_src. rename Heq0 into FLATTEN_SRC.
    inv STATE_EQUIV_TGT. rename STORE into STORE_TGT.
    unfold mstore in STORE_TGT.
    des_ifs.
    rename b into sb_tgt. rename i0 into sofs_tgt. rename Heq into GV2PTR_TGT.
    rename l0 into chunkl_tgt. rename Heq0 into FLATTEN_TGT.
    assert(SPTR_INJECT: InvMem.Rel.inject invmem0 sb_src = Some (sb_tgt, 0) /\ sofs_src = sofs_tgt).
    { inv PTR_INJECT; ss.
      des_ifs.
      match goal with
      | [H: memory_sim.MoreMem.val_inject _ (Values.Vptr _ _) (Values.Vptr _ _) |- _] =>
        inv H
      end.
      inv WF.
      exploit mi_range_block; eauto. i. subst.
      esplits; eauto.
      rewrite Integers.Int.add_zero. reflexivity.
    }
    des. subst.
    assert(CHUNKL_EQ: chunkl_tgt = chunkl_src).
    { destruct CONF as [[CONF_TD _]].
      rewrite CONF_TD in *.
      congruence. }
    rewrite CHUNKL_EQ in *. clear CHUNKL_EQ.

    exploit genericvalues_inject.mem_inj_mstore_aux; eauto. i. des.
    rewrite Z.add_0_r in *.
    assert (MEM_EQ: Mem2' = Mem st1_tgt).
    { congruence. }
    subst.

    econs; eauto.
    + inv SRC.
      econs; eauto.
      * (* Lemma mstore_aux_preserves_wf_Mem *)
        (*       (STORE_SRC : mstore_aux (Mem st0_src) chunkl_src gv_src sb_src (Integers.Int.signed 31 sofs_tgt) = Some (Mem st1_src)) *)
        (*       (WF : MemProps.wf_Mem (CurTargetData conf_src) (Mem st0_src)) *)
        (* : MemProps.wf_Mem (CurTargetData conf_src) (Mem st1_src). *)
        (* we will not prove this *)
        eapply mstore_aux_valid_ptrs_preserves_wf_Mem; eauto.
      * (* PRIVATE *)
        i. exploit PRIVATE; eauto. i. des.
        split; eauto.
        erewrite <- MemProps.nextblock_mstore_aux; eauto.
      * (* PRIVATE_PARENT *)
        i. exploit PRIVATE_PARENT; eauto. i. des.
        split; eauto.
        erewrite <- MemProps.nextblock_mstore_aux; eauto.
      * i. hexploit gv_inject_ptr_public_src; try exact PTR_INJECT; eauto. i.
        exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
        (* b <> sb_src *)
        eapply mstore_aux_preserves_mload_aux_eq; eauto.
        ii. subst.
        exploit PRIVATE_PARENT; eauto. i. des. eauto.
      * rewrite <- NEXTBLOCK. symmetry.
        eapply MemProps.nextblock_mstore_aux; eauto.
    + inv TGT.
      econs; eauto.
      * eapply mstore_aux_valid_ptrs_preserves_wf_Mem; eauto.
      * (* PRIVATE *)
        i. exploit PRIVATE; eauto. i. des.
        split; eauto.
        erewrite <- MemProps.nextblock_mstore_aux; eauto.
      * (* PRIVATE_PARENT *)
        i. exploit PRIVATE_PARENT; eauto. i. des.
        split; eauto.
        erewrite <- MemProps.nextblock_mstore_aux; eauto.
      * i. hexploit gv_inject_ptr_public_tgt; try exact PTR_INJECT; eauto. i.
        exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
        eapply mstore_aux_preserves_mload_aux_eq; eauto.
        ii. subst.
        exploit PRIVATE_PARENT; eauto. i. des. eauto.
      * rewrite <- NEXTBLOCK. symmetry.
        eapply MemProps.nextblock_mstore_aux; eauto.
  - (* store - none *)
    esplits; eauto; try reflexivity; try solve_alloc_inject.
    { unfold alloc_private, alloc_private_unary. split.
      - i. subst. ss. des_matchH MC_SOME_SRC; clarify.
      - i. subst. ss. des_matchH MC_SOME_TGT; clarify.
    }
    inv MEM.
    inv STATE_EQUIV_TGT. rewrite <- MEM_EQ.
    inv STATE_EQUIV_SRC.
    unfold mstore in STORE.
    des_ifs.
    rename Heq into GV2PTR. rename l0 into chunkl. rename Heq0 into FLATTEN.
    econs; eauto.
    + inv SRC.
      exploit PRIVATE; try exact IN. i. des.
      econs; eauto.
      * eapply mstore_aux_valid_ptrs_preserves_wf_Mem; eauto.
      * (* PRIVATE *)
        i. exploit PRIVATE; eauto. i. des.
        split; eauto.
        erewrite <- MemProps.nextblock_mstore_aux; eauto.
      * (* PRIVATE_PARENT *)
        i. exploit PRIVATE_PARENT; eauto. i. des.
        split; eauto.
        erewrite <- MemProps.nextblock_mstore_aux; eauto.
      * i. unfold list_disjoint in *.
        hexploit PRIVATE_DISJOINT; eauto. i.
        exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
        eapply mstore_aux_preserves_mload_aux_eq; eauto.
      * erewrite <- MemProps.nextblock_mstore_aux; eauto.
    + (* inject *)
      inv INJECT.
      econs.
      { (* mi_access *)
        i. exploit mi_access; eauto.
        erewrite mstore_aux_valid_access; eauto. }
      { (* mi_memval *)
        i. exploit mi_memval; eauto.
        { eapply mstore_aux_preserves_perm; eauto. }
        i.
        assert(STORE_DIFFBLOCK: b1 <> b).
        { ii. subst.
          inv SRC.
          exploit PRIVATE; eauto. intros [NOT_PUBLIC _].
          apply NOT_PUBLIC.
          unfold InvMem.Rel.public_src. congruence. }
        assert (GET_ONE: Memory.Mem.getN 1 ofs0 (Maps.PMap.get b1 (Memory.Mem.mem_contents (Mem st0_src))) =
                Memory.Mem.getN 1 ofs0 (Maps.PMap.get b1 (Memory.Mem.mem_contents (Mem st1_src)))).
        { eapply mstore_aux_getN_out; eauto. }
        ss. inv GET_ONE.
        eauto.
      }
    + (* WF *)
      inv WF.
      econs; eauto.
      * erewrite <- MemProps.nextblock_mstore_aux; eauto.
      * i. exploit mi_freeblocks; eauto.
        unfold Memory.Mem.valid_block in *.
        erewrite MemProps.nextblock_mstore_aux; eauto.
      * i. exploit mi_bounds; eauto. i.
        hexploit MemProps.bounds_mstore_aux; try exact STORE.
        intro BEQ_SRC. rewrite <- BEQ_SRC.
        eauto.
  - (* free - free *)
    esplits; eauto; try reflexivity; try solve_alloc_inject.
    { unfold alloc_private, alloc_private_unary. split.
      - i. subst. ss. des_matchH MC_SOME_SRC; clarify.
      - i. subst. ss. des_matchH MC_SOME_TGT; clarify.
    }
    rename ptr0 into ptr_src. rename ptr1 into ptr_tgt.
    inv MEM.
    inv STATE_EQUIV_SRC. rename FREE into FREE_SRC.
    inv STATE_EQUIV_TGT. rename FREE into FREE_TGT.
    specialize (MemProps.free_preserves_wf_Mem (InvMem.Rel.gmax invmem0) _ _ _ _ FREE_SRC). intro WF_SRC.
    specialize (MemProps.free_preserves_wf_Mem (InvMem.Rel.gmax invmem0) _ _ _ _ FREE_TGT). intro WF_TGT.

    unfold free in FREE_SRC. des_ifs.
    rename b into fb_src. rename z into lo_src. rename z0 into hi_src.
    rename Heq into GV2PTR_SRC. rename Heq0 into BOUNDS_SRC.
    unfold free in FREE_TGT. des_ifs.
    rename b into fb_tgt. rename z into lo_tgt. rename z0 into hi_tgt.
    rename Heq into GV2PTR_TGT. rename Heq0 into BOUNDS_TGT.

    assert(FPTR_INJECT: InvMem.Rel.inject invmem0 fb_src = Some (fb_tgt, 0) /\
                                       lo_src = lo_tgt /\ hi_src = hi_tgt).
    { inv PTR_INJECT; ss.
      des_ifs.
      match goal with
      | [H: memory_sim.MoreMem.val_inject _ (Values.Vptr _ _) (Values.Vptr _ _) |- _] =>
        inv H
      end.
      inv WF.
      exploit mi_bounds; eauto. intros BOUNDS.
      rewrite BOUNDS_SRC in BOUNDS.
      rewrite BOUNDS_TGT in BOUNDS.
      inv BOUNDS. esplits; eauto.
      exploit mi_range_block; eauto.
      i. subst. eauto.
    }
    des. subst.
    exploit genericvalues_inject.mem_inj__free; eauto. i. des.
    assert (MEM_EQ: Mem2' = (Mem st1_tgt)).
    { do 2 rewrite Z.add_0_r in *. congruence. }
    subst.
    econs; eauto.
    + inv SRC.
      econs; eauto.
      * (* PRIVATE *)
        i. exploit PRIVATE; eauto. i. des.
        split; eauto.
        erewrite Memory.Mem.nextblock_free; eauto.
      * (* PRIVATE_PARENT *)
        i. exploit PRIVATE_PARENT; eauto. i. des.
        split; eauto.
        erewrite Memory.Mem.nextblock_free; eauto.
      * i. hexploit gv_inject_ptr_public_src; try exact PTR_INJECT; eauto. i.
        exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
        exploit free_preserves_mload_aux_eq; try exact FREE_SRC; eauto.
        exploit PRIVATE_PARENT; eauto. i. des.
        ii. subst. eauto.
      * erewrite Memory.Mem.nextblock_free; eauto.
    + inv TGT.
      econs; eauto.
      * (* PRIVATE *)
        i. exploit PRIVATE; eauto. i. des.
        split; eauto.
        erewrite Memory.Mem.nextblock_free; eauto.
      * (* PRIVATE_PARENT *)
        i. exploit PRIVATE_PARENT; eauto. i. des.
        split; eauto.
        erewrite Memory.Mem.nextblock_free; eauto.
      * i. hexploit gv_inject_ptr_public_tgt; try exact PTR_INJECT; eauto. i.
        exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
        exploit free_preserves_mload_aux_eq; try exact FREE_TGT; eauto.
        exploit PRIVATE_PARENT; eauto. i. des.
        ii. subst. eauto.
      * erewrite Memory.Mem.nextblock_free; eauto.
  - (* none - none *)
    inv STATE_EQUIV_SRC. rewrite <- MEM_EQ. clear MEM_EQ.
    inv STATE_EQUIV_TGT. rewrite <- MEM_EQ. clear MEM_EQ.
    esplits; eauto; try reflexivity; try solve_alloc_inject.
    unfold alloc_private, alloc_private_unary. split.
    + i. subst. ss. des_matchH MC_SOME_SRC; clarify.
    + i. subst. ss. des_matchH MC_SOME_TGT; clarify.
Qed.

(* invariant *)

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

(* TODO: jeehoon.kang *)
Lemma unique_const_diffblock
      conf st x gv_x c gv_c (* S ty *)
      (UNIQUE_X : InvState.Unary.sem_unique conf st x)
      (INV_PTR : lookupAL GenericValue (Locals (EC st)) x = Some gv_x)
      (* (WF_CONST: wf_const S conf.(CurTargetData) c ty) *)
      (FORGET_PTR : const2GV (CurTargetData conf) (Globals conf) c = Some gv_c)
  : InvState.Unary.sem_diffblock conf gv_c gv_x.
Proof.
(* exploit MemProps.const2GV_valid_ptrs; eauto. *)
(* { admit. } *)
(* inv UNIQUE_X. *)
(* i. unfold InvState.Unary.sem_diffblock. des_ifs. *)
(* ii. subst.  *)
(* we can use the lemma below if we have MemProps.wf_globals and wf_const *)
(* MemProps.const2GV_valid_ptrs *)
(* wf_const requires a system.. *)
Admitted.

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
    intro UNIQUE_X.
    unfold Invariant.values_diffblock_from_unique in *.
    destruct v_forget as [x_forget| c_forget]; ss.
    + inv UNIQUE_X.
      assert (IDS_NEQ: x_forget <> x_inv).
      { unfold IdT.lift in *.
        match goal with
        | [H: _ <> _ |- _] =>
          ii; subst; apply H; reflexivity
        end. }
      apply diffblock_implies_noalias.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      apply diffblock_comm.
      eapply LOCALS; eauto.
    + apply diffblock_implies_noalias.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      eapply unique_const_diffblock; eauto.
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
    intro UNIQUE_X.

    unfold Invariant.values_diffblock_from_unique in *.
    destruct vt_inv as [[[] x_inv]| c_inv]; ss.
    + inv UNIQUE_X.
      assert (IDS_NEQ: x_forget <> x_inv).
      { unfold IdT.lift in *.
        match goal with
        | [H: _ <> _ |- _] =>
          ii; subst; apply H; reflexivity
        end. }
      apply diffblock_implies_noalias.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      
      eapply LOCALS; eauto.
    + apply diffblock_implies_noalias.
      apply diffblock_comm.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      eapply unique_const_diffblock; eauto.
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
Qed.

Lemma forget_memory_is_noalias_exprpair
      conf st1 invst0 invmem0 inv1 mem0
      p a e2
      vt_inv ty_inv gv_inv
      v_forget ty_forget gv_forget
      (STATE : InvState.Unary.sem conf (mkState st1.(EC) st1.(ECS) mem0) invst0 invmem0 inv1)
      (PAIR : p = (Expr.load vt_inv ty_inv a, e2) \/ p = (e2, Expr.load vt_inv ty_inv a))
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
      conf st0 mem1 invst0 invmem0 inv1 cmd mc
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv1)
      (MC_SOME : mem_change_of_cmd conf cmd st0.(EC).(Locals) = Some mc)
      (STATE_EQUIV : states_mem_change conf st0.(Mem) mem1 mc)
  : <<SEM_EXPR_EQ: forall p e1 e2
             (PAIR: p = (e1, e2) \/ p = (e2, e1))
             (FORGET_MEMORY : ExprPairSet.In p
                                             (Invariant.lessdef
                                                (ForgetMemory.unary
                                                   (Cmd.get_def_memory cmd)
                                                   (Cmd.get_leaked_ids_to_memory cmd)
                                                   inv1))),
        InvState.Unary.sem_expr conf st0 invst0 e1 =
        InvState.Unary.sem_expr conf (mkState st0.(EC) st0.(ECS) mem1) invst0 e1>>.
Proof.
  ii.
  destruct mc.
  - (* alloc *)
    destruct cmd; ss; des_ifs.
    destruct e1; ss.
    + erewrite sem_list_valueT_eq_locals with (st1:=mkState st0.(EC) st0.(ECS) mem1); ss.
    + erewrite sem_valueT_eq_locals with (st1:=mkState st0.(EC) st0.(ECS) mem1); ss.
      des_ifs.
      inv STATE_EQUIV.
      destruct (GV2ptr conf.(CurTargetData) conf.(CurTargetData).(getPointerSize) g) eqn:GV2PTR; cycle 1.
      { unfold mload. rewrite GV2PTR. reflexivity. }
      destruct v0;
        try by unfold mload; rewrite GV2PTR; eauto.
      eapply malloc_preserves_mload_other_eq; eauto.
      ii. subst.
      inv STATE.
      clear PAIR.
      exploit malloc_result; eauto. i. des. subst.
      destruct v.
      { (* id case *)
        destruct x as [[] x].
        - (* physical *)
          ss. unfold InvState.Unary.sem_idT in *. ss.
          exploit WF_LOCAL; eauto. i.
          exploit MemProps.GV2ptr_preserves_valid_ptrs; eauto. i.
          ss. des. psimpl.
        - (* previous *)
          ss. unfold InvState.Unary.sem_idT in *. ss.
          exploit WF_PREVIOUS; eauto. i.
          exploit MemProps.GV2ptr_preserves_valid_ptrs; eauto. i.
          ss. des. psimpl.
        - (* ghost *)
          ss. unfold InvState.Unary.sem_idT in *. ss.
          exploit WF_GHOST; eauto. i.
          exploit MemProps.GV2ptr_preserves_valid_ptrs; eauto. i.
          ss. des. psimpl.
      }
      { (* const case : need wf_const *)
        admit. (* c is evaluated into a global pointer, and GV2ptr cannot be mb *)
      }
  - (* store *)
    destruct cmd; ss; des_ifs.
    inv STATE_EQUIV.
    destruct e1; ss.
    + erewrite sem_list_valueT_eq_locals with (st1:=mkState st0.(EC) st0.(ECS) mem1); ss.
    + erewrite sem_valueT_eq_locals with (st1:=mkState st0.(EC) st0.(ECS) mem1); ss.
      des_ifs.
      
      unfold ForgetMemory.unary, Cmd.get_leaked_ids_to_memory in *. ss.
      des_ifs; ss.
      * apply ExprPairSetFacts.filter_iff in FORGET_MEMORY; try by solve_compat_bool.
        destruct FORGET_MEMORY as [FORGET_MEMORY_IN FORGET_MEMORY_NOALIAS].
        symmetry. eapply mstore_noalias_mload; eauto.
        eapply forget_memory_is_noalias_exprpair; eauto.
        instantiate (2:= st0.(Mem)).
        destruct st0. ss. exact STATE.
      * apply ExprPairSetFacts.filter_iff in FORGET_MEMORY; try by solve_compat_bool.
        destruct FORGET_MEMORY as [FORGET_MEMORY_IN FORGET_MEMORY_NOALIAS].
        symmetry. eapply mstore_noalias_mload; eauto.
        eapply forget_memory_is_noalias_exprpair; eauto.
        instantiate (2:= st0.(Mem)).
        destruct st0. ss. exact STATE.
  - (* free *)
    destruct cmd; ss; des_ifs.
    rename Heq into GET_VALUE.
    inv STATE_EQUIV.
    destruct e1; ss.
    + erewrite sem_list_valueT_eq_locals with (st1:=mkState st0.(EC) st0.(ECS) mem1); ss.
    + erewrite sem_valueT_eq_locals with (st1:=mkState st0.(EC) st0.(ECS) mem1); ss.
      des_ifs.
      apply ExprPairSetFacts.filter_iff in FORGET_MEMORY; try by solve_compat_bool.
      destruct FORGET_MEMORY as [FORGET_MEMORY_IN FORGET_MEMORY_NOALIAS].

      symmetry. eapply mfree_noalias_mload; eauto.
      eapply forget_memory_is_noalias_exprpair; eauto.
      instantiate (2:= st0.(Mem)).
      destruct st0. exact STATE.
  - (* none *)
    inv STATE_EQUIV. destruct st0; eauto.
Admitted.

Lemma forget_memory_maydiff_preserved
      conf_src mem1_src st0_src mem_change_src def_mem_src leaks_src
      conf_tgt mem1_tgt st0_tgt mem_change_tgt def_mem_tgt leaks_tgt
      invst0 invmem0 inv0
      (MEM_EQUIV_SRC : states_mem_change conf_src st0_src.(Mem) mem1_src mem_change_src)
      (MEM_EQUIV_TGT : states_mem_change conf_tgt st0_tgt.(Mem) mem1_tgt mem_change_tgt)
      (MAYDIFF : forall id : Tag.t * id,
          IdTSet.mem id (Invariant.maydiff inv0) = false ->
          InvState.Rel.sem_inject (mkState st0_src.(EC) st0_src.(ECS) mem1_src)
                                  (mkState st0_tgt.(EC) st0_tgt.(ECS) mem1_tgt)
                                  invst0 (InvMem.Rel.inject invmem0) id)
  : <<RES: forall id : Tag.t * id,
      IdTSet.mem id (Invariant.maydiff (ForgetMemory.t def_mem_src def_mem_tgt leaks_src leaks_tgt inv0)) = false ->
      InvState.Rel.sem_inject (mkState st0_src.(EC) st0_src.(ECS) mem1_src)
                              (mkState st0_tgt.(EC) st0_tgt.(ECS) mem1_tgt)
                              invst0 (InvMem.Rel.inject invmem0) id>>.
Proof.
  ii.
  assert (DROP_FORGET_MEMORY:IdTSet.mem id0 (Invariant.maydiff inv0) = false).
  { destruct def_mem_src; destruct def_mem_tgt; ss. }
  exploit MAYDIFF; eauto.
Qed.

Lemma forget_memory_sem_unary
      conf st0 mem1 mc cmd
      inv1 invst0 invmem0
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv1)
      (MC_SOME : mem_change_of_cmd conf cmd st0.(EC).(Locals) = Some mc)
      (STATE_MC : states_mem_change conf st0.(Mem) mem1 mc)
  : InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) mem1) invst0 invmem0
                       (ForgetMemory.unary
                          (Cmd.get_def_memory cmd)
                          (Cmd.get_leaked_ids_to_memory cmd)
                          inv1).
Proof.
  hexploit exprpair_forget_memory_disjoint; eauto. intro EXPR_EQ. des.
  unfold ForgetMemory.unary, Cmd.get_leaked_ids_to_memory.
  destruct mc; cycle 3.
  { destruct cmd; ss; des_ifs;
      inv STATE_MC; destruct st0; eauto. }
  - (* alloc *)
    destruct cmd; ss; des_ifs.
    inv STATE_MC.
    inv STATE.

    econs; eauto.
    + ii.
      destruct x.
      erewrite <- EXPR_EQ in VAL1; try left; eauto. i. des.
      exploit LESSDEF; eauto. i. des. ss.
      esplits; eauto.
      erewrite <- EXPR_EQ; eauto.
    + inv NOALIAS. econs; eauto.
    + ii.
      exploit UNIQUE; eauto.

      intro UNIQUE_X.
      inv UNIQUE_X.
      econs; eauto. i. ss.
      exploit MemProps.malloc_preserves_mload_inv; eauto. i. des.
      * eapply MEM; eauto.
      * unfold InvState.Unary.sem_diffblock. des_ifs.
        ii. subst.
        destruct val'.
        { ss. }
        { ss. destruct p. des_ifs. ss.
          exploit x1.
          - left. reflexivity.
          - inversion 1. }
    + ss. eapply MemProps.malloc_preserves_wf_lc_in_tail; eauto.
    + ss. eapply MemProps.malloc_preserves_wf_lc_in_tail; eauto.
    + ss. eapply MemProps.malloc_preserves_wf_lc_in_tail; eauto.
  - (* store *)
    destruct cmd; ss; des_ifs.
    { (* id *)
      destruct value1; ss.
      rename value2 into v_sptr.
      rename Heq0 into SVAL.
      rename Heq1 into SPTR.
      inv STATE_MC.
      inv STATE.
      econs.
      + ii. ss.
        destruct x.
        erewrite <- EXPR_EQ in VAL1; try left; eauto.
        exploit LESSDEF; eauto.
        { apply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool. des. eauto. }
        i. des.
        erewrite EXPR_EQ in VAL2; try right; eauto.
      + inv NOALIAS.
        econs; eauto.
      + ii. ss. clarify.
        rewrite AtomSetFacts.remove_iff in *. des.
        exploit UNIQUE; eauto.
        intro UNIQUE_X.
        eapply mstore_register_leak_no_unique; eauto.
      + ss.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + eauto.
    }
    { destruct value1; ss.
      rename value2 into v_sptr.
      rename Heq0 into SVAL.
      rename Heq1 into SPTR.
      inv STATE_MC.
      inv STATE.
      econs.
      + ii. ss.
        destruct x.
        erewrite <- EXPR_EQ in VAL1; try left; eauto.
        exploit LESSDEF; eauto.
        { apply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool. des. eauto. }
        i. des.
        erewrite EXPR_EQ in VAL2; try right; eauto.
      + inv NOALIAS.
        econs; eauto.
      + ii. ss.
        exploit UNIQUE; eauto.
        intro UNIQUE_X.
        eapply mstore_const_leak_no_unique; eauto.
      + ss.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + eauto.
    }
  - destruct cmd; ss; des_ifs.
    inv STATE_MC.
    inv STATE.
    econs; eauto.
    + ii.
      destruct x.
      erewrite <- EXPR_EQ in VAL1; try left; eauto.
      exploit LESSDEF; eauto.
      { apply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool. des. eauto. }
      i. des.
      erewrite EXPR_EQ in VAL2; try right; eauto.
    + inv NOALIAS.
      econs; eauto.
    + ii. ss.
      exploit UNIQUE; eauto.
      intro UNIQUE_X.
      inv UNIQUE_X.
      econs; eauto.
      i. exploit MEM; eauto.
      ss.
      eapply MemProps.free_preserves_mload_inv; eauto.
    + ss. eapply MemProps.free_preserves_wf_lc; eauto.
    + ss. eapply MemProps.free_preserves_wf_lc; eauto.
    + ss. eapply MemProps.free_preserves_wf_lc; eauto.
Qed.

Lemma forget_memory_sem
      conf_src st0_src mem1_src mc_src cmd_src
      conf_tgt st0_tgt mem1_tgt mc_tgt cmd_tgt
      inv0 invst0 invmem0
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MC_SOME_SRC : mem_change_of_cmd conf_src cmd_src st0_src.(EC).(Locals) = Some mc_src)
      (MC_SOME_TGT : mem_change_of_cmd conf_tgt cmd_tgt st0_tgt.(EC).(Locals) = Some mc_tgt)
      (STATE_MC_SRC : states_mem_change conf_src st0_src.(Mem) mem1_src mc_src)
      (STATE_MC_TGT : states_mem_change conf_tgt st0_tgt.(Mem) mem1_tgt mc_tgt)
  : InvState.Rel.sem conf_src conf_tgt
                     (mkState st0_src.(EC) st0_src.(ECS) mem1_src)
                     (mkState st0_tgt.(EC) st0_tgt.(ECS) mem1_tgt)
                     invst0 invmem0
                     (ForgetMemory.t (Cmd.get_def_memory cmd_src)
                                     (Cmd.get_def_memory cmd_tgt)
                                     (Cmd.get_leaked_ids_to_memory cmd_src)
                                     (Cmd.get_leaked_ids_to_memory cmd_tgt)
                                     inv0).
Proof.
  inv STATE.
  unfold ForgetMemory.t.
  econs.
  - eapply forget_memory_sem_unary; try exact SRC; eauto.
  - eapply forget_memory_sem_unary; try exact TGT; eauto.
  - eapply forget_memory_maydiff_preserved; eauto.
Qed.

Lemma inv_state_sem_monotone_wrt_invmem
      invmem0 invmem1 invst0 inv1
      conf_src st_src
      conf_tgt st_tgt
      (MEM_LE:InvMem.Rel.le invmem0 invmem1)
      (PRIVATE_PRESERVED_SRC: forall p, In p invmem0.(InvMem.Rel.src).(InvMem.Unary.private) ->
                                   In p invmem1.(InvMem.Rel.src).(InvMem.Unary.private))
      (PRIVATE_PRESERVED_TGT: forall p, In p invmem0.(InvMem.Rel.tgt).(InvMem.Unary.private) ->
                                   In p invmem1.(InvMem.Rel.tgt).(InvMem.Unary.private))
      (STATE:InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem0 inv1)
  : InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem1 inv1.
Proof.
  destruct STATE as [STATE_SRC STATE_TGT STATE_MAYDIFF].
  inv MEM_LE.
  econs.
  - inv SRC.
    inv STATE_SRC.
    econs; eauto.
    + ii. exploit PRIVATE; eauto. i.
      des_ifs.
      apply PRIVATE_PRESERVED_SRC. eauto.
    + rewrite <- UNIQUE_PARENT_EQ. eauto.
  - inv TGT.
    inv STATE_TGT.
    econs; eauto.
    + ii. exploit PRIVATE; eauto. i.
      des_ifs.
      apply PRIVATE_PRESERVED_TGT. eauto.
    + rewrite <- UNIQUE_PARENT_EQ. eauto.
  - i. hexploit STATE_MAYDIFF; eauto.
    intros SEM_INJECT.
    ii. exploit SEM_INJECT; eauto. i. des.
    esplits; eauto.
    eapply genericvalues_inject.gv_inject_incr; eauto.
Qed.

Lemma forget_memory_sound
      m_src conf_src st0_src st1_src cmd_src cmds_src evt_src
      m_tgt conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt evt_tgt
      invst0 invmem0 inv0
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
  : exists invmem1,
      <<ALLOC_INJECT: alloc_inject conf_src conf_tgt st0_src st0_tgt
                                   st1_src st1_tgt cmd_src cmd_tgt invmem1>> /\
      <<ALLOC_PRIVATE: alloc_private conf_src conf_tgt cmd_src cmd_tgt st0_src st0_tgt st1_src st1_tgt invmem1>> /\
      <<STATE: InvState.Rel.sem conf_src conf_tgt
                                (mkState st0_src.(EC) st0_src.(ECS) st1_src.(Mem))
                                (mkState st0_tgt.(EC) st0_tgt.(ECS) st1_tgt.(Mem))
                                invst0 invmem1
                                (ForgetMemory.t
                                   (Cmd.get_def_memory cmd_src)
                                   (Cmd.get_def_memory cmd_tgt)
                                   (Cmd.get_leaked_ids_to_memory cmd_src)
                                   (Cmd.get_leaked_ids_to_memory cmd_tgt)
                                   inv0) >> /\
      <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
      <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  assert (STATE2:= STATE).
  inv STATE2.
  exploit step_mem_change; try exact SRC; eauto.
  { inv MEM. exact SRC0. }
  i. des.
  exploit step_mem_change; try exact TGT; eauto.
  { inv MEM. exact TGT0. }
  i. des.
  exploit inject_invmem; try exact INJECT_EVENT; eauto. i. des.
  esplits; eauto.

  eapply forget_memory_sem; eauto.

  eapply inv_state_sem_monotone_wrt_invmem; eauto.
  (* - eapply inv_mem_sem_monotone_wrt_invmem; eauto. *)
Qed.
