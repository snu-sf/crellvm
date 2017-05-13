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
Require Import TODOProof.
Import Memory.

Set Implicit Arguments.

(* TODO: move *)
Lemma some_injective A (a b:A):
  Some a = Some b -> a = b.
Proof.
  congruence.
Qed.

Inductive mem_change : Type :=
| mem_change_alloca
    (def_var:id) (ty:typ) (s:sz) (gn:GenericValue) (a:align)
| mem_change_store
    (ptr:GenericValue) (ty:typ) (gv:GenericValue) (a:align)
| mem_change_free
    (ptr:GenericValue)
| mem_change_none
.

Inductive mem_change_inject (conf conf_tgt:Config) invmem: mem_change -> mem_change -> Prop :=
| mem_change_inject_alloca_alloca
    gsz gn0 gn1 a
    ty dv
    (N_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gn0 gn1)
  : mem_change_inject conf conf_tgt invmem
                      (mem_change_alloca dv ty gsz gn0 a)
                      (mem_change_alloca dv ty gsz gn1 a)
| mem_change_inject_alloca_none
    gsz gn a ty dv
  : mem_change_inject conf conf_tgt invmem
                      (mem_change_alloca dv ty gsz gn a)
                      mem_change_none
| mem_change_inject_none_alloca
    gsz gn a ty dv
  : mem_change_inject conf conf_tgt
                      invmem mem_change_none
                      (mem_change_alloca dv ty gsz gn a)
| mem_change_inject_store_store
    ptr0 ptr1 gv0 gv1 ty a
    (PTR_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) ptr0 ptr1)
    (VAL_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gv0 gv1)
  : mem_change_inject conf conf_tgt invmem
                      (mem_change_store ptr0 ty gv0 a)
                      (mem_change_store ptr1 ty gv1 a)
| mem_change_inject_store_nop
    ptr gv ty a
    (DISJOINT: forall b (GV2BLOCKS: In b (GV2blocks ptr)),
        <<NOT_PUBLIC: ~ InvMem.Rel.public_src invmem.(InvMem.Rel.inject) b>> /\
        <<PARENT_DISJOINT: ~ In b invmem.(InvMem.Rel.src).(InvMem.Unary.private_parent)>>)
  : mem_change_inject conf conf_tgt invmem
                      (mem_change_store ptr ty gv a)
                      mem_change_none
| mem_change_inject_free
    ptr0 ptr1
    (PTR_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) ptr0 ptr1)
  : mem_change_inject conf conf_tgt invmem
                      (mem_change_free ptr0)
                      (mem_change_free ptr1)
| mem_change_inject_none
  : mem_change_inject conf conf_tgt invmem
                      mem_change_none
                      mem_change_none
.

Inductive states_mem_change conf mem0 mem1: mem_change -> Prop :=
| states_mem_change_alloca
    ty bsz gn a dv mb
    (ALLOCA: alloca conf.(CurTargetData) mem0 bsz gn a = Some (mem1, mb))
  : states_mem_change conf mem0 mem1 (mem_change_alloca dv ty bsz gn a)
| states_mem_change_store
    ptr ty gv a
    (VALID_PTRS: MemProps.valid_ptrs mem0.(Mem.nextblock) gv)
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
    | Some tsz, Some gn => Some (mem_change_alloca x ty tsz gn a)
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

Definition alloc_private_unary (conf: Config) conf' cmd cmd' st public private_parent: Prop :=
  forall x ty v a lc'
    (ALLOCA: cmd = insn_alloca x ty v a)
    (NOP: mem_change_of_cmd conf' cmd' lc' = Some mem_change_none),
  exists gptr,
    <<PTR: lookupAL _ st.(EC).(Locals) x = Some gptr>> /\
    (forall b (IN: In b (GV2blocks gptr)),
        <<PRIVATE_BLOCK: InvMem.private_block (Mem st) public b >> /\
        <<PARENT_DISJOINT: ~ In b private_parent >>).

Definition alloc_private conf_src conf_tgt cmd_src cmd_tgt
           (st0_src st0_tgt: State) st1_src st1_tgt invmem : Prop :=
  alloc_private_unary
    conf_src conf_tgt cmd_src cmd_tgt st1_src
    (InvMem.Rel.public_src invmem.(InvMem.Rel.inject))
    invmem.(InvMem.Rel.src).(InvMem.Unary.private_parent) /\
  alloc_private_unary
    conf_tgt conf_src cmd_tgt cmd_src st1_tgt
    (InvMem.Rel.public_tgt invmem.(InvMem.Rel.inject))
    invmem.(InvMem.Rel.tgt).(InvMem.Unary.private_parent).

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
    alloc_inject_unary conf_src st1_src x st0_src.(Mem).(Mem.nextblock) /\
    alloc_inject_unary conf_tgt st1_tgt x st0_tgt.(Mem).(Mem.nextblock) /\
    invmem1.(InvMem.Rel.inject) st0_src.(Mem).(Mem.nextblock) =
    Some (st0_tgt.(Mem).(Mem.nextblock), 0).

(* Lemma getOperandValue_wf_lc_valid_ptrs *)
(*       TD lc gl *)
(*       mem v gv *)
(*       (VAL : getOperandValue TD v lc gl = Some gv) *)
(*       (WF_LOCAL : MemProps.wf_lc mem lc) *)
(*   : MemProps.valid_ptrs mem.(Mem.nextblock) gv. *)
(* Proof. *)
(*   apply WF_LOCAL in VAL. *)
(* (* hope MemProps.operand__lt_nextblock helps *) *)
(* Adm-itted. *)

(* not high priority for proof *)

Lemma mstore_never_produce_new_ptr
      TD mem0 mem1
      sptr sty val sa nptr
      (MEM_NOALIAS: forall ptr ty a gv,
          mload TD mem0 ptr ty a = Some gv ->
          MemProps.no_alias nptr gv)
      (STORE: mstore TD mem0 sptr sty val sa = Some mem1)
      (NOALIAS: MemProps.no_alias nptr val)
  : forall ptr ty a gv,
    mload TD mem1 ptr ty a = Some gv ->
    MemProps.no_alias nptr gv
.
Proof.
  unfold mstore in *.
  des_ifs.
  eapply TODOProof.mstore_aux_never_produce_new_ptr; eauto.
Qed.

Lemma getOperandValue_not_unique_parent
      conf st invst invmem gmax public inv v gv
      sys fdef ty
      (STATE: InvState.Unary.sem conf st invst invmem gmax public inv)
      (MEM: InvMem.Unary.sem conf gmax public st.(Mem) invmem)
      (WF_VALUE: wf_value sys
                          (module_intro conf.(CurTargetData).(fst)
                                        conf.(CurTargetData).(snd)
                                        conf.(CurProducts))
                          fdef v ty)
      (GETOP: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gv)
  : InvMem.gv_diffblock_with_blocks conf gv invmem.(InvMem.Unary.unique_parent).
Proof.
  ii.
  destruct v as [x | c]; ss.
  - (* inv MEM. *)
    (* exploit sublist_In; eauto. intro IN_PRIV. *)
    inv STATE.
    exploit UNIQUE_PARENT_LOCAL; eauto.
  - inv MEM.
    exploit UNIQUE_PARENT_GLOBALS; eauto. intro GT_GMAX.
    inv STATE. ss.
    inv WF_VALUE.
    exploit MemProps.const2GV_valid_ptrs; eauto.
    { eapply TODOProof.wf_globals_eq; eauto. }
    { rewrite <- surjective_pairing. eauto. }
    intro LT_GMAX_1.
    generalize ING LT_GMAX_1.
    generalize b GT_GMAX.
    clear.
    induction gv; ss.
    i. unfold GV2blocks in *.
    destruct a.
    destruct v; ss;
      exploit IHgv; eauto.
    + des; eauto.
      subst.
      exploit Plt_succ_inv.
      { rewrite <- Pplus_one_succ_r in *. eauto. }
      i. des.
      * generalize (Plt_trans gmax b gmax). intros TRANS.
        exploit TRANS; eauto. intros CONT.
        apply Pos.lt_irrefl in CONT. contradiction.
      * subst.
        apply Pos.lt_irrefl in GT_GMAX. contradiction.
    + des; eauto.
Qed.

Lemma mstore_never_produce_new_ptr'
      conf mem0 mem1
      sptr sty val sa b
      (MEM_NOALIAS: forall ptr ty a gv,
          mload conf.(CurTargetData) mem0 ptr ty a = Some gv ->
          ~ In b (GV2blocks gv))
      (STORE: mstore conf.(CurTargetData) mem0 sptr sty val sa = Some mem1)
      (NOALIAS: ~ In b (GV2blocks val))
  : forall ptr ty a gv,
    mload conf.(CurTargetData) mem1 ptr ty a = Some gv ->
    ~ In b (GV2blocks gv).
Proof.
  i. hexploit mstore_never_produce_new_ptr; eauto.
  { instantiate (1:= [(Values.Vptr b (Integers.Int.repr 31 0), AST.Mint 31)]).
    i. hexploit MEM_NOALIAS; eauto. i.
    eapply vellvm_no_alias_is_diffblock.
    instantiate (1:= conf).
    ii. ss. des; eauto.
    subst. eauto. }
  { eapply vellvm_no_alias_is_diffblock.
    instantiate (1:= conf).
    ii. ss. des; eauto.
    subst. eauto. }
  ii. rewrite (vellvm_no_alias_is_diffblock conf) in *.
  unfold InvState.Unary.sem_diffblock in *.
  unfold list_disjoint in *.
  eapply H0; eauto. ss. eauto.
Qed.

Lemma step_mem_change
      st0 st1 invst0 invmem0 inv0
      cmd cmds
      conf evt gmax public
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 gmax public inv0)
      (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0)
      (CMD: st0.(EC).(CurCmds) = cmd::cmds)
      (NONCALL: Instruction.isCallInst cmd = false)
      (NONMALLOC: isMallocInst cmd = false)
      (STEP: sInsn conf st0 st1 evt)
  : <<UNIQUE_PARENT_MEM:
      forall mptr typ align val'
        (LOAD: mload conf.(CurTargetData) st1.(Mem) mptr typ align = Some val'),
        InvMem.gv_diffblock_with_blocks conf val' invmem0.(InvMem.Unary.unique_parent)>> /\
        exists mc,
          <<MC_SOME: mem_change_of_cmd conf cmd st0.(EC).(Locals) = Some mc>> /\
          <<STATE_EQUIV: states_mem_change conf st0.(Mem) st1.(Mem) mc>>.
Proof.
  assert (MEM':=MEM).
  inv MEM'.
  inv STEP; destruct cmd; ss; clarify;
    try by esplits; ss; econs; eauto.
  - split.
    + ii. eapply UNIQUE_PARENT_MEM; eauto.
      eapply MemProps.free_preserves_mload_inv; eauto.
    + esplits; ss.
      * des_ifs.
      * econs; eauto.
  - split.
    + ii.
      exploit MemProps.alloca_preserves_mload_inv; eauto. i. des.
      { eapply UNIQUE_PARENT_MEM; eauto. }
      { ss.
        eapply InvState.Unary.undef_diffblock; eauto.
        eapply {|
            CurSystem := S;
            CurTargetData := TD;
            CurProducts := Ps;
            Globals := gl;
            FunTable := fs |}.
      }
    + esplits; ss.
      * des_ifs.
      * econs; eauto.
  - assert (BLOCK_IN_FDEF: blockInFdefB B F).
    { exact (SF_ADMIT "wf_EC"). }
    assert (INSN_IN_BLOCK: insnInBlockB (insn_cmd (insn_store id5 typ5 value1 value2 align5)) B).
    { exact (SF_ADMIT "wf_EC"). }
    split.
    + ii.
      exploit (mstore_never_produce_new_ptr' {| CurSystem := S;
                                                CurTargetData := TD;
                                                CurProducts := Ps;
                                                Globals := gl;
                                                FunTable := fs |}); eauto.
      { i. hexploit UNIQUE_PARENT_MEM; eauto. }
      hexploit getOperandValue_not_unique_parent.
      { eauto. }
      { eauto. }
      { inv STATE. ss.
        exploit WF_INSNS; eauto.
        { split; eauto.
          instantiate (1:= insn_cmd _). eauto. }
        intro WF_INSN. des.
        inv WF_INSN.
        apply H10.
      }
      { instantiate (1 := gv1). eauto. }
      ss. clarify.
      unfold InvMem.gv_diffblock_with_blocks. eauto.
    + esplits; ss.
      * des_ifs.
      * econs; eauto.
        inv STATE. ss.
        exploit WF_INSNS.
        { split; eauto.
          instantiate (1:= insn_cmd _). eauto. }
        intros WF_INSN. des. inv WF_INSN.
        destruct value1 as [x | c]; ss.
        { exploit WF_LOCAL; eauto. }
        { inv H10.
          exploit MemProps.const2GV_valid_ptrs; eauto.
          { eapply TODOProof.wf_globals_eq; eauto. }
          { rewrite <- surjective_pairing. eauto. }
          i. inv MEM. ss.
          inv WF0.
          eapply MemProps.valid_ptrs__trans; eauto.
          rewrite <- Pplus_one_succ_r.
          apply Pos.le_succ_l. eauto.
        }
Qed.

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
  unfold is_true in *.
  (* rewrite <- IdTSetFacts.mem_iff in *. *)

  econs. ii.
  exploit PRIVATE; eauto.
  { eapply IdTSet.mem_2; eauto. }
  { ss. }
  ii; des.
  inv PRIVATE_BLOCK.
  splits; ss.
Qed.

(* lemmas for alloca *)
Lemma alloca_result
      TD mem mem' sz gn a mb
      (ALLOCA: alloca TD mem sz gn a = Some (mem', mb))
  : <<ALLOC_BLOCK: mb = mem.(Mem.nextblock)>> /\
    <<NEXT_BLOCK: mem'.(Mem.nextblock) = Pos.succ mem.(Mem.nextblock)>>
.
Proof.
  unfold alloca in *.
  abstr (match GV2int TD Size.ThirtyTwo gn with
            | Some n => Size.to_Z sz * n
            | None => 0
            end) hi.
  des_ifs. unfold Datatypes.option_map, flip in *. des_ifs.
  expl Mem.alloc_result. clarify.
  splits; ss.
  erewrite Mem.nextblock_drop; eauto.
  eapply Mem.nextblock_alloc; eauto.
Qed.

Ltac u_alloca := MemProps.u_alloca; des_ifs_safe.

Lemma valid_access_alloca_inv
      TD mem0 mem1 bsz gn a b mb p chunk ofs
      (ALLOCA: alloca TD mem0 bsz gn a = Some (mem1, mb))
      (VALID: Mem.valid_access mem1 chunk b ofs p)
  : if Values.eq_block b mb
    then 0 <= ofs /\
         ofs + Memdata.size_chunk chunk <=
         Size.to_Z bsz * get_or_else (GV2int TD Size.ThirtyTwo gn) 0 /\
         (Memdata.align_chunk chunk | ofs) /\
         Memtype.perm_order Memtype.Writable p
    else Mem.valid_access mem0 chunk b ofs p.
Proof.
  u_alloca.
  rename mem1 into mem2.
  rename m into mem1.
  dup VALID.
  eapply Mem.valid_access_drop_2 in VALID; eauto.
  exploit Mem.valid_access_alloc_inv; eauto; []; i; des.
  destruct (Values.eq_block b mb); ss. clarify.
  assert(PERM: Memtype.perm_order Memtype.Writable p).
  { destruct p; try econs.
    exfalso.
    eapply Mem.valid_access_perm in VALID. des.
    hexploit Mem.perm_drop_2; eauto.
    { split; eauto.
      expl Memdata.size_chunk_pos. instantiate (1:= chunk) in size_chunk_pos.
      apply Z.gt_lt_iff in size_chunk_pos.
      omega.
    }
    { eapply Mem.valid_access_perm; eauto. }
    intro CONTR. inv CONTR.
  }
  des_ifs; des; esplits; ss.
  rewrite Z.mul_0_r in *. eauto.
Unshelve.
{ by econs. }
{ by econs. }
Qed.

Lemma valid_access_alloca_same
      TD mem0 mem1 bsz gn a mb p chunk ofs
      (ALLOCA: alloca TD mem0 bsz gn a = Some (mem1, mb))
      (OFS: 0 <= ofs /\
               ofs + Memdata.size_chunk chunk <=
               Size.to_Z bsz *
               (get_or_else (GV2int TD Size.ThirtyTwo gn) 0) /\
               (Memdata.align_chunk chunk | ofs) /\
               (Memtype.perm_order Memtype.Writable p))
  : Mem.valid_access mem1 chunk mb ofs p.
Proof.
  unfold alloca in *.
  des_ifs; des; ss.
  - u_alloca.
    eapply Mem.valid_access_drop_1; eauto.
    eapply Mem.valid_access_implies;
      try apply Memtype.perm_F_any.
    eapply Mem.valid_access_alloc_same; eauto.
  - rewrite Z.mul_0_r in *.
    specialize (Memdata.size_chunk_pos chunk). i.
    omega.
Qed.

Lemma valid_access_alloca_other
      TD mem0 bsz gn a mem1 mb b' ofs p chunk
      (ALLOCA: alloca TD mem0 bsz gn a = Some (mem1, mb))
      (VALID: Mem.valid_access mem0 chunk b' ofs p)
  : Mem.valid_access mem1 chunk b' ofs p.
Proof.
  unfold alloca in *.
  u_alloca.
  assert(DIFFBLOCK: b' <> mb).
  { ii. clarify.
    eapply Mem.valid_access_implies in VALID; [
      apply Mem.valid_access_valid_block in VALID|econs]; [].
    apply Mem.alloc_result in Heq. clarify.
    eapply Plt_irrefl; eauto.
  }
  eapply Mem.valid_access_drop_1; try eassumption.
  { left. ss. }
  rename mem1 into mem2.
  rename m into mem1.
  eapply Mem.valid_access_alloc_other; eauto.
Qed.

Lemma drop_perm_preserves_mem_contents
      m0 b lo hi p m1
      (DROP: Mem.drop_perm m0 b lo hi p = Some m1)
  :
    <<EQ: Mem.mem_contents m0 = Mem.mem_contents m1>>
.
Proof.
  unfold Mem.drop_perm in *.
  des_ifs.
Qed.

Lemma alloca_contents_same
      TD mem0 mem1 gsz gn a
      mb ofs
      (ALLOCA: alloca TD mem0 gsz gn a = Some (mem1, mb))
  : Maps.ZMap.get ofs (Maps.PMap.get mb (Mem.mem_contents mem1)) = Memdata.Undef.
Proof.
  u_alloca.
  erewrite <- drop_perm_preserves_mem_contents; eauto.
  erewrite <- Mem.alloc_mem_contents; eauto.
  expl Mem.alloc_result; clarify.
  rewrite Maps.PMap.gss.
  apply Maps.ZMap.gi.
Qed.

Lemma alloca_contents_other
      TD mem0 mem1 gsz gn a
      mb b ofs
      (ALLOCA: alloca TD mem0 gsz gn a = Some (mem1, mb))
      (DIFF: b <> mb)
  : Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents mem1)) =
    Maps.ZMap.get ofs (Maps.PMap.get b (Mem.mem_contents mem0)).
Proof.
  u_alloca.
  erewrite <- drop_perm_preserves_mem_contents; try eassumption.
  erewrite <- Mem.alloc_mem_contents; eauto.
  expl Mem.alloc_result; clarify.
  rewrite Maps.PMap.gsspec.
  des_ifs.
Qed.

Lemma alloca_preserves_mload_aux_other_eq
      TD mem0 bsz gn a mem1 mb
      ch b ofs
      (ALLOCA: alloca TD mem0 bsz gn a = Some (mem1, mb))
      (DIFFBLOCK: b <> mb)
  : mload_aux mem0 ch b ofs = mload_aux mem1 ch b ofs.
Proof.
  unfold alloca, Datatypes.option_map, flip in *. des_ifs_safe.
  destruct (mload_aux mem1 ch b ofs) eqn:LOAD1.
  - exploit MemProps.alloc_drop_preserves_mload_aux_inv; eauto; []; i; des; ss.
  - destruct (mload_aux mem0 ch b ofs) eqn:LOAD0; eauto.
    exploit MemProps.alloc_drop_preserves_mload_aux; eauto. i. congruence.
Qed.

Lemma alloca_preserves_mload_other_eq
      TD mem0 bsz gn a mem1 mb
      ptr b ofs tyl al
      (ALLOCA: alloca TD mem0 bsz gn a = Some (mem1, mb))
      (GV2PTR: GV2ptr TD (getPointerSize TD) ptr = Some (Values.Vptr b ofs))
      (DIFFBLOCK: b <> mb)
  : mload TD mem0 ptr tyl al = mload TD mem1 ptr tyl al.
Proof.
  unfold mload. rewrite GV2PTR.
  destruct (flatten_typ TD tyl); ss.
  eapply alloca_preserves_mload_aux_other_eq; eauto.
Qed.

Lemma mstore_aux_valid_access
      mem0 mem1 gv p
      chunkl b ofs
      chunk' b' ofs'
      (MALLOC: mstore_aux mem0 chunkl gv b ofs = Some mem1)
  : Mem.valid_access mem0 chunk' b' ofs' p <->
    Mem.valid_access mem1 chunk' b' ofs' p.
Proof.
  split.
  - revert mem0 mem1 gv ofs MALLOC.
    induction chunkl; ss; i; des_ifs.
    apply IHchunkl in MALLOC; eauto.
    eapply Mem.store_valid_access_1; eauto.
  - revert mem0 mem1 gv ofs MALLOC.
    induction chunkl; ss; i; des_ifs.
    apply IHchunkl in MALLOC; eauto.
    eapply Mem.store_valid_access_2; eauto.
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
  : Mem.perm M b' ofs' k p <->
    Mem.perm M' b' ofs' k p.
Proof.
  split.
  - revert M M' gv ofs MSTORE.
    induction mc; i; ss; des_ifs.
    apply IHmc in MSTORE; eauto.
    eapply Mem.perm_store_1; eauto.
  - revert M M' gv ofs MSTORE.
    induction mc; i; ss; des_ifs.
    apply IHmc in MSTORE; eauto.
    eapply Mem.perm_store_2; eauto.
Qed.

Lemma free_preserves_mload_aux_eq
      mem0 blk lo hi mem1 b
      mc ofs
      (FREE: Mem.free mem0 blk lo hi = Some mem1)
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
      (chunk : list AST.memory_chunk) (m1 : Mem.mem) (b : Values.block) (ofs : Z)
      (gv : GenericValue) (m2 : Mem.mem)
      (STORE: mstore_aux m1 chunk gv b ofs = Some m2)
      (blk : Values.block) (ofs1 : Z) (sz : nat)
      (DIFFBLOCK: blk <> b)
  : Mem.getN sz ofs1 (Maps.PMap.get blk (Mem.mem_contents m1)) =
    Mem.getN sz ofs1 (Maps.PMap.get blk (Mem.mem_contents m2)).
Proof.
  revert m1 ofs gv STORE.
  induction chunk; i; ss; des_ifs.
  eapply IHchunk in STORE. rewrite <- STORE.
  eapply Mem.store_getN_out; eauto.
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
  destruct (mload TD mem1 lptr lty la) eqn:LOAD1.
  - exploit MemProps.mstore_preserves_mload_inv'; eauto.
    rewrite vellvm_no_alias_is_diffblock.
    instantiate (1:=conf).
    unfold InvState.Unary.sem_noalias in *.
    unfold InvState.Unary.sem_diffblock.
    eauto.
  - destruct (mload TD mem0 lptr lty la) eqn:LOAD0; eauto.
    exploit MemProps.mstore_preserves_mload; eauto; try congruence.
    rewrite vellvm_no_alias_is_diffblock.
    instantiate (1:=conf).
    unfold InvState.Unary.sem_noalias in *.
    unfold InvState.Unary.sem_diffblock.
    eauto.
Qed.

Lemma mfree_noalias_mload
      conf mem0 mem1 TD
      ptr ty lptr lty la
      (FREE: free TD mem0 ptr = Some mem1)
      (NOALIAS: InvState.Unary.sem_noalias conf ptr lptr ty lty)
  : mload TD mem1 lptr lty la = mload TD mem0 lptr lty la.
Proof.
  destruct (mload TD mem1 lptr lty la) eqn:LOAD1.
  - exploit MemProps.free_preserves_mload_inv; eauto.
  - destruct (mload TD mem0 lptr lty la) eqn:LOAD0; eauto.
    exploit MemProps.free_preserves_mload; eauto; try congruence.
    rewrite vellvm_no_alias_is_diffblock.
    instantiate (1 := conf).
    unfold InvState.Unary.sem_noalias in *.
    unfold InvState.Unary.sem_diffblock.
    eauto.
Qed.

Lemma valid_ptrs__no_alias__fresh_ptr_iff
      bound TD gvs
  : MemProps.valid_ptrs bound gvs <->
    forall mb (BOUND: (bound <= mb)%positive),
      MemProps.no_alias gvs (blk2GV TD mb).
Proof.
  split.
  { i. eapply MemProps.valid_ptrs__no_alias__fresh_ptr; eauto. }
  induction gvs; ss.
  destruct a.
  destruct v; eauto.
  i. exploit IHgvs; eauto.
  { i. exploit H; eauto.
    i. des. eauto. }
  i. split; eauto.
  specialize (H b).
  destruct (plt b bound); ss.
  rewrite Pos.le_nlt in *.
  unfold Plt in *.
  exploit H; eauto.
  i. des. congruence.
Qed.

Lemma mstore_aux_valid_ptrs_preserves_wf_Mem
      gmax conf mem0 mem1
      b ofs ch gv
      (WF_MEM : MemProps.wf_Mem gmax conf.(CurTargetData) mem0)
      (VALID_PTRS: MemProps.valid_ptrs mem0.(Memory.Mem.nextblock) gv)
      (MSTORE_AUX : mstore_aux mem0 ch gv b ofs = Some mem1)
  : MemProps.wf_Mem gmax (CurTargetData conf) mem1.
Proof.
  unfold MemProps.wf_Mem in *. des.
  exploit MemProps.nextblock_mstore_aux; eauto. i.
  split; try congruence.
  i. eapply valid_ptrs__no_alias__fresh_ptr_iff.
  instantiate (1:=conf.(CurTargetData)).
  i. apply MemProps.no_alias_sym.
  eapply TODOProof.mstore_aux_never_produce_new_ptr; eauto.
  - i. exploit WF_MEM; eauto. i.
    erewrite valid_ptrs__no_alias__fresh_ptr_iff in x.
    apply MemProps.no_alias_sym.
    exploit x; eauto. congruence.
  - apply MemProps.no_alias_sym.
    rewrite valid_ptrs__no_alias__fresh_ptr_iff in VALID_PTRS.
    apply VALID_PTRS. congruence.
Qed.

Lemma mstore_const_leak_no_unique
      conf st0 gmax u
      c gv
      ptr ty a mem1
      (UNIQUE_U : InvState.Unary.sem_unique conf st0 gmax u)
      (PTR: const2GV conf.(CurTargetData) conf.(Globals) c = Some gv)
      (STORE : mstore conf.(CurTargetData) st0.(Mem) ptr ty gv a = Some mem1)
      (WF_GLOBALS: genericvalues_inject.wf_globals gmax conf.(Globals))
  : InvState.Unary.sem_unique conf (mkState st0.(EC) st0.(ECS) mem1) gmax u.
Proof.
  inv UNIQUE_U.
  econs; eauto. ss.
  i. hexploit mstore_never_produce_new_ptr; eauto.
  { i. rewrite vellvm_no_alias_is_diffblock. eauto. }
  {
    clear_tac.
    expl wf_globals_const2GV.
    unfold MemProps.wf_lc in *.
    clear - wf_globals_const2GV VAL GLOBALS.
    induction gv; ii; ss.
    - des_ifs; des; expl IHgv; clear IHgv.
      splits; ss.
      clear IHgv0. clear_tac.
      clear VAL.
      induction val; ii; ss.
      + des_ifs; des; try expl IHval.
        exploit GLOBALS.
        { ss. left. ss. }
        i; des.
        split; ss.
        * ii. clarify.
          apply_all_once Pos.le_succ_l.
          rewrite <- Pplus_one_succ_r in *.
          apply Pos.succ_le_mono in wf_globals_const2GV.
          hexploit Pos.le_trans.
          { apply x. }
          { eauto. }
          i; des.
          apply_all_once Pos.le_succ_l.
          expl Pos.lt_irrefl.
        * expl IHval.
  }
  rewrite <- vellvm_no_alias_is_diffblock. eauto.
Qed.

Lemma mstore_register_leak_no_unique
      conf st0 gmax u
      x gv
      ptr ty a mem1
      (UNIQUE_U : InvState.Unary.sem_unique conf st0 gmax u)
      (DIFF_ID: x <> u)
      (PTR: lookupAL GenericValue st0.(EC).(Locals) x = Some gv)
      (STORE : mstore conf.(CurTargetData) st0.(Mem) ptr ty gv a = Some mem1)
  : InvState.Unary.sem_unique conf (mkState st0.(EC) st0.(ECS) mem1) gmax u.
Proof.
  inv UNIQUE_U.
  econs; eauto. ss.
  i. hexploit mstore_never_produce_new_ptr; eauto.
  { i. rewrite vellvm_no_alias_is_diffblock. eauto. }
  { rewrite vellvm_no_alias_is_diffblock.
    eapply LOCALS; eauto. }
  rewrite <- vellvm_no_alias_is_diffblock. eauto.
Qed.

(* tactic for positive. TODO: can we use Hint instead of this? *)
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

Lemma invmem_unary_alloca_sem
      conf invmem0 mem0 mem1
      gmax public mb
      gsz gn a
      (STATE : InvMem.Unary.sem conf gmax public mem0 invmem0)
      (ALLOCA: alloca (CurTargetData conf) mem0 gsz gn a = Some (mem1, mb))
      (PUBLIC: ~ public mb)
  : InvMem.Unary.sem conf gmax public mem1 (InvMem.Unary.mk
                                              invmem0.(InvMem.Unary.private_parent)
                                              invmem0.(InvMem.Unary.mem_parent)
                                              invmem0.(InvMem.Unary.unique_parent)
                                              mem1.(Memory.Mem.nextblock)).
Proof.
  exploit alloca_result; eauto. i. des.
  inv STATE.
  econs; eauto.
  - eapply MemProps.alloca_preserves_wf_Mem; eauto.
  - ss. i.
    exploit PRIVATE_PARENT; eauto. i.
    unfold InvMem.private_block in *. des.
    split; eauto.
    psimpl.
  - i. exploit MEM_PARENT; eauto. intro LOAD_AUX.
    rewrite LOAD_AUX.
    eapply alloca_preserves_mload_aux_other_eq; eauto.
    ii. exploit PRIVATE_PARENT; eauto. i.
    unfold InvMem.private_block in *. des. psimpl.
  - ss. i.
    unfold mload in LOAD. des_ifs.
    destruct (Values.eq_block b (Memory.Mem.nextblock mem0)); cycle 1.
    + eapply UNIQUE_PARENT_MEM; eauto.
      erewrite alloca_preserves_mload_other_eq; eauto.
      instantiate (1:= align0).
      unfold mload.
      instantiate (1:= typ0).
      des_ifs.
    + subst.
      u_alloca.
      exploit MemProps.alloc_drop_preserves_mload_aux_inv; eauto.
      intro LOAD_UNDEF. des.
      { congruence. }
      ii. exploit external_intrinsics.GV2ptr_inv; eauto. i. des.
      subst. ss. clarify.
      eapply InvState.Unary.undef_diffblock; eauto.
  - ss. rewrite NEXT_BLOCK. etransitivity; [|eapply Ple_succ]. eauto.
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

(* TODO: better name? *)
(* TODO: better position? *)
Lemma inject_allocas_enhance
      f0 als_src als_tgt
      (INJ: InvState.Rel.inject_allocas f0 als_src als_tgt)
      P Q
      (PROP_SRC: Forall P als_src)
      (PROP_TGT: Forall Q als_tgt)
      f1
      (EQ_UNDER_PROP_SRC: forall b, P b -> f0 b = f1 b)
      (EQ_UNDER_PROP_TGT: forall b b_tgt delta (H: f1 b = Some (b_tgt, delta)), Q b_tgt -> f0 b = f1 b)
  :
    <<INJ: InvState.Rel.inject_allocas f1 als_src als_tgt>>
.
Proof.
  ginduction INJ; ii; ss.
  - econs; eauto.
  - inv PROP_SRC.
    econs; eauto.
    { rewrite <- PRIVATE. symmetry. eauto. }
    eapply IHINJ; eauto.
  - inv PROP_TGT.
    econs; eauto.
    { ii. exploit EQ_UNDER_PROP_TGT; eauto. i.
      eapply PRIVATE; eauto.
      rewrite x. eauto.
    }
    eapply IHINJ; eauto.
  - inv PROP_SRC. inv PROP_TGT. econs 4; eauto.
    { rewrite <- EQ_UNDER_PROP_SRC; eauto. }
    eapply IHINJ; eauto.
Qed.

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
    <<MEM: InvMem.Rel.sem conf_src conf_tgt (Mem st1_src) (Mem st1_tgt) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>> /\
    <<PRIVATE_PRESERVED_SRC: IdTSet.For_all
                               (InvState.Unary.sem_private
                                  conf_src st0_src (InvState.Rel.src invst0)
                                  (InvMem.Unary.private_parent (InvMem.Rel.src invmem1))
                                  (InvMem.Rel.public_src (InvMem.Rel.inject invmem1)))
                               (Invariant.private (Invariant.src inv0))>> /\
    <<PRIVATE_PRESERVED_TGT: IdTSet.For_all
                               (InvState.Unary.sem_private
                                  conf_tgt st0_tgt (InvState.Rel.tgt invst0)
                                  (InvMem.Unary.private_parent (InvMem.Rel.tgt invmem1))
                                  (InvMem.Rel.public_tgt (InvMem.Rel.inject invmem1)))
                               (Invariant.private (Invariant.tgt inv0))>> /\
    (* INJECT_ALLOCAS is needed for "inv_state_sem_monotone_wrt_invmem" *)
    (* I am not sure this design is good; as INJECT_ALLOCAS belongs to InvState *)
    (* INJECT_ALLOCAS is needed here. && also in SimLocal *)
    (* If we put this inside InvMem (may need to strengthen "frozen" until "nextblock" *)
    (* This will not be the case *)
    <<INJECT_ALLOCAS:
      InvState.Rel.inject_allocas (InvMem.Rel.inject invmem1)
                                  st0_src.(EC).(Allocas) st0_tgt.(EC).(Allocas)>> /\
   <<INJECT_ALLOCAS:
      InvState.Rel.inject_allocas (InvMem.Rel.inject invmem1)
                                  st1_src.(EC).(Allocas) st1_tgt.(EC).(Allocas)>> /\
    <<VALID_ALLOCAS_SRC: Forall (Mem.valid_block (Mem st1_src)) st1_src.(EC).(Allocas)>> /\
    <<VALID_ALLOCAS_TGT: Forall (Mem.valid_block (Mem st1_tgt)) st1_tgt.(EC).(Allocas)>>
.
Proof.
  exploit postcond_cmd_inject_event_non_malloc; eauto; []; ii; des.
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
    | [H: alloca _ _ _ _ _ = _ |- _] => rename H into ALLOCA_SRC
    end.
    inv STEP_TGT; inv CMD_TGT; ss; try by des; congruence.
    rename Mem0 into mem0_tgt. rename Mem' into mem1_tgt. rename mb into mb_tgt.
    match goal with
    | [H: alloca _ _ _ _ _ = _ |- _] => rename H into ALLOCA_TGT
    end.
    clear_tac.
    dup ALLOCA_SRC.
    dup ALLOCA_TGT.
    unfold alloca, Datatypes.option_map, flip in ALLOCA_SRC, ALLOCA_TGT. des_ifs_safe.
    expl alloca_result (try exact ALLOCA_SRC0; eauto). clarify.
    expl alloca_result (try exact ALLOCA_TGT0; eauto). clarify.
    expl Mem.alloc_result (try exact Heq1; eauto). clarify.
    expl Mem.alloc_result (try exact Heq3; eauto). clarify.
    clear_tac.
    eexists.
    instantiate (1:= InvMem.Rel.mk _ _ _
                                   (fun b =>
                                      if Values.eq_block b (Mem.nextblock mem0_src)
                                      then Some ((Mem.nextblock mem0_tgt), 0%Z)
                                      else invmem0.(InvMem.Rel.inject) b)).
    esplits.
    + (* alloc_inject *)
      ii. ss.
      inv ALLOCA_SRC. inv ALLOCA_TGT.
      esplits.
      * unfold alloc_inject_unary.
        esplits; try apply lookupAL_updateAddAL_eq; ss.
      * unfold alloc_inject_unary.
        esplits; try apply lookupAL_updateAddAL_eq; ss.
      * destruct (Values.eq_block (Mem.nextblock mem0_src)(Mem.nextblock mem0_src)); ss.
    + (* alloc_private *)
      econs; ii; ss; des_ifs.
    + (* InvMem sem *)
      inv MEM; ss.
      econs; ss; eauto.
      { (* SRC *)
        inv SRC.
        instantiate (1:= InvMem.Unary.mk _
                                         invmem0.(InvMem.Rel.src).(InvMem.Unary.mem_parent)
                                         invmem0.(InvMem.Rel.src).(InvMem.Unary.unique_parent)
                                         mem1_src.(Mem.nextblock)).
        econs; eauto.
        - eapply MemProps.alloca_preserves_wf_Mem; eauto.
        - ss. i. exploit PRIVATE_PARENT; eauto. intros [NOT_PUBLIC_B NEXT_B].
          split.
          + ii. unfold InvMem.Rel.public_src in *.
            destruct (Values.eq_block _ _); ss.
            psimpl.
          + erewrite Mem.nextblock_drop with (m:= m0); try eassumption.
            erewrite Mem.nextblock_alloc; try eassumption.
            eapply Pos.lt_le_trans; eauto.
            eapply Ple_succ; eauto.
        - i. exploit MEM_PARENT; eauto. i. ss.
          match goal with
          | [H: mload_aux (InvMem.Unary.mem_parent _) _ b _ = _ |- _] =>
            rewrite H
          end.
          exploit PRIVATE_PARENT; eauto. i.
          unfold InvMem.private_block in *. des.
          eapply alloca_preserves_mload_aux_other_eq; eauto.
        - ss. rewrite NEXT_BLOCK. etransitivity; [|apply Ple_succ]; eauto.
      }
      { (* TGT *)
        inv TGT.
        instantiate (1:= InvMem.Unary.mk _
                                         invmem0.(InvMem.Rel.tgt).(InvMem.Unary.mem_parent)
                                         invmem0.(InvMem.Rel.tgt).(InvMem.Unary.unique_parent)
                                         mem1_tgt.(Mem.nextblock)).
        econs; eauto.
        - eapply MemProps.alloca_preserves_wf_Mem; eauto.
        - ss. i. exploit PRIVATE_PARENT; eauto.
          intros [NOT_PUBLIC_B NEXT_B].
          split.
          + ii.
            match goal with
            | [H: ~ InvMem.Rel.public_tgt _ _ |- False] =>
              apply H
            end.
            unfold InvMem.Rel.public_tgt in *. des.
            destruct (Values.eq_block _ _).
            * clarify. exfalso. psimpl.
            * esplits; eauto.
          + erewrite Mem.nextblock_drop with (m:= m); try eassumption.
            erewrite Mem.nextblock_alloc; try eassumption.
            eapply Pos.lt_le_trans; eauto.
            eapply Ple_succ; eauto.
        - i. exploit MEM_PARENT; eauto. i.
          match goal with
          | [H: mload_aux (InvMem.Unary.mem_parent _) _ b _ = _ |- _] =>
            rewrite H
          end.
          exploit PRIVATE_PARENT; eauto. i.
          unfold InvMem.private_block in *. des.
          eapply alloca_preserves_mload_aux_other_eq; eauto.
        - ss. rewrite NEXT_BLOCK0. etransitivity; [|apply Ple_succ]; eauto.
      }
      { (* inject *)
        inv INJECT.
        unfold is_true in *.
        repeat rewrite andb_true_iff in INJECT_EVENT.
        destruct INJECT_EVENT as [[[ID_EQ TYP_EQ] INJECT_VALUE] DEC_EQ].
        unfold proj_sumbool in *. des_sumbool. clarify.
        econs.
        { (* mi_access *)
          ii. exploit valid_access_alloca_inv; try exact ALLOCA_SRC0; eauto.
          i.
          destruct (Values.eq_block _ _).
          - clarify.
            assert(Memtype.perm_order Memtype.Writable p).
            { move Heq4 at bottom.
              destruct p; try econs.
              eapply Mem.valid_access_perm in H0.
              hexploit Mem.perm_drop_2; eauto.
              des. split; ss.
              expl Memdata.size_chunk_pos. instantiate (1:= chunk) in size_chunk_pos.
              apply Z.gt_lt_iff in size_chunk_pos.
              eapply Z.lt_le_trans.
              { instantiate (1:= ofs + Memdata.size_chunk chunk). omega. }
              unfold get_or_else in *. des_ifs; omega.
            }
            eapply valid_access_alloca_same; eauto.
            repeat rewrite Z.add_0_r.
            des. splits; eauto.
            exploit genericvalues_inject.simulation__eq__GV2int; eauto. intro GV2INT_INJECT.
            rewrite <- GV2INT_INJECT. eauto.
          - exploit mi_access; eauto.
            eapply valid_access_alloca_other; eauto.
        }
        { (* mi_memval *)
          i. destruct (Values.eq_block _ _).
          - clarify.
            rewrite Z.add_0_r.
            erewrite alloca_contents_same; eauto.
            erewrite alloca_contents_same; eauto.
            apply memory_sim.MoreMem.memval_inject_undef.
          - eapply memory_sim.MoreMem.memval_inject_incr.
            + assert (DIFF_BLK_TGT: b2 <> (Mem.nextblock mem0_tgt)).
              { exploit genericvalues_inject.Hmap2; eauto. }
              eapply alloca_contents_other in DIFF_BLK_TGT; eauto.
              rewrite DIFF_BLK_TGT.
              erewrite alloca_contents_other; eauto.
              apply mi_memval; eauto.
              eapply Mem.perm_drop_4 in H0; [|try exact Heq4].
              exploit Mem.perm_alloc_inv.
              { try exact Heq3. }
              { eauto. }
              i. des_ifs.
            + ii.
              destruct (Values.eq_block _ _).
              { subst. exfalso.
                exploit genericvalues_inject.Hmap1; eauto.
                { instantiate (1:=Mem.nextblock mem0_src).
                  exploit alloca_inv; try exact ALLOCA_SRC0. i. psimpl.
                }
                i. congruence.
              }
              eauto.
        }
      }
      { (* wf_sb_mi *)
        inv WF.
        econs.
        - (* no_overlap *)
          ii.
          destruct (Values.eq_block _ _);
            destruct (Values.eq_block _ _); clarify.
          + exploit Hmap2; eauto. i. psimpl.
          + exploit Hmap2; eauto. i. psimpl.
          + eapply Hno_overlap with (b1:=b1) (b2:=b2); eauto.
        - (* Hmap1 *)
          intro b_src. i. destruct (Values.eq_block _ _).
          + subst.
            rewrite NEXT_BLOCK in *.
            exfalso. psimpl.
          + apply Hmap1. psimpl.
        - (* Hmap2 *)
          intros b_src b_tgt. i. destruct (Values.eq_block _ _).
          + clarify.
            subst. rewrite NEXT_BLOCK0 in *.
            apply Plt_succ'.
          + exploit Hmap2; eauto. i. psimpl.
        - (* mi_freeblocks *)
          intros b NOT_VALID_BLOCK.
          destruct (Values.eq_block _ _).
          + subst.
            exfalso.
            apply NOT_VALID_BLOCK.
            unfold Mem.valid_block.
            psimpl.
          + apply mi_freeblocks. intros VALID_BLOCK.
            apply NOT_VALID_BLOCK.
            unfold Mem.valid_block in *.
            psimpl.
        - (* mi_mappedblocks *)
          i. destruct (Values.eq_block _ _).
          + clarify.
            unfold Mem.valid_block in *.
            psimpl.
          + eapply Mem.drop_perm_valid_block_1; eauto.
            eapply Mem.valid_block_alloc.
            { eauto. }
            eapply mi_mappedblocks; eauto.
        - (* mi_range_blocks *)
          ii. destruct (Values.eq_block _ _).
          + subst. clarify.
          + eapply mi_range_block; eauto.
        - (* mi_bounds *)
          ii. destruct (Values.eq_block _ _).
          + clarify.
            erewrite Mem.bounds_drop; eauto.
            erewrite Mem.bounds_alloc_same; cycle 1.
            { eauto. }
            erewrite Mem.bounds_drop; eauto.
            erewrite Mem.bounds_alloc_same; cycle 1.
            { eauto. }
            apply injective_projections; ss.
            solve_match_bool. clarify.
            exploit genericvalues_inject.simulation__eq__GV2int; eauto. intro GV2INT_INJECT.
            rewrite <- GV2INT_INJECT. eauto.
          + erewrite Mem.bounds_drop; eauto.
            erewrite Mem.bounds_alloc_other with (b':=b); eauto; cycle 1.
            assert (NEQ_BLK_TGT: b' <> mem0_tgt.(Mem.nextblock)).
            { exploit Hmap2; eauto. }
            symmetry. (* TODO: "rewrite at" doesn't work, WHY???????? *)
            erewrite Mem.bounds_drop; eauto.
            erewrite Mem.bounds_alloc_other with (b':=b'); try exact NEQ_BLK_TGT; cycle 1.
            { eauto. }
            symmetry. eapply mi_bounds; eauto.
        - (* mi_globals *)
          i. destruct (Values.eq_block _ _).
          + subst.
            exploit mi_globals; eauto. i.
            exploit Hmap1.
            { psimpl. }
            i. congruence.
          + exploit mi_globals; eauto.
      }
      { (* ftable *)
        eapply inject_incr__preserves__ftable_simulation; eauto.
        ii. rename H into INJ0.
        des_ifs_safe.
        inv WF.
        exploit Hmap1.
        { ii. rewrite Pos.compare_refl in *. clarify. }
        intro INJ1.
        rewrite INJ1 in *. clarify.
      }
    + (* le *)
      econs; try (econs; ss).
      { inv MEM. inv SRC. rewrite <- NEXTBLOCK. psimpl. }
      { inv MEM. inv TGT. rewrite <- NEXTBLOCK. psimpl. }
      {
        (* incr *)
        ii. ss.
        destruct (Values.eq_block _ _); eauto.
        subst.
        inv MEM. inv WF.
        exploit Hmap1.
        { psimpl. }
        i. congruence.
      }
      {
        ii. des. des_ifsH NEW0.
        unfold Mem.valid_block.
        split; ss.
        - apply MEM.
        - apply MEM.
      }
    + ss.
      inv STATE. inv SRC. ss.
      ii. exploit PRIVATE; eauto. i. des.
      esplits; eauto. ss.
      unfold InvMem.private_block in *. des.
      split.
      * unfold InvMem.Rel.public_src in *.
        destruct (Values.eq_block _ _); ss.
        psimpl.
      * eauto.
    + ss.
      inv STATE. inv TGT. ss.
      ii. exploit PRIVATE; eauto. i. des.
      esplits; eauto. ss.
      unfold InvMem.private_block in *. des.
      split.
      * unfold InvMem.Rel.public_tgt in *.
        ii. des.
        destruct (Values.eq_block _ _); ss.
        { clarify. psimpl. }
        apply PRIVATE_BLOCK. esplits; eauto.
      * eauto.
    + ss.
      inv STATE. clear MAYDIFF.
      inv SRC. clear LESSDEF NOALIAS UNIQUE PRIVATE ALLOCAS_PARENT
                     WF_LOCAL WF_PREVIOUS WF_GHOST UNIQUE_PARENT_LOCAL WF_INSNS.
      inv TGT. clear LESSDEF NOALIAS UNIQUE PRIVATE ALLOCAS_PARENT
                     WF_LOCAL WF_PREVIOUS WF_GHOST UNIQUE_PARENT_LOCAL WF_INSNS.
      ss.
      eapply inject_allocas_enhance; eauto.
      { i. des_ifsG. exfalso. eapply Plt_irrefl. eauto. }
      { i. des_ifsG. exfalso. eapply Plt_irrefl. eauto. }
      (* ginduction ALLOCAS; ii; ss. *)
      (* * econs; eauto. *)
      (* * inv ALLOCAS_VALID. *)
      (*   econs; eauto. des_ifs. *)
      (*   exfalso. eapply Plt_irrefl. eauto. *)
      (* * inv ALLOCAS_VALID0. *)
      (*   econs; eauto. *)
      (*   i. des_ifs. *)
      (*   { ii. clarify. eapply Plt_irrefl. eauto. } *)
      (*   eapply PRIVATE. *)
      (* * inv ALLOCAS_VALID. inv ALLOCAS_VALID0. *)
      (*   econs 4; eauto. *)
      (*   des_ifs. *)
      (*   exfalso. eapply Plt_irrefl. eauto. *)
    + ss.
      inv STATE. clear MAYDIFF.
      inv SRC. clear LESSDEF NOALIAS UNIQUE PRIVATE ALLOCAS_PARENT
                     WF_LOCAL WF_PREVIOUS WF_GHOST UNIQUE_PARENT_LOCAL WF_INSNS.
      inv TGT. clear LESSDEF NOALIAS UNIQUE PRIVATE ALLOCAS_PARENT
                     WF_LOCAL WF_PREVIOUS WF_GHOST UNIQUE_PARENT_LOCAL WF_INSNS.
      ss.
      econs 4; eauto.
      * des_ifsG.
      * eapply inject_allocas_enhance; eauto.
        { i. des_ifsG. exfalso. eapply Pos.lt_irrefl. eauto. }
        { i. des_ifsG. exfalso. eapply Pos.lt_irrefl. eauto. }
    + inv STATE. inv SRC.
      clear - NEXT_BLOCK ALLOCAS_VALID.
      ss.
      econs; eauto.
      * unfold Mem.valid_block. rewrite NEXT_BLOCK. eapply Plt_succ.
      * eapply Forall_harder; eauto.
        i.
        unfold Mem.valid_block. rewrite NEXT_BLOCK.
        eapply Pos.lt_le_trans; eauto. eapply Ple_succ.
    + inv STATE. inv TGT.
      clear - NEXT_BLOCK0 ALLOCAS_VALID.
      ss.
      econs; eauto.
      * unfold Mem.valid_block. rewrite NEXT_BLOCK0. eapply Plt_succ.
      * eapply Forall_harder; eauto.
        i.
        unfold Mem.valid_block. rewrite NEXT_BLOCK0.
        eapply Pos.lt_le_trans; eauto. eapply Ple_succ.
  - (* alloc - none *)
    inv STATE_EQUIV_TGT. rewrite <- MEM_EQ in *.

    inv STEP_SRC; destruct cmd_src; ss; clarify;
      des_matchH MC_SOME_SRC; clarify; ss.
    rename Mem0 into mem0_src.
    rename Mem' into mem1_src.
    inv STATE_EQUIV_SRC. ss. clarify.
    exploit alloca_result; eauto. intros [ALLOCA_BLOCK_SRC ALLOCA_NEXT_SRC]. des.

    exists (InvMem.Rel.mk
         (InvMem.Unary.mk
            invmem0.(InvMem.Rel.src).(InvMem.Unary.private_parent)
            invmem0.(InvMem.Rel.src).(InvMem.Unary.mem_parent)
            invmem0.(InvMem.Rel.src).(InvMem.Unary.unique_parent)
            mem1_src.(Mem.nextblock))
         invmem0.(InvMem.Rel.tgt)
         invmem0.(InvMem.Rel.gmax)
         (* mem0_src should be private. *)
         (* we can just copy invmem0's, because wf_sb_mi guarantees mem0_src is priviate *)
         (* Without wf_sb_mi, we need to put a function with if-then-else *)
         invmem0.(InvMem.Rel.inject)
           ).
    esplits; ss; eauto.
    + (* alloc_inject *)
      solve_alloc_inject.
    + (* alloc_private *)
      econs; ii; ss; try by des_ifs.
      clarify.
      inv MEM. inv SRC. ss.
      esplits.
      * apply lookupAL_updateAddAL_eq.
      * ii. ss. des; ss.
        move b at bottom.
        rename b into __b__.
        clarify.
        unfold InvMem.private_block in *.
        splits; ss.
        {
          ii.
          unfold InvMem.Rel.public_src in H.
          apply H.
          (* destruct invmem0. ss. *)
          inv WF.
          apply Hmap1. psimpl.
        }
        { psimpl. }
        { ii.
          exploit PRIVATE_PARENT; eauto; []; ii; des.
          psimpl.
        }
    + inv MEM.
      econs; eauto.
      * ss. eapply invmem_unary_alloca_sem; eauto.
        ii. unfold InvMem.Rel.public_src in *.
        apply H.
        inv WF.
        apply Hmap1. psimpl.
      * inv INJECT.
        econs.
        { (* mi-access *)
          i. exploit mi_access; eauto.
          assert (DIFFBLOCK_ALLOC: b1 <> Mem.nextblock mem0_src).
          { inv WF.
            ii. exploit Hmap1.
            { instantiate (1:= Mem.nextblock mem0_src).
              psimpl. }
            i. subst. ss. congruence.
          }
          exploit valid_access_alloca_inv; eauto.
          des_ifs.
        }
        { (* mi_memval *)
          i.
          assert (DIFFBLOCK_ALLOC: b1 <> Mem.nextblock mem0_src).
          { inv WF.
            ii. exploit Hmap1.
            { instantiate (1:= Mem.nextblock mem0_src).
              psimpl. }
            i. subst. ss. congruence.
          }
          exploit mi_memval; eauto.
          { u_alloca.
            eapply Mem.perm_drop_4 in H0; revgoals; eauto.
            hexploit Mem.perm_alloc_inv; eauto; []; i.
            clear INJECT_EVENT.
            des_ifs. eauto. ss.
          }
          i. exploit alloca_contents_other; eauto.
          intro CONTENTS.
          rewrite CONTENTS. eauto.
        }
      * inv WF.
        econs; eauto.
        ++ i. apply Hmap1. psimpl.
        ++ i. apply Hmap1.
           unfold Mem.valid_block in *. psimpl.
        ++ i.
           assert (ALLOC_PRIVATE: b <> Mem.nextblock mem0_src).
           { ii. subst.
             exploit Hmap1.
             { psimpl. }
             i. ss. congruence. }
           u_alloca.
           erewrite Mem.bounds_drop; revgoals; eauto.
           erewrite Mem.bounds_alloc_other; try exact ALLOC_PRIVATE; cycle 1.
           { eauto. }
           eapply mi_bounds; eauto.
    + econs; eauto.
      * econs; eauto. ss.
        inv MEM. inv SRC.
        rewrite <- NEXTBLOCK.
        psimpl.
      * econs; eauto. ss.
        inv MEM. inv TGT.
        rewrite <- NEXTBLOCK.
        psimpl.
      * clarify. ss.
        econs; eauto.
        ii. des; ss. clarify.
    + inv STATE. inv SRC. eauto.
    + inv STATE. inv TGT. eauto.
    + inv STATE. ss.
    + inv STATE. ss.
      assert(EQ_ALLOC: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. }
      des. rewrite EQ_ALLOC.
      econs; eauto.
      inv MEM.
      inv WF.
      apply Hmap1. psimpl.
    + inv STATE. inv SRC. ss.
      clear - ALLOCAS_VALID ALLOCA_NEXT_SRC.
      econs; eauto.
      * unfold Mem.valid_block. rewrite ALLOCA_NEXT_SRC. eapply Plt_succ.
      * eapply Forall_harder; eauto.
        i.
        unfold Mem.valid_block. rewrite ALLOCA_NEXT_SRC.
        eapply Pos.lt_le_trans; eauto.
        eapply Ple_succ.
    + assert(EQ_ALLOC: Allocas (EC st1_tgt) = Allocas (EC st0_tgt) /\ ECS st1_tgt = ECS st0_tgt).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      inv STATE. inv TGT. ss.
      rewrite EQ_ALLOC. ss.
  - (* none - alloc *)
    inv STATE_EQUIV_SRC.
    rewrite <- MEM_EQ in *.

    inv STEP_TGT; destruct cmd_tgt; ss; clarify;
      des_matchH MC_SOME_TGT; clarify; ss.
    rename Mem0 into mem0_tgt.
    rename Mem' into mem1_tgt.
    inv STATE_EQUIV_TGT. ss. clarify.
    exploit alloca_result; eauto. intros [ALLOCA_BLOCK_TGT ALLOCA_NEXT_TGT]. des.

    exists (InvMem.Rel.mk
         invmem0.(InvMem.Rel.src)
         (InvMem.Unary.mk
            invmem0.(InvMem.Rel.tgt).(InvMem.Unary.private_parent)
            invmem0.(InvMem.Rel.tgt).(InvMem.Unary.mem_parent)
            invmem0.(InvMem.Rel.tgt).(InvMem.Unary.unique_parent)
            mem1_tgt.(Mem.nextblock))
         invmem0.(InvMem.Rel.gmax)
                   invmem0.(InvMem.Rel.inject)).
    esplits; ss; eauto.
    + (* alloc_inject *)
      solve_alloc_inject.
    + (* alloc_private *)
      econs; ii; ss; try by des_ifs.
      clarify.
      inv MEM. inv TGT. ss.
      esplits; try apply lookupAL_updateAddAL_eq.
      * ii. ss.
        des; ss.
        unfold InvMem.private_block.
        splits.
        {
          ii.
          subst.
          unfold InvMem.Rel.public_tgt in H.
          des.
          inv WF.
          exploit Hmap2; eauto; []; ii; des.
          psimpl.
        }
        { psimpl. }
        { ii.
          subst.
          exploit PRIVATE_PARENT; eauto; []; ii; des.
          unfold InvMem.private_block in *.
          des.
          psimpl.
        }
    + inv MEM.
      econs; eauto.
      * eapply invmem_unary_alloca_sem; eauto.
        ss. ii. unfold InvMem.Rel.public_tgt in *. des.
        inv WF.
        exploit Hmap2; eauto. i.
        psimpl.
      * inv INJECT.
        econs.
        { (* mi-access *)
          i. exploit mi_access; eauto. i.
          assert (DIFFBLOCK_ALLOC: b2 <> Mem.nextblock mem0_tgt).
          { inv WF.
            ii. exploit Hmap2; eauto.
            i. psimpl. }
          exploit valid_access_alloca_other; eauto.
        }
        { (* mi_memval *)
          i.
          assert (DIFFBLOCK_ALLOC: b2 <> Mem.nextblock mem0_tgt).
          { inv WF.
            ii. exploit Hmap2; eauto.
            i. psimpl. }
          exploit mi_memval; eauto.
          i. exploit alloca_contents_other; eauto.
          intro CONTENTS.
          rewrite CONTENTS. eauto.
        }
      * inv WF.
        econs; eauto.
        ++ i. exploit Hmap2; eauto. i. psimpl.
        ++ i. exploit Hmap2; eauto. i.
           unfold Mem.valid_block. psimpl.
        ++ i.
           assert (ALLOC_PRIVATE: b' <> Mem.nextblock mem0_tgt).
           { ii. subst.
             exploit Hmap2; eauto. i. psimpl. }
           u_alloca.
           symmetry. (* TODO: WHY???????? "rewrite at" dosen't work ???????????????? *)
           erewrite Mem.bounds_drop; revgoals; eauto.
           erewrite Mem.bounds_alloc_other with (b':=b'); try exact ALLOC_PRIVATE; cycle 1.
           { eauto. }
           symmetry.
           eapply mi_bounds; eauto.
    + econs; eauto.
      * econs; eauto. ss.
        inv MEM. inv SRC. rewrite <- NEXTBLOCK. psimpl.
      * econs; eauto. ss.
        inv MEM. inv TGT. rewrite <- NEXTBLOCK. psimpl.
      * ss. econs; eauto.
        ii.
        des; ss. clarify.
    + inv STATE. inv SRC. eauto.
    + inv STATE. inv TGT. eauto.
    + inv STATE. ss.
    + inv STATE. ss.
      assert(EQ_ALLOC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. }
      des. rewrite EQ_ALLOC.
      econs; eauto.
      inv MEM.
      inv WF.
      ii.
      expl Hmap2. psimpl.
    + assert(EQ_ALLOC: Allocas (EC st1_src) = Allocas (EC st0_src) /\ ECS st1_src = ECS st0_src).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      inv STATE. inv SRC. ss.
      rewrite EQ_ALLOC. ss.
    + inv STATE. inv TGT. ss.
      clear - ALLOCAS_VALID ALLOCA_NEXT_TGT.
      econs; eauto.
      * unfold Mem.valid_block. rewrite ALLOCA_NEXT_TGT. eapply Plt_succ.
      * eapply Forall_harder; eauto.
        i.
        unfold Mem.valid_block. rewrite ALLOCA_NEXT_TGT.
        eapply Pos.lt_le_trans; eauto.
        eapply Ple_succ.
  - (* store - store *)
    rename ptr0 into ptr_src. rename gv0 into gv_src.
    rename ptr1 into ptr_tgt. rename gv1 into gv_tgt.
    inv MEM. rename SRC into MSRC. rename TGT into MTGT.
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

    esplits; eauto; try reflexivity; try solve_alloc_inject.
    { unfold alloc_private, alloc_private_unary. split.
      - i. subst. ss. des_matchH MC_SOME_SRC; clarify.
      - i. subst. ss. des_matchH MC_SOME_TGT; clarify.
    }
    + {
        econs; eauto.
        + inv MSRC.
          econs; eauto.
          * eapply mstore_aux_valid_ptrs_preserves_wf_Mem; eauto.
          * (* PRIVATE_PARENT *)
            i. exploit PRIVATE_PARENT; eauto. i. des.
            unfold InvMem.private_block in *. des.
            split; eauto.
            erewrite <- MemProps.nextblock_mstore_aux; eauto.
          * i. hexploit gv_inject_ptr_public_src; try exact PTR_INJECT; eauto. i.
            exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
            (* b <> sb_src *)
            eapply mstore_aux_preserves_mload_aux_eq; eauto.
            ii. subst.
            exploit PRIVATE_PARENT; eauto. i.
            unfold InvMem.private_block in *. des. eauto.
          * rewrite <- NEXTBLOCK. symmetry.
            eapply MemProps.nextblock_mstore_aux; eauto.
          * rpapply NEXTBLOCK_PARENT.
            symmetry. eapply MemProps.nextblock_mstore_aux; eauto.
        + inv MTGT.
          econs; eauto.
          * eapply mstore_aux_valid_ptrs_preserves_wf_Mem; eauto.
          * (* PRIVATE_PARENT *)
            i. exploit PRIVATE_PARENT; eauto. i.
            unfold InvMem.private_block in *. des.
            split; eauto.
            erewrite <- MemProps.nextblock_mstore_aux; eauto.
          * i. hexploit gv_inject_ptr_public_tgt; try exact PTR_INJECT; eauto. i.
            exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
            eapply mstore_aux_preserves_mload_aux_eq; eauto.
            ii. subst.
            exploit PRIVATE_PARENT; eauto. i.
            unfold InvMem.private_block in *. des. eauto.
          * rewrite <- NEXTBLOCK. symmetry.
            eapply MemProps.nextblock_mstore_aux; eauto.
          * rpapply NEXTBLOCK_PARENT.
            symmetry. eapply MemProps.nextblock_mstore_aux; eauto.
      }
    + inv STATE. inv SRC. eauto.
    + inv STATE. inv TGT. eauto.
    + inv STATE. ss.
    + assert(EQ_ALLOC_SRC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      rewrite EQ_ALLOC_SRC.
      assert(EQ_ALLOC_TGT: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      rewrite EQ_ALLOC_TGT.
      apply STATE.
    + assert(EQ_ALLOC_SRC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      rewrite EQ_ALLOC_SRC.
      unfold Mem.valid_block.
      expl MemProps.nextblock_mstore_aux (try exact STORE_SRC).
      rewrite <- nextblock_mstore_aux.
      apply STATE.
    + assert(EQ_ALLOC_TGT: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      rewrite EQ_ALLOC_TGT.
      unfold Mem.valid_block.
      expl MemProps.nextblock_mstore_aux (try exact STORE_TGT).
      rewrite <- nextblock_mstore_aux.
      apply STATE.
  - (* store - none *)
    inv MEM. rename SRC into MSRC. rename TGT into MTGT.
    inv STATE_EQUIV_TGT. rewrite <- MEM_EQ.
    inv STATE_EQUIV_SRC.
    unfold mstore in STORE.
    des_ifs.
    rename Heq into GV2PTR. rename l0 into chunkl. rename Heq0 into FLATTEN.
    esplits; eauto; try reflexivity; try solve_alloc_inject.
    { unfold alloc_private, alloc_private_unary. split.
      - i. subst. ss. des_matchH MC_SOME_SRC; clarify.
      - i. subst. ss. des_matchH MC_SOME_TGT; clarify.
    }
    +
      {
        econs; eauto.
        + inv MSRC.
          econs; eauto.
          * eapply mstore_aux_valid_ptrs_preserves_wf_Mem; eauto.
          * (* PRIVATE_PARENT *)
            i. exploit PRIVATE_PARENT; eauto. i.
            unfold InvMem.private_block in *. des.
            split; eauto.
            erewrite <- MemProps.nextblock_mstore_aux; eauto.
          * i. exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
            eapply mstore_aux_preserves_mload_aux_eq; eauto.
            ii. subst.
            move DISJOINT at bottom.
            exploit DISJOINT; eauto.
            { eapply GV2ptr_In_GV2blocks; eauto. }
            ii; des.
            eauto.
          * erewrite <- MemProps.nextblock_mstore_aux; eauto.
          * rpapply NEXTBLOCK_PARENT.
            symmetry. eapply MemProps.nextblock_mstore_aux; eauto.
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
              move DISJOINT at bottom.
              exploit DISJOINT; eauto.
              { eapply GV2ptr_In_GV2blocks; eauto. }
              ii; des.
              apply NOT_PUBLIC. ii. clarify. }
            assert (GET_ONE: Mem.getN 1 ofs (Maps.PMap.get b1 (Mem.mem_contents (Mem st0_src))) =
                             Mem.getN 1 ofs (Maps.PMap.get b1 (Mem.mem_contents (Mem st1_src)))).
            { eapply mstore_aux_getN_out; eauto. }
            ss. inv GET_ONE.
            eauto.
          }
        + (* WF *)
          inv WF.
          econs; eauto.
          * erewrite <- MemProps.nextblock_mstore_aux; eauto.
          * i. exploit mi_freeblocks; eauto.
            unfold Mem.valid_block in *.
            erewrite MemProps.nextblock_mstore_aux; eauto.
          * i. exploit mi_bounds; eauto. i.
            hexploit MemProps.bounds_mstore_aux; try exact STORE.
            intro BEQ_SRC. rewrite <- BEQ_SRC.
            eauto.
      }
    + inv STATE. inv SRC. eauto.
    + inv STATE. inv TGT. eauto.
    + inv STATE. ss.
    + assert(EQ_ALLOC_SRC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      rewrite EQ_ALLOC_SRC.
      assert(EQ_ALLOC_TGT: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      rewrite EQ_ALLOC_TGT.
      apply STATE.
    + assert(EQ_ALLOC_SRC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      rewrite EQ_ALLOC_SRC.
      unfold Mem.valid_block.
      expl MemProps.nextblock_mstore_aux (try exact STORE).
      rewrite <- nextblock_mstore_aux.
      apply STATE.
    + assert(EQ_ALLOC_TGT: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      rewrite EQ_ALLOC_TGT.
      apply STATE.
  - (* free - free *)
    rename ptr0 into ptr_src. rename ptr1 into ptr_tgt.
    inv MEM. rename SRC into MSRC. rename TGT into MTGT.
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

    esplits; eauto; try reflexivity; try solve_alloc_inject.
    { unfold alloc_private, alloc_private_unary. split.
      - i. subst. ss. des_matchH MC_SOME_SRC; clarify.
      - i. subst. ss. des_matchH MC_SOME_TGT; clarify.
    }
    +
      {
        econs; eauto.
        + inv MSRC.
          econs; eauto.
          * (* PRIVATE_PARENT *)
            i. exploit PRIVATE_PARENT; eauto. i.
            unfold InvMem.private_block in *. des.
            split; eauto.
            erewrite Mem.nextblock_free; eauto.
          * i. hexploit gv_inject_ptr_public_src; try exact PTR_INJECT; eauto. i.
            exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
            exploit free_preserves_mload_aux_eq; try exact FREE_SRC; eauto.
            exploit PRIVATE_PARENT; eauto. i.
            unfold InvMem.private_block in *. des.
            ii. subst. eauto.
          * erewrite Mem.nextblock_free; eauto.
          * rpapply NEXTBLOCK_PARENT.
            eapply Mem.nextblock_free; eauto.
        + inv MTGT.
          econs; eauto.
          * (* PRIVATE_PARENT *)
            i. exploit PRIVATE_PARENT; eauto. i.
            unfold InvMem.private_block in *. des.
            split; eauto.
            erewrite Mem.nextblock_free; eauto.
          * i. hexploit gv_inject_ptr_public_tgt; try exact PTR_INJECT; eauto. i.
            exploit MEM_PARENT; eauto. intro MLOAD_EQ. rewrite MLOAD_EQ.
            exploit free_preserves_mload_aux_eq; try exact FREE_TGT; eauto.
            exploit PRIVATE_PARENT; eauto. i.
            unfold InvMem.private_block in *. des.
            ii. subst. eauto.
          * erewrite Mem.nextblock_free; eauto.
          * rpapply NEXTBLOCK_PARENT.
            eapply Mem.nextblock_free; eauto.
      }
    + inv STATE. inv SRC. eauto.
    + inv STATE. inv TGT. eauto.
    + inv STATE. ss.
    + assert(EQ_ALLOC_SRC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      rewrite EQ_ALLOC_SRC.
      assert(EQ_ALLOC_TGT: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      rewrite EQ_ALLOC_TGT.
      apply STATE.
    + assert(EQ_ALLOC_SRC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      rewrite EQ_ALLOC_SRC.
      unfold Mem.valid_block.
      expl Mem.nextblock_free (try exact FREE_SRC).
      rewrite nextblock_free.
      apply STATE.
    + assert(EQ_ALLOC_TGT: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      rewrite EQ_ALLOC_TGT.
      unfold Mem.valid_block.
      expl Mem.nextblock_free (try exact FREE_TGT).
      rewrite nextblock_free.
      apply STATE.
  - (* none - none *)
    inv STATE_EQUIV_SRC. rewrite <- MEM_EQ. clear MEM_EQ.
    inv STATE_EQUIV_TGT. rewrite <- MEM_EQ. clear MEM_EQ.
    esplits; eauto; try reflexivity; try solve_alloc_inject.
    + unfold alloc_private, alloc_private_unary. split.
      * i. subst. ss. des_matchH MC_SOME_SRC; clarify.
      * i. subst. ss. des_matchH MC_SOME_TGT; clarify.
    + inv STATE. inv SRC. eauto.
    + inv STATE. inv TGT. eauto.
    + inv STATE. ss.
    + assert(EQ_ALLOC_SRC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      rewrite EQ_ALLOC_SRC.
      assert(EQ_ALLOC_TGT: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      rewrite EQ_ALLOC_TGT.
      apply STATE.
    + assert(EQ_ALLOC_SRC: Allocas (EC st1_src) = Allocas (EC st0_src)).
      { inv STEP_SRC; ss; des_ifs.
        - inv MC_SOME_SRC. des_ifs. } des.
      rewrite EQ_ALLOC_SRC.
      apply STATE.
    + assert(EQ_ALLOC_TGT: Allocas (EC st1_tgt) = Allocas (EC st0_tgt)).
      { inv STEP_TGT; ss; des_ifs.
        - inv MC_SOME_TGT. des_ifs. } des.
      rewrite EQ_ALLOC_TGT.
      apply STATE.
Unshelve.
{ by econs. }
Qed.

(* invariant *)

Lemma diffblock_implies_noalias
      conf gv1 gv2 ty1 ty2
      (DIFFBLOCK: InvState.Unary.sem_diffblock conf gv1 gv2)
  : InvState.Unary.sem_noalias conf gv1 gv2 ty1 ty2.
Proof.
  unfold InvState.Unary.sem_diffblock, InvState.Unary.sem_noalias in *. des_ifs.
Qed.

Lemma is_diffblock_sem
      conf st invst invmem inv gmax public
      v1 ty1 v2 ty2 gv1 gv2
      (STATE : InvState.Unary.sem conf st invst invmem gmax public inv)
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
    eapply DIFFBLOCK; eauto.
  - des_bool. des. ss.
    unfold proj_sumbool in *; des_ifs.
    rewrite ValueTPairSetFacts.mem_iff in *.
    apply InvState.Unary.diffblock_comm.
    eapply DIFFBLOCK; eauto.
Qed.

Lemma is_noalias_sem
      conf st invst invmem inv gmax public
      v1 ty1 v2 ty2 gv1 gv2
      (STATE : InvState.Unary.sem conf st invst invmem gmax public inv)
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
    eapply NOALIAS; subst; eauto.
  - des_bool. des. ss. des_ifs.
    rewrite PtrPairSetFacts.mem_iff in *.
    apply InvState.Unary.noalias_comm.
    eapply NOALIAS; subst; eauto.
Qed.

(* TODO: simplify proof script *)
Lemma forget_memory_is_noalias_expr
      conf st1 invst0 invmem0 inv1 mem0 gmax public
      vt_inv ty_inv gv_inv
      v_forget ty_forget gv_forget
      (STATE : InvState.Unary.sem conf (mkState st1.(EC) st1.(ECS) mem0) invst0 invmem0 gmax public inv1)
      (NOALIAS_PTR: ForgetMemory.is_noalias_Ptr inv1 (ValueT.lift Tag.physical v_forget, ty_forget) (vt_inv, ty_inv) = true)
      (FORGET_PTR: getOperandValue (CurTargetData conf) v_forget (Locals (EC st1)) (Globals conf) = Some gv_forget)
      (INV_PTR: InvState.Unary.sem_valueT conf st1 invst0 vt_inv = Some gv_inv)
      (WF_GLOBALS: genericvalues_inject.wf_globals gmax (Globals conf))
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
      apply InvState.Unary.diffblock_comm.
      eapply LOCALS; eauto.
    + apply diffblock_implies_noalias.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      eapply InvState.Unary.diffblock_comm.
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
      apply InvState.Unary.diffblock_comm.
      unfold InvState.Unary.sem_idT in *. ss. clarify.
      eapply InvState.Unary.diffblock_comm.
      eapply unique_const_diffblock; eauto.
  - apply InvState.Unary.noalias_comm.
    eapply is_noalias_sem; eauto.
    unfold ValueT.lift. des_ifs; eauto.
  - eapply InvState.Unary.diffblock_comm.
    eapply is_diffblock_sem; eauto.
    unfold ValueT.lift. des_ifs; eauto.
Qed.

Lemma forget_memory_is_noalias_exprpair
      conf st1 invst0 invmem0 inv1 mem0 gmax public
      p a e2
      vt_inv ty_inv gv_inv
      v_forget ty_forget gv_forget
      (STATE : InvState.Unary.sem conf (mkState st1.(EC) st1.(ECS) mem0) invst0 invmem0 gmax public inv1)
      (PAIR : p = (Expr.load vt_inv ty_inv a, e2) \/ p = (e2, Expr.load vt_inv ty_inv a))
      (FORGET_MEMORY_NOALIAS : ForgetMemory.is_noalias_ExprPair inv1 (ValueT.lift Tag.physical v_forget, ty_forget) p = true)
      (FORGET_PTR: getOperandValue (CurTargetData conf) v_forget (Locals (EC st1)) (Globals conf) = Some gv_forget)
      (INV_PTR: InvState.Unary.sem_valueT conf st1 invst0 vt_inv = Some gv_inv)
      (WF_GLOBALS: genericvalues_inject.wf_globals gmax (Globals conf))
  : InvState.Unary.sem_noalias conf gv_forget gv_inv ty_forget ty_inv.
Proof.
  unfold ForgetMemory.is_noalias_ExprPair in *.
  des; des_bool; des; subst; ss;
    eapply forget_memory_is_noalias_expr; eauto.
Qed.

Lemma exprpair_forget_memory_disjoint
      conf st0 mem1 invst0 invmem0 inv1 cmd mc gmax public
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 gmax public inv1)
      (MC_SOME : mem_change_of_cmd conf cmd st0.(EC).(Locals) = Some mc)
      (STATE_EQUIV : states_mem_change conf st0.(Mem) mem1 mc)
      (WF_GLOBALS: genericvalues_inject.wf_globals gmax (Globals conf))
      (WF_MEM: MemProps.wf_Mem gmax (CurTargetData conf) st0.(Mem))
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
      eapply alloca_preserves_mload_other_eq; eauto.
      ii. subst.
      inv STATE.
      clear PAIR.
      exploit alloca_result; eauto. i. des. subst.
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
        ss.
        rename g into __g__.
        exploit TODOProof.wf_globals_const2GV; eauto; []; intro VALID_PTR; des.
        destruct WF_MEM as [_ WF_MEM].
        clear - WF_MEM ALLOCA GV2PTR VALID_PTR.
        (* GV2ptr is a bit weird? it is artificially made from above destruct, *)
        (* and it seems main concern here is "load", so it may make sense.. *)
        destruct __g__ as [|[headVal headChunki] tail]; ss.
        destruct headVal; ss. des_ifs.
        des. ss. clear VALID_PTR0.
        clear - WF_MEM VALID_PTR.
        replace (gmax + 1)%positive with (Pos.succ gmax)%positive in *; cycle 1.
        { destruct gmax; ss. }
        rewrite Pos.lt_succ_r in VALID_PTR.
        exploit Pos.lt_le_trans; eauto.
        intro CONTR. apply Pos.lt_irrefl in CONTR. ss.
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
        instantiate (3:= st0.(Mem)).
        destruct st0. ss. exact STATE.
      * apply ExprPairSetFacts.filter_iff in FORGET_MEMORY; try by solve_compat_bool.
        destruct FORGET_MEMORY as [FORGET_MEMORY_IN FORGET_MEMORY_NOALIAS].
        symmetry. eapply mstore_noalias_mload; eauto.
        eapply forget_memory_is_noalias_exprpair; eauto.
        instantiate (3:= st0.(Mem)).
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
      instantiate (3:= st0.(Mem)).
      destruct st0. exact STATE.
  - (* none *)
    inv STATE_EQUIV. destruct st0; eauto.
Qed.

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
      conf st0 mem1 mc cmd gmax public
      inv1 invst0 invmem0
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 gmax public inv1)
      (MC_SOME : mem_change_of_cmd conf cmd st0.(EC).(Locals) = Some mc)
      (STATE_MC : states_mem_change conf st0.(Mem) mem1 mc)
      (WF_GLOBALS: genericvalues_inject.wf_globals gmax (Globals conf))
      (WF_MEM: MemProps.wf_Mem gmax (CurTargetData conf) st0.(Mem))
  : InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) mem1) invst0 invmem0 gmax public
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
      exploit MemProps.alloca_preserves_mload_inv; eauto. i. des.
      * eapply MEM; eauto.
      *
        apply InvState.Unary.diffblock_comm.
        apply InvState.Unary.undef_diffblock; ss.
    + ii. exploit PRIVATE; eauto. i. des.
      esplits; eauto. ss.
      unfold InvMem.private_block in *. des.
      split; eauto.
      exploit alloca_result; eauto. i. des.
      psimpl.
    + ss. eapply Forall_harder; eauto. i.
      exploit alloca_result; eauto; []; i; des.
      clarify.
      unfold Mem.valid_block in *.
      rewrite NEXT_BLOCK.
      etransitivity; eauto.
      eapply Plt_succ.
    + ss. eapply MemProps.alloca_preserves_wf_lc_in_tail; eauto.
    + ss. eapply MemProps.alloca_preserves_wf_lc_in_tail; eauto.
    + ss. eapply MemProps.alloca_preserves_wf_lc_in_tail; eauto.
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
      + ss. ii. exploit PRIVATE; eauto. i. des.
        esplits; eauto. ss.
        unfold InvMem.private_block in *. des.
        split; eauto.
        exploit MemProps.nextblock_mstore; eauto.
        intro NEXTBLOCK_EQ. rewrite <- NEXTBLOCK_EQ.
        psimpl.
      + ss.
      + ss. eapply Forall_harder; eauto.
        i. exploit MemProps.nextblock_mstore; eauto; []; intro EQ; des.
        unfold Mem.valid_block in *.
        rewrite <- EQ. ss.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + eauto.
      + ii. exploit WF_INSNS; eauto.
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
      + ss. ii. exploit PRIVATE; eauto. i. des.
        esplits; eauto. ss.
        unfold InvMem.private_block in *. des.
        split; eauto.
        exploit MemProps.nextblock_mstore; eauto.
        intro NEXTBLOCK_EQ. rewrite <- NEXTBLOCK_EQ.
        psimpl.
      + ss.
      + ss. eapply Forall_harder; eauto.
        i. exploit MemProps.nextblock_mstore; eauto; []; intro EQ; des.
        unfold Mem.valid_block in *.
        rewrite <- EQ. ss.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + ss. eapply MemProps.mstore_preserves_wf_lc; eauto.
      + eauto.
      + ii. exploit WF_INSNS; eauto.
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
      ii. des.
      exploit MemProps.free_preserves_mload_inv; eauto; []; i; des.
      exploit MEM; eauto.
    + ss. ii. exploit PRIVATE; eauto. i. des.
      esplits; eauto. ss.
      unfold InvMem.private_block in *. des.
      split; eauto.
      exploit MemProps.nextblock_free; eauto.
      intro NEXTBLOCK_EQ. rewrite <- NEXTBLOCK_EQ.
      psimpl.
    + ss. eapply Forall_harder; eauto.
      i. exploit MemProps.nextblock_free; eauto; []; intro EQ; des.
      unfold Mem.valid_block in *.
      rewrite <- EQ. ss.
    + ss. eapply MemProps.free_preserves_wf_lc; eauto.
    + ss. eapply MemProps.free_preserves_wf_lc; eauto.
    + ss. eapply MemProps.free_preserves_wf_lc; eauto.
Qed.

Lemma forget_memory_sem
      conf_src st0_src mem1_src mc_src cmd_src
      conf_tgt st0_tgt mem1_tgt mc_tgt cmd_tgt
      inv0 invst0 invmem0
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (WF_GLOBALS_SRC: genericvalues_inject.wf_globals (InvMem.Rel.gmax invmem0) (Globals conf_src))
      (WF_GLOBALS_TGT: genericvalues_inject.wf_globals (InvMem.Rel.gmax invmem0) (Globals conf_tgt))
      (MC_SOME_SRC : mem_change_of_cmd conf_src cmd_src st0_src.(EC).(Locals) = Some mc_src)
      (MC_SOME_TGT : mem_change_of_cmd conf_tgt cmd_tgt st0_tgt.(EC).(Locals) = Some mc_tgt)
      (STATE_MC_SRC : states_mem_change conf_src st0_src.(Mem) mem1_src mc_src)
      (STATE_MC_TGT : states_mem_change conf_tgt st0_tgt.(Mem) mem1_tgt mc_tgt)
      (WF_MEM_SRC: MemProps.wf_Mem invmem0.(InvMem.Rel.gmax) (CurTargetData conf_src) st0_src.(Mem))
      (WF_MEM_TGT: MemProps.wf_Mem invmem0.(InvMem.Rel.gmax) (CurTargetData conf_tgt) st0_tgt.(Mem))
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
  - ss.
Qed.

Lemma inv_state_sem_monotone_wrt_invmem
      invmem0 invmem1 invst0 inv1
      conf_src st_src
      conf_tgt st_tgt
      (MEM_LE:InvMem.Rel.le invmem0 invmem1)
      (PRIVATE_PRESERVED_SRC: IdTSet.For_all
                                (InvState.Unary.sem_private
                                   conf_src st_src (InvState.Rel.src invst0)
                                   (InvMem.Unary.private_parent (InvMem.Rel.src invmem1))
                                   (InvMem.Rel.public_src (InvMem.Rel.inject invmem1)))
                                (Invariant.private (Invariant.src inv1)))
      (PRIVATE_PRESERVED_TGT: IdTSet.For_all
                                (InvState.Unary.sem_private
                                   conf_tgt st_tgt (InvState.Rel.tgt invst0)
                                   (InvMem.Unary.private_parent (InvMem.Rel.tgt invmem1))
                                   (InvMem.Rel.public_tgt (InvMem.Rel.inject invmem1)))
                                (Invariant.private (Invariant.tgt inv1)))
      (STATE:InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem0 inv1)
      (INJECT_ALLOCAS_NEW:
           InvState.Rel.inject_allocas (InvMem.Rel.inject invmem1)
                                       st_src.(EC).(Allocas) st_tgt.(EC).(Allocas))
  : InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem1 inv1.
Proof.
  destruct STATE as [STATE_SRC STATE_TGT STATE_MAYDIFF].
  inv MEM_LE.
  econs.
  - inv SRC.
    inv STATE_SRC.
    econs; eauto.
    + rewrite <- GMAX. eauto.
    + rewrite <- PRIVATE_PARENT_EQ. ss.
    + rewrite <- UNIQUE_PARENT_EQ. eauto.
  - inv TGT.
    inv STATE_TGT.
    econs; eauto.
    + rewrite <- GMAX. eauto.
    + rewrite <- PRIVATE_PARENT_EQ. ss.
    + rewrite <- UNIQUE_PARENT_EQ. eauto.
  - i. hexploit STATE_MAYDIFF; eauto.
    intros SEM_INJECT.
    ii. exploit SEM_INJECT; eauto. i. des.
    esplits; eauto.
    eapply genericvalues_inject.gv_inject_incr; eauto.
  - ss.
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
      <<MEMLE: InvMem.Rel.le invmem0 invmem1>> /\
      <<INJECT_ALLOCAS: InvState.Rel.inject_allocas (InvMem.Rel.inject invmem1)
                         st1_src.(EC).(Allocas) st1_tgt.(EC).(Allocas)>> /\
      <<VALID_ALLOCAS_SRC: Forall (Mem.valid_block (Mem st1_src)) st1_src.(EC).(Allocas)>> /\
      <<VALID_ALLOCAS_TGT: Forall (Mem.valid_block (Mem st1_tgt)) st1_tgt.(EC).(Allocas)>>
.
Proof.
  assert (STATE2:= STATE).
  inv STATE2.
  exploit postcond_cmd_inject_event_non_malloc; eauto; []; ii; des.
  exploit step_mem_change; try exact SRC; eauto.
  { inv MEM. exact SRC0. }
  i. des.
  exploit step_mem_change; try exact TGT; eauto.
  { inv MEM. exact TGT0. }
  i. des.
  exploit inject_invmem; try exact INJECT_EVENT; eauto. i. des.
  esplits; eauto.
  - eapply forget_memory_sem; eauto.

    eapply inv_state_sem_monotone_wrt_invmem; eauto.
    { apply MEM0. }
    { apply MEM0. }
    { inv MEMLE. rewrite <- GMAX. apply MEM. }
    { inv MEMLE. rewrite <- GMAX. apply MEM. }
Qed.