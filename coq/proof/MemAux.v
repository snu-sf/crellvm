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
Require Import TODOProof.
Import Memory.

Set Implicit Arguments.




Theorem wf_globals_const2GV: forall
    gmax gl TD cnst gv
    (GLOBALS: genericvalues_inject.wf_globals gmax gl)
    (C2G: const2GV TD gl cnst = Some gv)
  ,
    <<VALID_PTR: MemProps.valid_ptrs (gmax + 1)%positive gv>>
.
Proof.
  ii.
  unfold const2GV in *. des_ifs.
  move cnst at top. revert_until cnst.
  unfold cgv2gv.
  induction cnst using Decs.const_ind_gen; ii; ss; des_ifs_safe ss; clarify.
  - clear GLOBALS. clear_tac.
    expl MemProps.zeroconst2GV_no_ptr.
    clear Heq0.
    ginduction g; ii; ss.
    des_ifs; ss; eapply IHg; eauto.
  - des_ifs.
  - eapply MemProps.undef_valid_ptrs; eauto.
  - {
      clear Heq1.
      ginduction l0; ii; ss; clarify.
      inv IH. des_ifs.
      expl H1.
      expl IHl0.
      eapply MemProps.valid_ptrs_app; eauto.
      eapply MemProps.valid_ptrs_app; eauto.
      eapply MemProps.uninits_valid_ptrs; eauto.
    }
  - abstr (p :: g1) gv.
    clear Heq1.
    ginduction l0; ii; ss; clarify.
    des_ifs.
    inv IH.
    expl H1.
    expl IHl0.
    eapply MemProps.valid_ptrs_app; eauto.
    eapply MemProps.valid_ptrs_app; eauto.
    eapply MemProps.uninits_valid_ptrs; eauto.
  - expl genericvalues_inject.wf_globals__wf_global.
    clear - wf_globals__wf_global.
    ginduction g; ii; ss.
    des_ifs; ss; des; try eapply IHg; eauto.
    split; ss.
    + rewrite <- Pplus_one_succ_r.
      eapply Pos.lt_succ_r; eauto.
    + eapply IHg; eauto.
  - eapply MemProps.mtrunc_preserves_valid_ptrs; eauto.
  - eapply MemProps.mext_preserves_valid_ptrs; eauto.
  - eapply MemProps.mcast_preserves_valid_ptrs; eauto.
    eapply IHcnst; eauto.
  - des_ifs; try (by eapply MemProps.undef_valid_ptrs; eauto).
    eapply MemProps.mgep_preserves_valid_ptrs; eauto.
    unfold GV2ptr in *. des_ifs.
    ss. des_ifs. expl IHcnst.
  - des_ifs.
    + eapply IHcnst3; eauto.
    + eapply IHcnst2; eauto.
  - eapply MemProps.micmp_preserves_valid_ptrs; eauto.
  - eapply MemProps.mfcmp_preserves_valid_ptrs; eauto.
  - eapply MemProps.extractGenericValue_preserves_valid_ptrs; eauto.
    eapply IHcnst; eauto.
  - eapply MemProps.insertGenericValue_preserves_valid_ptrs; eauto.
    + expl IHcnst1.
    + expl IHcnst2.
  - eapply MemProps.mbop_preserves_valid_ptrs; eauto.
  - eapply MemProps.mfbop_preserves_valid_ptrs; eauto.
Qed.

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
  eapply MemProps.mstore_aux_never_produce_new_ptr; eauto.
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
  - inv STATE.
    exploit UNIQUE_PARENT_LOCAL; eauto.
  - inv MEM.
    exploit UNIQUE_PARENT_GLOBALS; eauto. intro GT_GMAX.
    inv STATE. ss.
    inv WF_VALUE.
    exploit wf_globals_const2GV; eauto.
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

Lemma vellvm_no_alias_is_diffblock
      conf gv1 gv2
  : MemProps.no_alias gv1 gv2 <->
    InvState.Unary.sem_diffblock conf gv1 gv2.
Proof.
  assert (NOALIAS_BLK_AUX:
            forall gv b,
              MemProps.no_alias_with_blk gv b <->
              ~ In b (GV2blocks gv)).
  { clear.
    induction gv; ss.
    destruct a. i.
    destruct v; ss.
    split.
    - ii. des; eauto.
      rewrite IHgv in *. eauto.
    - i. split.
      + ii. subst. eauto.
      + rewrite IHgv. eauto.
  }
  split; i.
  { unfold InvState.Unary.sem_diffblock.
    revert dependent gv1.
    induction gv2; i; ss.
    destruct a. unfold GV2blocks in *.
    destruct v; eauto.
    ss.
    cut (~ In b (filter_map (val2block <*> fst) gv1) /\
         list_disjoint (filter_map (val2block <*> fst) gv1)
                       (filter_map (val2block <*> fst) gv2)).
    { i. des.
      unfold list_disjoint in *.
      i. ss.
      des; subst; eauto.
      ii. clarify.
    }
    des.
    split; eauto.
    apply NOALIAS_BLK_AUX. eauto.
  }
  { unfold InvState.Unary.sem_diffblock in *.
    revert dependent gv1.
    induction gv2; i; ss.
    destruct a.
    destruct v; eauto.
    split.
    - apply NOALIAS_BLK_AUX.
      ii. unfold list_disjoint in *.
      exploit H; eauto. ss. eauto.
    - apply IHgv2.
      unfold list_disjoint in *.
      i.
      ii; clarify.
      exploit H; eauto. ss. right. eauto.
  }
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

(* lemmas for alloca *)
Lemma alloca_result
      TD mem mem' sz gn a mb
      (ALLOCA: alloca TD mem sz gn a = Some (mem', mb))
  : <<ALLOC_BLOCK: mb = mem.(Mem.nextblock)>> /\
    <<NEXT_BLOCK: mem'.(Mem.nextblock) = Pos.succ mem.(Mem.nextblock)>> /\
    <<GV2INT: exists z, GV2int TD Size.ThirtyTwo gn = Some z>>
.
Proof.
  unfold alloca in *.
  des_ifs. unfold option_map, flip in *. des_ifs.
  expl Mem.alloc_result. clarify.
  splits; ss.
  - erewrite Mem.nextblock_drop; eauto.
    eapply Mem.nextblock_alloc; eauto.
  - esplits; eauto.
Qed.

Ltac u_alloca := MemProps.u_alloca; des_ifs_safe.

Lemma valid_access_alloca_inv
      TD mem0 mem1 bsz gn a b mb p chunk ofs
      (ALLOCA: alloca TD mem0 bsz gn a = Some (mem1, mb))
      (VALID: Mem.valid_access mem1 chunk b ofs p)
      z
      (INT: GV2int TD Size.ThirtyTwo gn = Some z)
  : if Values.eq_block b mb
    then 0 <= ofs /\
         ofs + Memdata.size_chunk chunk <=
         (Size.to_Z bsz * z)%Z /\
         (Memdata.align_chunk chunk | ofs) /\
         Memtype.perm_order Memtype.Writable p
    else Mem.valid_access mem0 chunk b ofs p.
Proof.
  u_alloca.
  rename mem1 into mem2.
  rename m into mem1.
  dup VALID.
  unfold option_map in *. des_ifs_safe.
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
Unshelve.
{ by econs. }
{ by econs. }
Qed.

Lemma valid_access_alloca_same
      TD mem0 mem1 bsz gn a mb p chunk ofs
      (ALLOCA: alloca TD mem0 bsz gn a = Some (mem1, mb))
      z
      (INT: GV2int TD Size.ThirtyTwo gn = Some z)
      (OFS: 0 <= ofs /\
               ofs + Memdata.size_chunk chunk <=
               (Size.to_Z bsz * z)%Z /\
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
    apply Mem.alloc_result in Heq0. clarify.
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
  unfold alloca, option_map, flip in *. des_ifs_safe.
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
  eapply MemProps.mstore_aux_never_produce_new_ptr; eauto.
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
    clear - wf_globals_const2GV0 VAL GLOBALS.
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
          apply Pos.succ_le_mono in wf_globals_const2GV0.
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

(* invmem *)

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


Inductive mem_change : Type :=
| mem_change_alloca
    (def_var:id) (ty:typ) (s:sz) (gn:GenericValue) (a:align)
| mem_change_store
    (ptr:GenericValue) (ty:typ) (gv:GenericValue) (a:align)
| mem_change_free
    (ptr:GenericValue)
| mem_change_none
.

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

Lemma valid_ptr_alloca_diffblock
      SRC_MEM val'
      (VALID_PTR: MemProps.valid_ptrs (Memory.Mem.nextblock SRC_MEM) val')
      TD align0 tsz gn SRC_MEM_STEP mb
      (ALLOCA: alloca TD SRC_MEM tsz gn align0 = Some (SRC_MEM_STEP, mb))
      conf_src
  :
    <<DIFFBLOCK: InvState.Unary.sem_diffblock conf_src (blk2GV TD mb) val'>>
.
Proof.
  exploit MemProps.nextblock_alloca; try apply ALLOCA; []; ii; des.
  exploit MemProps.alloca_result; try apply ALLOCA; []; ii; des.
  subst.

  induction val'; ss.
  destruct a; ss.
  des; ss.
  destruct v; ss; try (eapply IHval'; eauto; fail).
  des; clarify.
  - ss. exploit Pos.lt_irrefl; eauto.
  - eapply IHval'; ss.
Qed.

Lemma locals_alloca_diffblock
      conf_src mem locals
      TD tsz gn align0 SRC_MEM_STEP mb
      reg val
      (ALLOCA: alloca TD mem tsz gn align0 = Some (SRC_MEM_STEP, mb))
      (VAL: lookupAL GenericValue locals reg = Some val)
      (WF_LOCAL: MemProps.wf_lc mem locals)
  :
  <<DIFFBLOCK: InvState.Unary.sem_diffblock conf_src (blk2GV TD mb) val>>
.
Proof.
  exploit WF_LOCAL; eauto; []; intro WF; des.
  eapply valid_ptr_alloca_diffblock; eauto.
Qed.

Lemma globals_alloca_diffblock
      align0 TD gn SRC_MEM SRC_MEM_STEP
      tsz conf_src mb
      gmax
      (WF_GLOBALS: genericvalues_inject.wf_globals gmax (Globals conf_src))
      (ALLOCA: alloca TD SRC_MEM tsz gn align0 = Some (SRC_MEM_STEP, mb))
      (WF_MEM: MemProps.wf_Mem gmax (CurTargetData conf_src) SRC_MEM)
  : (gmax < mb)%positive.
Proof.
  unfold MemProps.wf_Mem in *. des.
  exploit MemProps.nextblock_alloca; try apply ALLOCA; []; ii; des.
  exploit MemProps.alloca_result; try apply ALLOCA; []; ii; des. clarify.
Qed.

Lemma mload_alloca_diffblock
  align0 TD gn tsz conf_src SRC_MEM SRC_MEM_STEP mb
  (ALLOCA: alloca TD SRC_MEM tsz gn align0 = Some (SRC_MEM_STEP, mb))
  mptr0 typ0 align1 val'
  (LOAD: mload (CurTargetData conf_src) SRC_MEM_STEP mptr0 typ0 align1 = Some val')
  gmax
  (WF: MemProps.wf_Mem gmax (CurTargetData conf_src) SRC_MEM)
  :
  <<DIFFBLOCK: InvState.Unary.sem_diffblock conf_src (blk2GV TD mb) val'>>
.
Proof.
  inversion WF as [WF_A WF_B]. clear WF.
  (*
WTS
mb <-> val'
val': read from SRC_MEM_STEP.
if read from SRC_MEM -> use WF.
if read from SRC_MEM_STEP - SRC_MEM -> undef
   *)
  exploit MemProps.alloca_preserves_mload_inv; try apply LOAD; eauto; []; i.
  des.
  - exploit WF_A; try apply LOAD; eauto; []; clear WF_A; intros WF_A; des.
    eapply valid_ptr_alloca_diffblock; eauto.
  - eapply InvState.Unary.diffblock_comm.
    eapply InvState.Unary.undef_diffblock; eauto.
Unshelve.
eauto.
eauto.
Qed.
