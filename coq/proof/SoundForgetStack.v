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
Require Import Validator.
Require Import Postcond.
Require Import Exprs.
Require Import Hints.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Require Import Inject. (* TODO: for simtac *)
Require Import SoundPostcondCmdAdd.

Set Implicit Arguments.


(* Forget *)

Definition locals_equiv_except (ids:AtomSetImpl.t) (locals0 locals1:GVsMap): Prop :=
  forall id (NOT_MEM: AtomSetImpl.mem id ids = false),
    lookupAL _ locals0 id = lookupAL _ locals1 id.

Inductive state_equiv_except (ids:AtomSetImpl.t) (st0 st1: State): Prop :=
| state_eq_except_intro
    (MEM: st0.(Mem) = st1.(Mem))
    (LOCALS: locals_equiv_except ids st0.(EC).(Locals) st1.(EC).(Locals))
.

Ltac inv_state_equiv_except :=
  repeat match goal with
         | [H: state_equiv_except ?ids ?st0 ?st1 |- _] =>
           inv H; unfold locals_equiv_except in *
         end;
  repeat match goal with
         | [_:_ |- state_equiv_except ?ids ?st0 ?st1] =>
           econs; unfold locals_equiv_except in *
         end.

Program Instance Equivalence_state_equiv_except ids
  : Equivalence (state_equiv_except ids).
Next Obligation.
  ss.
Qed.
Next Obligation.
  ii. inv_state_equiv_except; symmetry; eauto.
Qed.
Next Obligation.
  ii. inv_state_equiv_except; eauto using eq_trans.
Qed.

Lemma sem_idT_equiv_except
      ids st0 st1 invst id gv
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_idT st0 invst (Tag.physical, id) = Some gv)
      (NOTIN: AtomSetImpl.mem id ids = false)
  : <<STATE: InvState.Unary.sem_idT st1 invst (Tag.physical, id) = Some gv>>.
Proof.
  unfold InvState.Unary.sem_idT in *.
  inv EQUIV.
  unfold locals_equiv_except in LOCALS.
  red. rewrite <- STATE.
  symmetry. eapply LOCALS; eauto.
Qed.

Lemma sem_valueT_equiv_except
      ids st0 st1 invst v gv
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_valueT conf st0 invst v = Some gv)
      (NOTIN: (LiftPred.ValueT (flip IdTSet.mem (lift_physical_atoms_idtset ids))) v = false)
  : <<STATE: InvState.Unary.sem_valueT conf st1 invst v = Some gv>>.
Proof.
  unfold flip in NOTIN.
  destruct v; ss. destruct x. destruct t; ss.
  rewrite lift_physical_atoms_idtset_spec1 in *.
  eapply sem_idT_equiv_except; eauto.
Qed.

Lemma sem_list_valueT_equiv_except
      ids st0 st1 invst lsv gvs
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_list_valueT conf st0 invst lsv = Some gvs)
      (NOTIN: existsb (LiftPred.ValueT (flip IdTSet.mem (lift_physical_atoms_idtset ids)) <*> snd) lsv = false)
  : <<STATE: InvState.Unary.sem_list_valueT conf st1 invst lsv = Some gvs>>.
Proof.
  unfold flip in NOTIN.
  revert gvs STATE NOTIN.
  induction lsv; ss.
  i. simtac.
  apply orb_false_iff in NOTIN. des.
  exploit sem_valueT_equiv_except; eauto. i. des.
  des_ifs; exploit IHlsv; eauto; i; des; clarify.
Qed.

Ltac solve_equiv_except_val st0 :=
  repeat match goal with
         | [H: _ || LiftPred.ValueT _ _ = false |- _] =>
           apply orb_false_iff in H;des
         | [H: LiftPred.ValueT _ _ || _ = false |- _] =>
           apply orb_false_iff in H;des
         end;
  repeat match goal with
         | [H: InvState.Unary.sem_valueT _ st0 _ _ = Some _ |- _] =>
           eapply sem_valueT_equiv_except in H; eauto; rewrite H
         end.

Lemma sem_expr_equiv_except
      conf invst
      ids st0 st1 e val
      (EQUIV: state_equiv_except ids st0 st1)
      (FILTER: (LiftPred.Expr (flip IdTSet.mem (lift_physical_atoms_idtset ids))) e = false)
      (SEM_EXPR: InvState.Unary.sem_expr conf st0 invst e = Some val)
  : <<SEM_EXPR: InvState.Unary.sem_expr conf st1 invst e = Some val>>.
Proof.
  unfold compose in FILTER.
  destruct e; ss; simtac;
    try (solve_equiv_except_val st0; eauto).
  - erewrite sem_list_valueT_equiv_except; eauto.
  - rewrite COND2. eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
Qed.

Lemma forget_stack_unary_Subset
      defs leaks inv0
  : Invariant.Subset_unary (ForgetStack.unary defs leaks inv0) inv0.
Proof.
  unfold ForgetStack.unary.
  econs; ss; ii.
  - eapply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
  - econs; ii.
    + eapply ValueTPairSetFacts.filter_iff in H; try by solve_compat_bool.
      des. eauto.
    + eapply PtrPairSetFacts.filter_iff in H; try by solve_compat_bool.
      des. eauto.
  - eapply AtomSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
  - eapply IdTSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
Qed.

Lemma forget_stack_Subset
      def_src def_tgt inv0
      leaks_src leaks_tgt
  : Invariant.Subset (ForgetStack.t def_src def_tgt leaks_src leaks_tgt inv0) inv0.
Proof.
  unfold ForgetStack.t.
  econs; ss;
    try apply forget_stack_unary_Subset.
  ii.
  apply IdTSet.union_3. eauto.
Qed.

(* soundness *)

Inductive unique_preserved_except conf inv unique_parent st gmax except_for : Prop :=
| unique_preserved_except_intro
    (UNIQUE_PRESERVED_INV:
       forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true)
         (NO_LEAK: AtomSetImpl.mem u except_for = false),
         InvState.Unary.sem_unique conf st gmax u)
    (UNIQUE_PRESERVED_PARENT_LOCAL:
       forall x ptr
         (PTR:lookupAL _ st.(EC).(Locals) x = Some ptr),
         InvMem.gv_diffblock_with_blocks conf ptr unique_parent)
    (UNIQUE_PRESERVED_PARENT_MEM:
       forall mptr typ align val'
         (LOAD: mload conf.(CurTargetData) st.(Mem) mptr typ align = Some val'),
         InvMem.gv_diffblock_with_blocks conf val' unique_parent)
    (UNIQUE_PRESERVED_PARENT_GLOBALS:
       forall b (IN: In b unique_parent), (gmax < b)%positive)
.

Require Import memory_props.
Import MemProps.

Lemma mbop_multiple_result_inv
      TD bop sz gvs1 gvs2 val1 val2 vals
      (MBOP: mbop TD bop sz gvs1 gvs2 = Some (val1 :: val2 :: vals))
  :
    gundef TD (typ_int sz) = Some (val1 :: val2 :: vals)
.
Proof.
  unfold mbop in *.
  des_ifs.
Qed.

Lemma mbop_no_result_inv
      TD bop sz gvs1 gvs2
      (MBOP: mbop TD bop sz gvs1 gvs2 = Some (nil))
  :
    gundef TD (typ_int sz) = Some (nil)
.
Proof.
  unfold mbop in *.
  des_ifs.
Qed.

Lemma no_alias_not_in_gv_blocks
      gval1 b
      (NOALIAS: no_alias_with_blk gval1 b)
      (IN: In b (GV2blocks gval1))
  :
    False
.
Proof.
  induction gval1; ss.
  destruct a; ss.
  destruct v; ss; try (exploit IHgval1; eauto; fail).
  des;clarify.
  exploit IHgval1; eauto.
Qed.

Lemma no_alias_diffblock
      conf gval1 gval2
      (NOALIAS: no_alias gval1 gval2)
  :
    <<DIFFBLOCK: InvState.Unary.sem_diffblock conf gval1 gval2>>
.
Proof.
  generalize dependent gval1.
  induction gval2; ii; ss; des; ss.
  destruct a; ss.
  destruct v; ss; try (exploit IHgval2; eauto; fail).
  (* des. exploit IHgval2; eauto. esplits; eauto. *)
  des.
  - clarify.
    eapply no_alias_not_in_gv_blocks; eauto.
    (* eapply no_alias_with_blk__neq_blk in NOALIAS; eauto. *)
  - exploit IHgval2; eauto.
Qed.

Lemma diffblock_with_blocks_any_diffblock_any
      conf valx
      (DIFFBLOCK: forall blocks, InvMem.gv_diffblock_with_blocks conf valx blocks)
  :
    <<DIFFBLOCK: forall gvs, InvState.Unary.sem_diffblock conf valx gvs>>
.
Proof.
  ii. eapply DIFFBLOCK; eauto.
Qed.

Lemma no_embedded_ptrs_diffblock_with_blocks
      val blocks
      (NO_PTR: no_embedded_ptrs val)
  :
    (* moving conf above : (to premise) will make Unshelved goals in BOP_diffblock_with_blocks *)
  <<DIFFBLOCK: forall conf, InvMem.gv_diffblock_with_blocks conf val blocks>>
.
Proof.
  induction val; ii; ss.
  des_ifs; ss; exploit IHval; eauto.
Qed.

Lemma undef_implies_diffblock_with_blocks
      TD ty1 valx conf
      (UNDEF: gundef TD ty1 = Some valx)
  :
    <<DIFFBLOCK: forall blocks, InvMem.gv_diffblock_with_blocks conf valx blocks>>
.
Proof.
  unfold gundef in *.
  des_ifs.
  clear Heq.
  induction l0; ii; ss; des; ss.
  exploit IHl0; eauto.
Qed.

Lemma undef_implies_diffblock
      TD ty1 valx conf valy
      (UNDEF: gundef TD ty1 = Some valx)
  :
    InvState.Unary.sem_diffblock conf valx valy
.
Proof.
  ii. exploit undef_implies_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma BOP_diffblock_with_blocks
      S TD Ps gl fs
      lc bop sz v1 v2 val
      (H : BOP TD lc gl bop sz v1 v2 = Some val)
  : <<DIFFBLOCK: forall blocks, InvMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
Proof.
  apply opsem_props.OpsemProps.BOP_inversion in H. des.
  apply mbop_preserves_no_embedded_ptrs in H1.
  red; i.
  eapply no_embedded_ptrs_diffblock_with_blocks; eauto.
Qed.

Lemma BOP_diffblock
      S TD Ps gl fs
      lc bop sz v1 v2 val ptr
      (H : BOP TD lc gl bop sz v1 v2 = Some val)
  : InvState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit BOP_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma FBOP_diffblock_with_blocks
      S TD Ps gl fs
      lc fbop sz v1 v2 val
      (H : FBOP TD lc gl fbop sz v1 v2 = Some val)
  : <<DIFFBLOCK: forall blocks, InvMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
Proof.
  apply opsem_props.OpsemProps.FBOP_inversion in H. des.
  apply mfbop_preserves_no_embedded_ptrs in H1.
  red; i.
  eapply no_embedded_ptrs_diffblock_with_blocks; eauto.
Qed.

Lemma FBOP_diffblock
      S TD Ps gl fs
      lc fbop sz v1 v2 val ptr
      (H : FBOP TD lc gl fbop sz v1 v2 = Some val)
  : InvState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit FBOP_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma TRUNC_diffblock_with_blocks
      S TD Ps gl fs lc val
      truncop1 typ1 value1 typ2
      (H: TRUNC TD lc gl truncop1 typ1 value1 typ2 = Some val)
  : <<DIFFBLOCK: forall blocks, InvMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
Proof.
  apply opsem_props.OpsemProps.TRUNC_inversion in H. des.
  apply mtrunc_preserves_no_embedded_ptrs in H0.
  red; i.
  eapply no_embedded_ptrs_diffblock_with_blocks; eauto.
Qed.

Lemma TRUNC_diffblock
      S TD Ps gl fs lc val ptr
      truncop1 typ1 value1 typ2
      (H: TRUNC TD lc gl truncop1 typ1 value1 typ2 = Some val)
  : InvState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit TRUNC_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma EXT_diffblock_with_blocks
      S TD Ps gl fs lc val
      extop1 typ1 value1 typ2
      (H: EXT TD lc gl extop1 typ1 value1 typ2 = Some val)
  : <<DIFFBLOCK: forall blocks, InvMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
Proof.
  apply opsem_props.OpsemProps.EXT_inversion in H. des.
  apply mext_preserves_no_embedded_ptrs in H0.
  red; i.
  eapply no_embedded_ptrs_diffblock_with_blocks; eauto.
Qed.

Lemma EXT_diffblock
      S TD Ps gl fs lc val ptr
      extop1 typ1 value1 typ2
      (H: EXT TD lc gl extop1 typ1 value1 typ2 = Some val)
  : InvState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit EXT_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma micmp_preserves_no_embedded_ptrs
      td cnd ty vx vy vres
      (MICMP: micmp td cnd ty vx vy = Some vres)
  :
    <<NO_PTR: no_embedded_ptrs vres>>
.
Proof.
  unfold micmp in *. des_ifs.
  - eapply micmp_int_preserves_no_embedded_ptrs; eauto.
  - eapply undef__no_embedded_ptrs; eauto.
Qed.

Lemma ICMP_diffblock_with_blocks
      S TD Ps gl fs lc val
      cond1 typ1 value1 value2
      (H: ICMP TD lc gl cond1 typ1 value1 value2 = Some val)
  : <<DIFFBLOCK: forall blocks, InvMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
Proof.
  apply opsem_props.OpsemProps.ICMP_inversion in H. des.
  apply micmp_preserves_no_embedded_ptrs in H1.
  red; i.
  eapply no_embedded_ptrs_diffblock_with_blocks; eauto.
Qed.

Lemma ICMP_diffblock
      S TD Ps gl fs lc val ptr
      cond1 typ1 value1 value2
      (H: ICMP TD lc gl cond1 typ1 value1 value2 = Some val)
  : InvState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit ICMP_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma mfcmp_preserves_no_embedded_ptrs
      td cnd ty vx vy vres
      (MFCMP: mfcmp td cnd ty vx vy = Some vres)
  :
    <<NO_PTR: no_embedded_ptrs vres>>
.
Proof.
  unfold mfcmp in *. red.
  des_ifs; cbn in *; try (eapply undef__no_embedded_ptrs; eauto; fail); try (des_ifs; fail).
Qed.

Lemma FCMP_diffblock_with_blocks
      S TD Ps gl fs lc val
      fcond1 floating_point1 value1 value2
      (H: FCMP TD lc gl fcond1 floating_point1 value1 value2 = Some val)
  : <<DIFFBLOCK: forall blocks, InvMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
Proof.
  apply opsem_props.OpsemProps.FCMP_inversion in H. des.
  apply mfcmp_preserves_no_embedded_ptrs in H1.
  red; i.
  eapply no_embedded_ptrs_diffblock_with_blocks; eauto.
Qed.

Lemma FCMP_diffblock
      S TD Ps gl fs lc val ptr
      fcond1 floating_point1 value1 value2
      (H: FCMP TD lc gl fcond1 floating_point1 value1 value2 = Some val)
  : InvState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit FCMP_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma GEP_diffblock
  (invmem : InvMem.Unary.t)
  (inbounds5 : inbounds)
  (typ5 : typ)
  (value_5 : value)
  (l0 : list (sz * value))
  (typ' : typ)
  (gmax : positive)
  (u : atom)
  (S : system)
  (TD : TargetData)
  (Ps : list product)
  (F : fdef)
  (B : block)
  (lc : GVsMap)
  (gl fs : GVMap)
  (vidxs : list GenericValue)
  (mp : GenericValue)
  (tmn : terminator)
  (Mem0 : mem)
  (als : list mblock)
  (NEXTBLOCK : Memory.Mem.nextblock Mem0 = InvMem.Unary.nextblock invmem)
  (GLOBALS : genericvalues_inject.wf_globals gmax gl)
  (WF : wf_Mem gmax TD Mem0)
  (H : getOperandValue TD value_5 lc gl = Some mp)
  (val : GenericValue)
  (VAL : lookupAL GenericValue lc u = Some val)
  (LOCALS : forall (reg : atom) (val' : GenericValue),
           u <> reg ->
           lookupAL GenericValue lc reg = Some val' ->
           InvState.Unary.sem_diffblock
             {|
             CurSystem := S;
             CurTargetData := TD;
             CurProducts := Ps;
             Globals := gl;
             FunTable := fs |} val val')
  (MEM : forall (mptr : mptr) (typ : typ) (align : align) (val' : GenericValue),
        mload TD Mem0 mptr typ align = Some val' ->
        InvState.Unary.sem_diffblock
          {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |} val val')
  (GLOBALS0 : forall b : Values.block, In b (GV2blocks val) -> (gmax < b)%positive)
  (reg : atom)
  (val' : GenericValue)
  (REG : u <> reg)
  (NOT_LEAKED_U : AtomSetImpl.mem u
                   (AtomSetImpl_from_list
                      (Cmd.get_leaked_ids (insn_gep reg inbounds5 typ5 value_5 l0 typ'))) =
                 false)
  (H1 : GEP TD typ5 mp vidxs inbounds5 typ' = Some val')
  (WF_INSNS: forall (insn : insn) (b : block),
             insnInBlockB insn b /\ blockInFdefB b F ->
             <<WF_INSN: wf_insn S (module_intro (fst TD) (snd TD) Ps) F b insn >>)
  :
  <<DIFFBLOCK: InvState.Unary.sem_diffblock
    {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}
    val val'>>
.
Proof.
  (* i; des. *)
  unfold GEP in *. unfold gep in *. unfold genericvalues.LLVMgv.GEP in *.
  assert(TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT: True) by ss.
  move val at bottom.
  eapply InvState.Unary.diffblock_comm.
  destruct (GV2ptr TD (getPointerSize TD) mp) eqn:T1; cycle 1.
  { eapply undef_implies_diffblock; eauto. }
  destruct (GVs2Nats TD vidxs) eqn:T2; cycle 1.
  { eapply undef_implies_diffblock; eauto. }
  destruct (mgep TD typ5 v l1) eqn:T3; cycle 1.
  { eapply undef_implies_diffblock; eauto. }
  clarify. ss.
  {
    assert (BLOCK_IN_FDEF: blockInFdefB B F).
    { admit. } (* wf_EC *)
    assert (INSN_IN_BLOCK: insnInBlockB (insn_cmd (insn_gep reg inbounds5 typ5 value_5 l0 typ')) B).
    { admit. } (* wf_EC *)
    exploit WF_INSNS; eauto; []; intro WF_INSN; des.
    clear BLOCK_IN_FDEF INSN_IN_BLOCK.

    ii.
    destruct v0; ss; des; ss.
    clarify.
    apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U.
    apply AtomSetImpl_from_list_spec2 in NOT_LEAKED_U.
    unfold Cmd.get_leaked_ids in *.
    ss.
    {
      symmetry in T3. apply mgep_inv in T3. des. clarify.
      destruct value_5; ss.
      -
        apply not_or_and in NOT_LEAKED_U.
        des.
        hexploit LOCALS; try apply H; eauto; []; ii; des.
        (* b0 <-> b0 *)
        destruct mp; ss. destruct p, v; ss.
        destruct mp; ss. clarify.
        unfold InvState.Unary.sem_diffblock in *.
        unfold list_disjoint in *.
        eapply H0; eauto. ss. left; ss.
      -
        (* const5 -> mp -> Vptr b <= gmax *)
        rename val into __val__.
        rename u into __u__.
        rename b into __b__.
        destruct TD; ss.
        apply TODOProof.wf_globals_eq in GLOBALS.
        exploit const2GV_valid_ptrs; eauto.
        { inv WF_INSN. inv H11. eauto. }
        intro VALID_PTR; des. clear WF_INSN.
        ss.
        idtac.
        exploit valid_ptr_globals_diffblock; eauto.
        eapply {| CurSystem := S; CurTargetData := (l2, n);
                  CurProducts := Ps; Globals := gl; FunTable := fs |}.
        destruct mp; ss. destruct p; ss. destruct v; ss. des. des_ifs.
        left; ss.
    }
Admitted.

(* care for quantification position of the "blocks".
If it is inside getOperand_diffblock && DIFFBLOCK, this lemma is not usable in intended use case. *)
Lemma CAST_diffblock_with_blocks
      S Ps fs val1
      TD lc gl castop0 t1 v1 t2
      (H: CAST TD lc gl castop0 t1 v1 t2 = Some val1)
      blocks
      (getOperand_diffblock: forall v2 val2,
          getOperandValue TD v2 lc gl = Some val2 ->
          InvMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val2 blocks)
  : <<DIFFBLOCK: InvMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val1 blocks>>.
Proof.
  red; i.
  apply opsem_props.OpsemProps.CAST_inversion in H. des.
  unfold mcast in *.
  des_ifs; try (eapply undef_implies_diffblock_with_blocks; eauto; fail);
    try (apply mbitcast_inv in H0; clarify; []; hexploit getOperand_diffblock; eauto).
Qed.

(* Definition leaks_diffblock_with conf st cmd ptr: Prop := *)
(*   forall v gv *)
(*     (IN_LEAK: In v (Cmd.get_leaked_values cmd)) *)
(*     (VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gv), *)
(*     InvState.Unary.sem_diffblock conf ptr gv. *)

(* Lemma operands_diffblock *)
(*       conf st gmax cmd *)
(*       u uptr *)
(*       (UNIQUE_U: InvState.Unary.sem_unique conf st gmax u) *)
(*       (NOT_LEAKED: AtomSetImpl.mem u (AtomSetImpl_from_list *)
(*                                         (Cmd.get_leaked_ids cmd)) = false) *)
(*       (U_VALUE : lookupAL GenericValue st.(EC).(Locals) u = Some uptr) *)
(*   : leaks_diffblock_with conf st cmd uptr. *)
(* Proof. *)
(*   unfold leaks_diffblock_with. *)
(*   ii. *)
(*   unfold Cmd.get_leaked_values in *. *)
(*   unfold Cmd.get_leaked_ids in *. *)
(*   inv UNIQUE_U. *)
(*   remember cmd as CCC. *)
(*   rewrite HeqCCC in IN_LEAK. *)
(*   destruct cmd; ss; des. (* ; subst *) *)
(*   - subst. *)
(*     rename v into vvvv. *)
(*     rename vvvv into v. *)
(*     destruct v; ss. *)
(*     + *)
(*       clarify. rename u into uuu. *)
(*       eapply LOCALS; eauto. *)
(*       apply_all_once AtomSetFacts.not_mem_iff. *)
(*       apply_all_once AtomSetImpl_from_list_spec2. *)
(*       ii. subst. apply NOT_LEAKED. econs. ss. *)
(*     + admit. *)
(*       (* may need some wf coditions *) *)
(*       (* const2GV_disjoint_with_runtime_alloca *) *)
(* Adm-itted. *)

(* Lemma extractGenericValue_diffblock *)
(*       conf st cmd *)
(*       x ty1 v lc ty2 *)
(*       ptr gv l0 val *)
(*       (CMD: cmd = insn_extractvalue x ty1 v lc ty2) *)
(*       (VAL : getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gv) *)
(*       (OPERANDS_DIFFBLOCK: leaks_diffblock_with conf st cmd ptr) *)
(*       (RES: extractGenericValue conf.(CurTargetData) ty1 gv l0 = Some val) *)
(*   : InvState.Unary.sem_diffblock conf ptr val. *)
(* Proof. *)
(*   subst. *)
(*   unfold leaks_diffblock_with in *. *)
(*   unfold Cmd.get_leaked_values in *. *)
(*   eapply OPERANDS_DIFFBLOCK; try econs; eauto. clear OPERANDS_DIFFBLOCK. *)
(*   rewrite VAL. clear VAL. *)
(*   unfold extractGenericValue in *. *)
(*   des_ifs. *)
(* Adm-itted. *)

Lemma extractValue_sub
      TD typ5 gvs l0 val'
      (EXTRACT: extractGenericValue TD typ5 gvs l0 = Some val')
  :
    <<SUB: List.incl val' gvs \/ exists t, <<UNDEF: (gundef TD t) = Some val'>> >>
.
Proof.
  unfold extractGenericValue in *.
  des_ifs.
  unfold mget' in *.
  des_ifs; cycle 1.
  { right; eexists; eauto. }
  left.
  clear Heq0 Heq.
  unfold mget in *.
  unfold monad.mbind in *.
  des_ifs.
  apply_all_once splitGenericValue_spec1.
  des.
  clarify.
  eapply incl_appr; eauto.
  eapply incl_appl; eauto.
  eapply incl_refl; eauto.
Qed.

Lemma insertValue_sub
      TD typ5 gvs l0 typ' gvs' val'
      (INSERT: insertGenericValue TD typ5 gvs l0 typ' gvs' = Some val')
  :
    <<SUB: List.incl val' (gvs ++ gvs') \/ exists t, <<UNDEF: (gundef TD t) = Some val'>> >>
.
Proof.
  unfold insertGenericValue in *.
  des_ifs.
  unfold mset' in *.
  des_ifs; cycle 1.
  { right; eexists; eauto. }
  left.
  clear Heq0 Heq.
  unfold mset in *.
  unfold monad.mbind in *.
  des_ifs.
  apply_all_once splitGenericValue_spec1.
  des.
  clarify.
  ii.
  repeat (apply_all_once in_app; des).
  - repeat (apply in_app; left); ss.
  - repeat (apply in_app; right); ss.
  - apply in_app; left.
    repeat (apply in_app; right); ss.
Qed.

Lemma step_unique_preserved_except_current
      conf st0 st1 evt
      invst invmem inv0
      cmd cmds
      gmax public
      (STATE: InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst invmem gmax public inv0)
      (WF_LC_BEFORE: wf_lc st0.(Mem) st0.(EC).(Locals))
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem)
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : << UNIQUE_CURRENT:
    forall u : atom,
      AtomSetImpl.mem u (Invariant.unique inv0) = true ->
      AtomSetImpl.mem u
                      (union (AtomSetImpl_from_list (Cmd.get_def cmd))
                             (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd))) = false ->
      InvState.Unary.sem_unique conf st1 gmax u>>.
Proof.
  intros u MEM_U NOT_LEAKED_U0.
  apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U0.
  hexploit notin_union_1; eauto. intros NOT_DEF_U.
  hexploit notin_union_2; eauto. intros NOT_LEAKED_U. clear NOT_LEAKED_U0.
  apply AtomSetFacts.not_mem_iff in NOT_DEF_U.
  apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U.

  inv STATE. inv MEM.
  exploit UNIQUE; eauto.
  { apply AtomSetFacts.mem_iff. eauto. }
  intros UNIQUE_BEF.
  clear UNIQUE MEM_U.

  (* Ltac solve_unique_not_def := *)
  (*   try by match goal with *)
  (*          | [H: AtomSetImpl.mem ?u (AtomSetImpl_from_list [?x]) = false |- *)
  (*             lookupAL _ (updateAddAL _ ?lc ?x _) ?u = Some _ ] => *)
  (*            rewrite <- lookupAL_updateAddAL_neq; eauto; *)
  (*            apply AtomSetImpl_singleton_mem_false; eauto *)
  (*          end. *)
  Ltac clarify_not_def :=
    match goal with
    | [H: AtomSetImpl.mem ?u (AtomSetImpl_from_list [?x]) = false |- _] =>
      apply AtomSetImpl_singleton_mem_false in H
    end.

  Ltac narrow_down_unique :=
    try
      (clarify_not_def;
       econs; eauto; ss;
       [by rewrite <- lookupAL_updateAddAL_neq; eauto |
        i;
        match goal with
        | [H: lookupAL _ (updateAddAL _ ?lc ?x _) ?reg = Some _ |- _] =>
          destruct (id_dec x reg); [|by rewrite <- lookupAL_updateAddAL_neq in *; eauto]
        end; subst;
        rewrite lookupAL_updateAddAL_eq in *; clarify]).
  clear LESSDEF NOALIAS PRIVATE.
  inv STEP; destruct cmd; ss; clarify; try by inv UNIQUE_BEF; econs; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply BOP_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply FBOP_diffblock; eauto.
  -
    (* inv UNIQUE_BEF; narrow_down_unique. *)
    inversion UNIQUE_BEF; subst; narrow_down_unique.
    ii.
    rename val into __val__.
    apply extractValue_sub in H0.
    des; cycle 1.
    { exploit undef_implies_diffblock; eauto. ii; ss. }
    assert(TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT: True) by ss.
    move val' at bottom.
    move gvs at bottom.
    assert(list_disjoint (GV2blocks __val__) (GV2blocks gvs)).
    {
      clear - VAL H LOCALS NOT_LEAKED_U UNIQUE_BEF GLOBALS.
      destruct value5; ss.
      { eapply LOCALS; eauto.
        { compute in NOT_LEAKED_U.
          apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U.
          eapply notin_add_1 in NOT_LEAKED_U. ii; subst; ss. }
      }
      { hexploit unique_const_diffblock; ss; eauto. }
    }
    clear - INL INR H0 H1.
    exploit In_incl; eauto.
    eapply GV2blocks_incl; eauto.
  -
    inversion UNIQUE_BEF; subst; narrow_down_unique.
    ii.
    rename val into __val__.
    (* move value5 at bottom. *)
    (* destruct value5; ss. *)
    apply insertValue_sub in H1.
    des; cycle 1.
    { exploit undef_implies_diffblock; eauto. ii; ss. }
    assert(TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT: True) by ss.
    move val' at bottom.
    move gvs at bottom.
    move gvs' at bottom.
    assert(list_disjoint (GV2blocks __val__) (GV2blocks gvs)).
    {
      clear - VAL H LOCALS NOT_LEAKED_U UNIQUE_BEF GLOBALS.
      destruct value5; ss.
      { eapply LOCALS; eauto.
        { compute in NOT_LEAKED_U.
          apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U.
          ii; subst; ss.
          des_ifs.
          - eapply notin_add_2 in NOT_LEAKED_U. eapply notin_add_1 in NOT_LEAKED_U. ss.
          - eapply notin_add_1 in NOT_LEAKED_U. ss.
        }
      }
      { hexploit unique_const_diffblock; ss; eauto. }
    }
    assert(list_disjoint (GV2blocks __val__) (GV2blocks gvs')).
    {
      clear - VAL H0 LOCALS NOT_LEAKED_U UNIQUE_BEF GLOBALS.
      destruct value'; ss.
      { eapply LOCALS; eauto.
        { compute in NOT_LEAKED_U.
          apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U.
          ii; subst; ss.
          des_ifs.
          - eapply notin_add_1 in NOT_LEAKED_U. ss.
          - eapply notin_add_1 in NOT_LEAKED_U. ss.
        }
      }
      { hexploit unique_const_diffblock; ss; eauto. }
    }
    clear - H2 H3 H1 INR INL.
    exploit In_incl.
    { eapply INR. }
    { instantiate (1:= (GV2blocks (gvs ++ gvs'))). eapply GV2blocks_incl; eauto. }
    intro IN.
    (* unfold list_disjoint in *. *)

    {
      eapply GV2blocks_app_inv in IN.
      des.
      -
        apply GV2blocks_in_inv in IN.
        des.
        eapply H2; eauto.
        eapply GV2blocks_lift; eauto.
      -
        apply GV2blocks_in_inv in IN.
        des.
        eapply H3; eauto.
        eapply GV2blocks_lift; eauto.
    }
  - (* malloc *)
    inv UNIQUE_BEF; narrow_down_unique.
    assert(TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT: True) by reflexivity.
    move val at bottom.
    move mb at bottom.
    hexploit locals_malloc_diffblock; eauto; []; ii; des.
    unfold InvState.Unary.sem_diffblock in H2.
    unfold list_disjoint in H2.
    eapply H2; eauto.
  - (* alloca *)
    inv UNIQUE_BEF; narrow_down_unique.
    ii.
    exploit locals_malloc_diffblock; eauto.
    apply {|
        CurSystem := S;
        CurTargetData := TD;
        CurProducts := Ps;
        Globals := gl;
        FunTable := fs |}.
  - (* load *)
    inv UNIQUE_BEF; narrow_down_unique.
    eapply MEM; eauto.
  - (* GEP *)
    inv UNIQUE_BEF; narrow_down_unique.
    eapply GEP_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply TRUNC_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply EXT_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    (* specialize (LOCALS reg val' REG). *)
    unfold CAST in *. des_ifs. apply mcast_inv in H.
    des; cycle 1.
    +
      apply InvState.Unary.diffblock_comm.
      eapply undef_implies_diffblock; eauto.
    +
      subst.
      unfold getOperandValue in *.
      des_ifs; cycle 1.
      * ss.
        rename g into __g__.
        rename val into __val__.
        exploit TODOProof.wf_globals_const2GV; eauto; []; i; des.
        eapply valid_ptr_globals_diffblock; eauto.
      * eapply LOCALS; try apply Heq; eauto.
        apply AtomSetFacts.not_mem_iff in NOT_LEAKED_U.
        apply AtomSetImpl_from_list_spec2 in NOT_LEAKED_U.
        ss.
        ii. subst. apply not_or_and in NOT_LEAKED_U.
        des. apply NOT_LEAKED_U. ss.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply ICMP_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply FCMP_diffblock; eauto.
  - (* select *)
    inv UNIQUE_BEF; narrow_down_unique.
    rename val into ___val___.
    move gvs1 at bottom.
    move gvs2 at bottom.
    unfold getOperandValue in *.
    destruct decision; ss.
    { clear H1.
      destruct value1; ss.
      {
        apply_all_once AtomSetFacts.not_mem_iff.
        apply_all_once AtomSetImpl_from_list_spec2.
        unfold Cmd.get_leaked_ids in *. ss.
        eapply LOCALS; try apply H0; eauto.
        {
          ii. apply NOT_LEAKED_U. subst.
          destruct value0; ss.
          - right. left. ss.
          - left. ss.
        }
      }
      {
        exploit TODOProof.wf_globals_const2GV; eauto; []; intro VALID_PTR; des.
        eapply valid_ptr_globals_diffblock; eauto.
      }
    }
    { clear H0.
      destruct value2; ss.
      {
        apply_all_once AtomSetFacts.not_mem_iff.
        apply_all_once AtomSetImpl_from_list_spec2.
        unfold Cmd.get_leaked_ids in *. ss.
        eapply LOCALS; try apply H1; eauto.
        {
          ii. apply NOT_LEAKED_U. subst.
          destruct value0; ss.
          - right. destruct (Value.get_ids value1); ss.
            + right. left. ss.
            + left. ss.
          - destruct (Value.get_ids value1); ss.
            + right. left. ss.
            + left. ss.
        }
      }
      {
        exploit TODOProof.wf_globals_const2GV; eauto; []; intro VALID_PTR; des.
        eapply valid_ptr_globals_diffblock; eauto.
      }
    }
Unshelve.
apply {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}.
apply {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}.
apply {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}.
apply {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}.
Qed.

Lemma step_unique_preserved_except_parent
      conf st0 st1 evt
      invst invmem inv0
      cmd cmds
      gmax public
      (STATE: InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst invmem gmax public inv0)
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem)
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : <<UNIQUE_PARENT:
    forall (x : atom) (ptr : GenericValue),
      lookupAL GenericValue (Locals (EC st1)) x = Some ptr ->
      InvMem.gv_diffblock_with_blocks conf ptr (InvMem.Unary.unique_parent invmem)>>.
Proof.
  red; i.
  inv STATE. clear LESSDEF NOALIAS UNIQUE PRIVATE WF_LOCAL WF_PREVIOUS WF_GHOST WF_INSNS.
  inv STEP; ss; clarify.
  - (* nop *) eapply UNIQUE_PARENT_LOCAL; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply BOP_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply FBOP_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    destruct v; ss.
    { hexploit UNIQUE_PARENT_LOCAL; eauto; []; intro VALID_PTR; des.
      (* ptr is from gvs *)
      admit. }
    { exploit TODOProof.wf_globals_const2GV; eauto; [apply MEM|]; intro VALID_PTR; des.
      (* gvs <= gmax *)
      (* ptr <= gmax *)
      (* gmax < unique_parent *)
      admit. }
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    admit. (* insertGenericvalue *)
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    (* eapply valid_ptr_malloc_diffblock; eauto. *)
    (* hexploit locals_malloc_diffblock; eauto. *)
    admit. (* malloc *)
  - (* free *) eapply UNIQUE_PARENT_LOCAL; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    admit. (* malloc *)
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply MEM; eauto.
  - (* store *) eapply UNIQUE_PARENT_LOCAL; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    (* gep *) admit.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply TRUNC_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply EXT_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    idtac.
    eapply CAST_diffblock_with_blocks; eauto.
    { i. destruct v2; ss.
      - eapply UNIQUE_PARENT_LOCAL; eauto.
      - eapply TODOProof.wf_globals_const2GV in H; [|apply MEM]; des.
        (* unique_parent > gmax, val2 <= gmax *)
        admit.
    }
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply ICMP_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply FCMP_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    (* select *) admit.
Admitted.

Lemma step_unique_preserved_except
      conf st0 st1 evt
      invst invmem inv0
      cmd cmds
      gmax public
      (STATE: InvState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst invmem gmax public inv0)
      (WF_LC_BEFORE: wf_lc st0.(Mem) st0.(EC).(Locals))
      (MEM: InvMem.Unary.sem conf gmax public st1.(Mem) invmem)
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : unique_preserved_except conf inv0 invmem.(InvMem.Unary.unique_parent) st1 gmax
                            (AtomSetImpl.union (AtomSetImpl_from_list (Cmd.get_def cmd))
                                               (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd))).
Proof.
  hexploit step_unique_preserved_except_current; eauto. i.
  hexploit step_unique_preserved_except_parent; eauto. i.
  inv STATE. inv MEM.
  econs; eauto.
Qed.


(* Ltac rename_id_res x:= *)
(*   match goal with *)
(*   | [H: lookupAL _ (updateAddAL _ _ ?id _) ?reg = Some _ |- _] => *)
(*     rename id into x *)
(*   end. *)
(* inv STEP; ss; destruct cmd; ss; inv CMDS. *)
(* - (* nop *) *)
(*   ii. apply AtomSetFacts.mem_iff in MEM. *)
(*   specialize (STATE _ MEM). *)
(*   inv STATE. ss. *)
(*   econs; ss; eauto. *)
(* - (* bop *) *)
(*   ii. rewrite AtomSetFacts.union_b in NO_LEAK. ss. *)
(*   solve_des_bool. *)
(*   apply AtomSetImpl_singleton_mem_false in NO_LEAK. *)
(*   apply AtomSetFacts.mem_iff in MEM. *)
(*   specialize (STATE _ MEM). *)
(*   inv STATE. *)

(*   econs; ss; eauto. *)
(*   + rewrite <- lookupAL_updateAddAL_neq; eauto. *)
(*   + i. rename_id_res id_res. *)
(*     destruct (id_dec id_res reg). *)
(*     * admit. (* bop: operand not unique => result not unique *) *)
(*       (* TODO: result of inst not containing unique *) *)
(*       (* can believe it even without proofs *) *)
(*     * exploit LOCALS; eauto. *)
(*       rewrite <- lookupAL_updateAddAL_neq in *; eauto. *)
(* - (* fbop *) *)
(*   ii. rewrite AtomSetFacts.union_b in NO_LEAK. ss. *)
(*   solve_des_bool. *)
(*   apply AtomSetImpl_singleton_mem_false in NO_LEAK. *)
(*   apply AtomSetFacts.mem_iff in MEM. *)
(*   specialize (STATE _ MEM). *)
(*   inv STATE. *)

(*   econs; ss; eauto. *)
(*   + rewrite <- lookupAL_updateAddAL_neq; eauto. *)
(*   + i. rename_id_res id_res. *)
(*     destruct (id_dec id_res reg). *)
(*     * admit. (* fbop: operand not unique => result not unique *) *)
(*       (* TODO: result of inst not containing unique *) *)
(*       (* can believe it even without proofs *) *)
(*     * exploit LOCALS; eauto. *)
(*       rewrite <- lookupAL_updateAddAL_neq in *; eauto. *)
(* - (* extractvalue *) *)
(*   ii. rewrite AtomSetFacts.union_b in NO_LEAK. ss. *)
(*   solve_des_bool. *)
(*   apply AtomSetImpl_singleton_mem_false in NO_LEAK. *)
(*   apply AtomSetFacts.mem_iff in MEM. *)
(*   specialize (STATE _ MEM). *)
(*   inv STATE. *)

(*   econs; ss; eauto. *)
(*   + rewrite <- lookupAL_updateAddAL_neq; eauto. *)
(*   + i. rename_id_res id_res. *)
(*     destruct (id_dec id_res reg). *)
(*     * admit. (* bop: operand not unique => result not unique *) *)
(*       (* TODO: result of inst not containing unique *) *)
(*       (* can believe it even without proofs *) *)
(*     * exploit LOCALS; eauto. *)
(*       rewrite <- lookupAL_updateAddAL_neq in *; eauto. *)
(* - (* insertvalue *) *)
(*   (* TODO: fill rest *) *)


Lemma step_state_equiv_except
      conf st0 st1 evt
      cmd cmds
      (NONCALL: Instruction.isCallInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP: sInsn conf st0 st1 evt)
  : state_equiv_except (AtomSetImpl_from_list (Cmd.get_def cmd))
                       (mkState st0.(EC) st0.(ECS) st1.(Mem)) st1.
Proof.
  inv STEP; ss;
    inv CMDS; econs; ss; ii;
      hexploit AtomSetImpl_singleton_mem_false; eauto; i;
        eauto using lookupAL_updateAddAL_neq.
Qed.

Lemma forget_stack_unary_sound
      conf defs leaks st0 st1 gmax public
      inv invst invmem
      (EQUIV : state_equiv_except defs st0 st1)
      (UNIQUE_PRESERVED : unique_preserved_except conf inv invmem.(InvMem.Unary.unique_parent) st1 gmax (AtomSetImpl.union defs leaks))
      (STATE : InvState.Unary.sem conf st0 invst invmem gmax public inv)
      (WF_LC: memory_props.MemProps.wf_lc st1.(Mem) st1.(EC).(Locals))
      (EQ_FUNC: st0.(EC).(CurFunction) = st1.(EC).(CurFunction))
  : InvState.Unary.sem conf st1 invst invmem gmax public (ForgetStack.unary defs leaks inv).
Proof.
  inv STATE.
  assert (EQUIV_REV: state_equiv_except defs st1 st0).
  { symmetry. eauto. }
  econs; eauto.
  - ii. destruct x as [e1 e2]. ss.
    apply ExprPairSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    solve_negb_liftpred.
    exploit sem_expr_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto.
    i. des.
    exploit LESSDEF; eauto.
    i. des. ss.
    exploit sem_expr_equiv_except; try exact EQUIV; try exact VAL2; eauto.
  - inv NOALIAS.
    econs.
    + i. ss.
      rewrite ValueTPairSetFacts.filter_b in MEM; try by solve_compat_bool. des_ifs.
      unfold sflib.is_true in MEM.
      solve_negb_liftpred.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL2; eauto.
    + i. ss.
      rewrite PtrPairSetFacts.filter_b in MEM; try by solve_compat_bool. des_ifs.
      unfold sflib.is_true in MEM.
      solve_negb_liftpred.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL2; eauto.
  - ii. ss.
    apply AtomSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    apply negb_true_iff in H0.
    inv UNIQUE_PRESERVED.
    apply UNIQUE_PRESERVED_INV; eauto.
    apply AtomSetFacts.mem_iff; eauto.
  - ii. ss.
    apply IdTSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    unfold flip, compose in *.
    apply negb_true_iff in H0.
    destruct x as [t x].

    inv EQUIV. rewrite <- MEM.
    destruct t; try (exploit PRIVATE; eauto; fail).
    exploit sem_idT_equiv_except; eauto.
    { rewrite <- lift_physical_atoms_idtset_spec1. eauto. }
    i. des.
    exploit PRIVATE; eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
  - inv UNIQUE_PRESERVED. eauto.
  - rewrite <- EQ_FUNC.
    ii.
    exploit WF_INSNS; eauto.
Qed.

Lemma forget_stack_sound
      conf_src st0_src
      conf_tgt st0_tgt
      st1_src st1_tgt
      invst invmem inv0
      defs_src defs_tgt
      leaks_src leaks_tgt
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst invmem inv0)
      (EQUIV_SRC: state_equiv_except defs_src st0_src st1_src)
      (EQUIV_TGT: state_equiv_except defs_tgt st0_tgt st1_tgt)
      (UNIQUE_SRC: unique_preserved_except
                     conf_src inv0.(Invariant.src)
                     invmem.(InvMem.Rel.src).(InvMem.Unary.unique_parent)
                     st1_src invmem.(InvMem.Rel.gmax)
                     (AtomSetImpl.union defs_src leaks_src))
      (UNIQUE_TGT: unique_preserved_except
                     conf_tgt inv0.(Invariant.tgt)
                     invmem.(InvMem.Rel.tgt).(InvMem.Unary.unique_parent)
                     st1_tgt invmem.(InvMem.Rel.gmax)
                     (AtomSetImpl.union defs_tgt leaks_tgt))
      (WF_LC_SRC: memory_props.MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_LC_TGT: memory_props.MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))
      (EQ_FUNC_SRC: st0_src.(EC).(CurFunction) = st1_src.(EC).(CurFunction))
      (EQ_FUNC_TGT: st0_tgt.(EC).(CurFunction) = st1_tgt.(EC).(CurFunction))
  : <<STATE_FORGET: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt
                                     invst invmem (ForgetStack.t defs_src defs_tgt leaks_src leaks_tgt inv0)>>.
Proof.
  inv STATE.
  econs; ss.
  - eapply forget_stack_unary_sound; eauto.
  - eapply forget_stack_unary_sound; eauto.
  - i. ss.
    rewrite IdTSetFacts.union_b in NOTIN.
    solve_des_bool.
    destruct id0. destruct t; ss.
    + rewrite lift_physical_atoms_idtset_spec1 in *.
      rewrite AtomSetFacts.union_b in NOTIN.
      solve_des_bool.
      ii. symmetry in EQUIV_SRC.
      exploit sem_idT_equiv_except; try exact EQUIV_SRC; eauto. i. des.
      exploit MAYDIFF; eauto. i. des.
      exploit sem_idT_equiv_except; try exact EQUIV_TGT; eauto.
    + ii. exploit MAYDIFF; eauto.
    + ii. exploit MAYDIFF; eauto.
Qed.
