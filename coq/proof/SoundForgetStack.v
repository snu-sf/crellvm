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
Require AssnMem.
Require AssnState.
Require Import SoundBase.

Require Import Inject. (* TODO: for simtac *)
Require Import TODOProof.
Require Import MemAux.
Require Import memory_props.
Import MemProps.

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
      (STATE: AssnState.Unary.sem_idT st0 invst (Tag.physical, id) = Some gv)
      (NOTIN: AtomSetImpl.mem id ids = false)
  : <<STATE: AssnState.Unary.sem_idT st1 invst (Tag.physical, id) = Some gv>>.
Proof.
  unfold AssnState.Unary.sem_idT in *.
  inv EQUIV.
  unfold locals_equiv_except in LOCALS.
  red. rewrite <- STATE.
  symmetry. eapply LOCALS; eauto.
Qed.

Lemma sem_valueT_equiv_except
      ids st0 st1 invst v gv
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: AssnState.Unary.sem_valueT conf st0 invst v = Some gv)
      (NOTIN: (LiftPred.ValueT (flip IdTSet.mem (lift_physical_atoms_idtset ids))) v = false)
  : <<STATE: AssnState.Unary.sem_valueT conf st1 invst v = Some gv>>.
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
      (STATE: AssnState.Unary.sem_list_valueT conf st0 invst lsv = Some gvs)
      (NOTIN: existsb (LiftPred.ValueT (flip IdTSet.mem (lift_physical_atoms_idtset ids)) <*> snd) lsv = false)
  : <<STATE: AssnState.Unary.sem_list_valueT conf st1 invst lsv = Some gvs>>.
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
         | [H: AssnState.Unary.sem_valueT _ st0 _ _ = Some _ |- _] =>
           eapply sem_valueT_equiv_except in H; eauto; rewrite H
         end.

Lemma sem_expr_equiv_except
      conf invst
      ids st0 st1 e val
      (EQUIV: state_equiv_except ids st0 st1)
      (FILTER: (LiftPred.Expr (flip IdTSet.mem (lift_physical_atoms_idtset ids))) e = false)
      (SEM_EXPR: AssnState.Unary.sem_expr conf st0 invst e = Some val)
  : <<SEM_EXPR: AssnState.Unary.sem_expr conf st1 invst e = Some val>>.
Proof.
  unfold compose in FILTER.
  destruct e; ss; simtac;
    try (solve_equiv_except_val st0; eauto).
  - erewrite sem_list_valueT_equiv_except; eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
Qed.

Lemma forget_stack_unary_Subset
      defs leaks inv0
  : Assertion.Subset_unary (ForgetStack.unary defs leaks inv0) inv0.
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
  : Assertion.Subset (ForgetStack.t def_src def_tgt leaks_src leaks_tgt inv0) inv0.
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
       forall u (MEM: AtomSetImpl.mem u inv.(Assertion.unique) = true)
         (NO_LEAK: AtomSetImpl.mem u except_for = false),
         AssnState.Unary.sem_unique conf st gmax u)
    (UNIQUE_PRESERVED_PARENT_LOCAL:
       forall x ptr
         (PTR:lookupAL _ st.(EC).(Locals) x = Some ptr),
         AssnMem.gv_diffblock_with_blocks conf ptr unique_parent)
    (UNIQUE_PRESERVED_PARENT_MEM:
       forall mptr typ align val'
         (LOAD: mload conf.(CurTargetData) st.(Mem) mptr typ align = Some val'),
         AssnMem.gv_diffblock_with_blocks conf val' unique_parent)
    (UNIQUE_PRESERVED_PARENT_GLOBALS:
       forall b (IN: In b unique_parent), (gmax < b)%positive)
.

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

(* TODO move diffblock theories to SoundBase? or some root file so that others can see? *)
Lemma getOperandValue_diffblock
      conf gmax (* public Mem0 assnmem *)
      blocks
      lc
      valy gvaly
      (GET_OPERAND: getOperandValue conf.(CurTargetData) valy lc conf.(Globals) = Some gvaly)
      (* (MEM: AssnMem.Unary.sem conf gmax public Mem0 assnmem) *)
      (* in MEM, WF_GLOBALS and GLOBALS exist, but blocks will be bound to unique_parent *)
      (WF_GLOBALS: genericvalues_inject.wf_globals gmax (Globals conf))
      (GLOBALS: forall b : Values.block, In b blocks -> (gmax < b)%positive)
      (LOOKUP_DIFFBLOCK:
         forall valx gvalx (LOOKUP: lookupAL GenericValue lc valx = Some gvalx),
           AssnMem.gv_diffblock_with_blocks conf gvalx blocks)
  :
    AssnMem.gv_diffblock_with_blocks conf gvaly blocks
.
Proof.
  destruct valy; ss.
  - hexploit LOOKUP_DIFFBLOCK; eauto.
  - eapply MemAux.wf_globals_const2GV in GET_OPERAND; eauto.
    des.
    eapply valid_ptr_globals_diffblock_with_blocks; eauto.
Unshelve.
ss.
Qed.

Lemma no_alias_diffblock
      conf gval1 gval2
      (NOALIAS: no_alias gval1 gval2)
  :
    <<DIFFBLOCK: AssnState.Unary.sem_diffblock conf gval1 gval2>>
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
      (DIFFBLOCK: forall blocks, AssnMem.gv_diffblock_with_blocks conf valx blocks)
  :
    <<DIFFBLOCK: forall gvs, AssnState.Unary.sem_diffblock conf valx gvs>>
.
Proof.
  ii. eapply DIFFBLOCK; eauto.
Qed.

Lemma no_embedded_ptrs_diffblock_with_blocks
      val blocks
      (NO_PTR: no_embedded_ptrs val)
  :
    (* moving conf above : (to premise) will make Unshelved goals in BOP_diffblock_with_blocks *)
  <<DIFFBLOCK: forall conf, AssnMem.gv_diffblock_with_blocks conf val blocks>>
.
Proof.
  induction val; ii; ss.
  des_ifs; ss; exploit IHval; eauto.
Qed.

Lemma undef_implies_diffblock_with_blocks
      TD ty1 valx conf
      (UNDEF: gundef TD ty1 = Some valx)
  :
    <<DIFFBLOCK: forall blocks, AssnMem.gv_diffblock_with_blocks conf valx blocks>>
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
    AssnState.Unary.sem_diffblock conf valx valy
.
Proof.
  ii. exploit undef_implies_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma app_diffblock_with_blocks
      conf gvs gvs' blocks
  (DIFFBLOCK1: AssnMem.gv_diffblock_with_blocks conf gvs blocks)
  (DIFFBLOCK2: AssnMem.gv_diffblock_with_blocks conf gvs' blocks)
  :
  <<DIFFBLOCK: AssnMem.gv_diffblock_with_blocks conf (gvs ++ gvs') blocks>>
.
Proof.
  ii.
  apply GV2blocks_app_inv in ING. des.
  - eapply DIFFBLOCK1; eauto.
  - eapply DIFFBLOCK2; eauto.
Qed.

Lemma incl_diffblock_with_blocks
      gvsx gvsy conf blocks
  (INCL: incl gvsx gvsy)
  (DIFFBLOCK: AssnMem.gv_diffblock_with_blocks conf gvsy blocks)
  :
    <<DIFFBLOCK: AssnMem.gv_diffblock_with_blocks conf gvsx blocks>>
.
Proof.
  red.
  generalize dependent gvsy.
  induction gvsx; i; ss.
  assert(INCL2: incl gvsx gvsy).
  { ii. eapply INCL. ss. right. ss. }
  ii.
  destruct a; ss.
  unfold GV2blocks in *. unfold compose in *.
  destruct v; cbn in *; try (eapply IHgvsx; eauto; fail).
  rename b into __b__.
  des.
  - clarify. eapply IHgvsx; eauto.
    exploit DIFFBLOCK; eauto.
    { eapply GV2blocks_incl in INCL. eapply INCL. ss. left. ss. }
    i; ss.
  - eapply IHgvsx; eauto.
Qed.

Lemma BOP_diffblock_with_blocks
      S TD Ps gl fs
      lc bop sz v1 v2 val
      (H : BOP TD lc gl bop sz v1 v2 = Some val)
  : <<DIFFBLOCK: forall blocks, AssnMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
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
  : AssnState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit BOP_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma FBOP_diffblock_with_blocks
      S TD Ps gl fs
      lc fbop sz v1 v2 val
      (H : FBOP TD lc gl fbop sz v1 v2 = Some val)
  : <<DIFFBLOCK: forall blocks, AssnMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
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
  : AssnState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit FBOP_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma TRUNC_diffblock_with_blocks
      S TD Ps gl fs lc val
      truncop1 typ1 value1 typ2
      (H: TRUNC TD lc gl truncop1 typ1 value1 typ2 = Some val)
  : <<DIFFBLOCK: forall blocks, AssnMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
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
  : AssnState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit TRUNC_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma EXT_diffblock_with_blocks
      S TD Ps gl fs lc val
      extop1 typ1 value1 typ2
      (H: EXT TD lc gl extop1 typ1 value1 typ2 = Some val)
  : <<DIFFBLOCK: forall blocks, AssnMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
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
  : AssnState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
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
  unfold micmp in *. des_ifs; try (by eapply undef__no_embedded_ptrs; eauto).
  - eapply micmp_int_preserves_no_embedded_ptrs; eauto.
Qed.

Lemma ICMP_diffblock_with_blocks
      S TD Ps gl fs lc val
      cond1 typ1 value1 value2
      (H: ICMP TD lc gl cond1 typ1 value1 value2 = Some val)
  : <<DIFFBLOCK: forall blocks, AssnMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
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
  : AssnState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
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
  : <<DIFFBLOCK: forall blocks, AssnMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val blocks>>.
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
  : AssnState.Unary.sem_diffblock (mkCfg S TD Ps gl fs) ptr val.
Proof.
  ii. exploit FCMP_diffblock_with_blocks; eauto; i; des.
Qed.

Lemma GEP_diffblock
  assnmem inbounds5 typ5 value_5 l0 typ' gmax u S TD Ps F lc gl fs vidxs mp Mem0 reg val'
  (B: block)
  (NEXTBLOCK : Memory.Mem.nextblock Mem0 = AssnMem.Unary.nextblock assnmem)
  (GLOBALS : genericvalues_inject.wf_globals gmax gl)
  (WF : wf_Mem gmax TD Mem0)
  (H : getOperandValue TD value_5 lc gl = Some mp)
  (val : GenericValue)
  (VAL : lookupAL GenericValue lc u = Some val)
  (LOCALS : forall (reg : atom) (val' : GenericValue),
           u <> reg ->
           lookupAL GenericValue lc reg = Some val' ->
           AssnState.Unary.sem_diffblock
             {|
             CurSystem := S;
             CurTargetData := TD;
             CurProducts := Ps;
             Globals := gl;
             FunTable := fs |} val val')
  (MEM : forall (mptr : mptr) (typ : typ) (align : align) (val' : GenericValue),
        mload TD Mem0 mptr typ align = Some val' ->
        AssnState.Unary.sem_diffblock
          {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |} val val')
  (GLOBALS0 : forall b : Values.block, In b (GV2blocks val) -> (gmax < b)%positive)
  (REG : u <> reg)
  (NOT_LEAKED_U : AtomSetImpl.mem u
                   (AtomSetImpl_from_list
                      (Cmd.get_leaked_ids (insn_gep reg inbounds5 typ5 value_5 l0 typ'))) =
                 false)
  (H1 : GEP TD typ5 mp vidxs inbounds5 typ' = Some val')
  (WF_INSN: wf_insn S (module_intro (fst TD) (snd TD) Ps) F B
                    (insn_cmd (insn_gep reg inbounds5 typ5 value_5 l0 typ')))
  :
  <<DIFFBLOCK: AssnState.Unary.sem_diffblock
    {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}
    val val'>>
.
Proof.
  (* i; des. *)
  unfold GEP in *. unfold gep in *. unfold genericvalues.LLVMgv.GEP in *.
  assert(TTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTTT: True) by ss.
  move val at bottom.
  eapply AssnState.Unary.diffblock_comm.
  destruct (GV2ptr TD (getPointerSize TD) mp) eqn:T1; cycle 1.
  { eapply undef_implies_diffblock; eauto. }
  destruct (GVs2Nats TD vidxs) eqn:T2; cycle 1.
  { eapply undef_implies_diffblock; eauto. }
  destruct (mgep TD typ5 v l1) eqn:T3; cycle 1.
  { eapply undef_implies_diffblock; eauto. }
  clarify. ss.
  {
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
        unfold AssnState.Unary.sem_diffblock in *.
        unfold list_disjoint in *.
        eapply H0; eauto. ss. left; ss.
      -
        (* const5 -> mp -> Vptr b <= gmax *)
        rename val into __val__.
        rename u into __u__.
        rename b into __b__.
        destruct TD; ss.
        apply TODOProof.wf_globals_eq in GLOBALS.
        exploit MemAux.wf_globals_const2GV; eauto.
        { eapply wf_globals_eq; eauto. }
        intro VALID_PTR; des. clear WF_INSN.
        ss.
        idtac.
        exploit valid_ptr_globals_diffblock; eauto.
        {
          eapply {| CurSystem := S; CurTargetData := (l2, l3);
                    CurProducts := Ps; Globals := gl; FunTable := fs |}.
        }
        destruct mp; ss. destruct p; ss. destruct v; ss. des. des_ifs.
        left; ss.
    }
  }
Qed.

(* care for quantification position of the "blocks".
If it is inside getOperand_diffblock && DIFFBLOCK, this lemma is not usable in intended use case. *)
Lemma CAST_diffblock_with_blocks
      S Ps fs val1
      TD lc gl castop0 t1 v1 t2
      (H: CAST TD lc gl castop0 t1 v1 t2 = Some val1)
      blocks
      (getOperand_diffblock: forall v2 val2,
          getOperandValue TD v2 lc gl = Some val2 ->
          AssnMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val2 blocks)
  : <<DIFFBLOCK: AssnMem.gv_diffblock_with_blocks (mkCfg S TD Ps gl fs) val1 blocks>>.
Proof.
  red; i.
  apply opsem_props.OpsemProps.CAST_inversion in H. des.
  unfold mcast in *.
  des_ifs; try (eapply undef_implies_diffblock_with_blocks; eauto; fail);
    try (apply mbitcast_inv in H0; clarify; []; hexploit getOperand_diffblock; eauto).
Qed.

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
      invst assnmem inv0
      cmd cmds
      gmax public
      (STATE: AssnState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst assnmem gmax public inv0)
      (WF_LC_BEFORE: wf_lc st0.(Mem) st0.(EC).(Locals))
      (MEM: AssnMem.Unary.sem conf gmax public st1.(Mem) assnmem)
      (NONCALL: Instruction.isCallInst cmd = false)
      (NONMALLOC: isMallocInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : << UNIQUE_CURRENT:
    forall u : atom,
      AtomSetImpl.mem u (Assertion.unique inv0) = true ->
      AtomSetImpl.mem u
                      (union (AtomSetImpl_from_list (Cmd.get_def cmd))
                             (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd))) = false ->
      AssnState.Unary.sem_unique conf st1 gmax u>>.
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
    clarify.
    {
      clear - H1 H4 H2 H0.
      exploit In_incl; eauto.
      { eapply GV2blocks_incl; eauto. }
      i.
      exploit H4; eauto.
    }
  -
    inversion UNIQUE_BEF; subst; narrow_down_unique.
    ii.
    rename val into __val__.
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
    clarify.
    {
      clear - H1 H5 H6 H2 H3.
      exploit In_incl; eauto.
      { eapply GV2blocks_incl; eauto. }
      intro IN.
      eapply GV2blocks_app_inv in IN.
      des.
      -
        apply GV2blocks_in_inv in IN.
        des.
        expl GV2blocks_lift.
        expl H5.
      -
        apply GV2blocks_in_inv in IN.
        des.
        expl GV2blocks_lift.
        expl H6.
    }
  - (* alloca *)
    inv UNIQUE_BEF; narrow_down_unique.
    ii.
    exploit locals_alloca_diffblock; eauto.
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
    destruct TD; ss. destruct B; ss. destruct s; ss.
    eapply GEP_diffblock; eauto.
    { inv WF_EC. ss.
      eapply typings_props.wf_fdef__wf_cmd; try eassumption.
      - eapply sublist_In; eauto. ss. left. ss.
    }
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply TRUNC_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    eapply EXT_diffblock; eauto.
  - inv UNIQUE_BEF; narrow_down_unique.
    (* specialize (LOCALS reg val' REG). *)
    unfold CAST in *. des_ifs. apply mcast_inv in H.
    des; cycle 1.
    +
      apply AssnState.Unary.diffblock_comm.
      eapply undef_implies_diffblock; eauto.
    +
      subst.
      unfold getOperandValue in *.
      des_ifs; cycle 1.
      * ss.
        rename g into __g__.
        rename val into __val__.
        exploit MemAux.wf_globals_const2GV; eauto; []; i; des.
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
    unfold SELECT in *. des_ifs.
    unfold mselect in *.
    move g0 at bottom.
    move g1 at bottom.
    unfold getOperandValue in *.
    destruct (GV2int (l0, n) Size.One g) eqn:T; ss; cycle 1.
    { eapply AssnState.Unary.diffblock_comm; eauto.
      eapply undef_implies_diffblock; eauto. }
    abstr (zeq z 0) decision.
    destruct decision; ss. 
    { clear Heq0.
      unfold fit_chunk_gv in *.
      des_ifsH H; cycle 1.
      { eapply AssnState.Unary.diffblock_comm; eauto.
        eapply undef_implies_diffblock; eauto. }
      destruct value2; ss.
      {
        apply_all_once AtomSetFacts.not_mem_iff.
        apply_all_once AtomSetImpl_from_list_spec2.
        unfold Cmd.get_leaked_ids in *. ss.
        eapply LOCALS; try apply Heq1; eauto.
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
        exploit MemAux.wf_globals_const2GV; eauto; []; intro VALID_PTR; des.
        eapply valid_ptr_globals_diffblock; eauto.
      }
    }
    { clear Heq1.
      unfold fit_chunk_gv in *.
      des_ifsH H; cycle 1.
      { eapply AssnState.Unary.diffblock_comm; eauto.
        eapply undef_implies_diffblock; eauto. }
      destruct value1; ss.
      {
        apply_all_once AtomSetFacts.not_mem_iff.
        apply_all_once AtomSetImpl_from_list_spec2.
        unfold Cmd.get_leaked_ids in *. ss.
        eapply LOCALS; try apply Heq0; eauto.
        {
          ii. apply NOT_LEAKED_U. subst.
          destruct value0; ss.
          - right. left. ss.
          - left. ss.
        }
      }
      {
        exploit MemAux.wf_globals_const2GV; eauto; []; intro VALID_PTR; des.
        eapply valid_ptr_globals_diffblock; eauto.
      }
    }
Unshelve.
all: ss.
Qed.

Lemma step_unique_preserved_except_parent
      conf st0 st1 evt
      invst assnmem inv0
      cmd cmds
      gmax public
      (STATE: AssnState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst assnmem gmax public inv0)
      (MEM: AssnMem.Unary.sem conf gmax public st1.(Mem) assnmem)
      (PRIVATE_PARENT_BEFORE:
         forall b (IN: In b assnmem.(AssnMem.Unary.private_parent)),
           (b < Memory.Mem.nextblock st0.(Mem))%positive)
      (NONCALL: Instruction.isCallInst cmd = false)
      (NONMALLOC: isMallocInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : <<UNIQUE_PARENT:
    forall (x : atom) (ptr : GenericValue),
      lookupAL GenericValue (Locals (EC st1)) x = Some ptr ->
      AssnMem.gv_diffblock_with_blocks conf ptr (AssnMem.Unary.unique_parent assnmem)>>.
Proof.
  red; i.
  inv STATE. clear LESSDEF NOALIAS UNIQUE PRIVATE WF_LOCAL WF_PREVIOUS WF_GHOST WF_FDEF WF_EC.
  inv STEP; ss; clarify.
  - (* nop *) eapply UNIQUE_PARENT_LOCAL; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply BOP_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply FBOP_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    rename H1 into EXTRACT.
    apply extractValue_sub in EXTRACT.
    des; cycle 1.
    { eapply undef_implies_diffblock_with_blocks; eauto. }
    remember {| CurSystem := S;
                CurTargetData := TD;
                CurProducts := Ps;
                Globals := gl;
                FunTable := fs |} as conf.
    replace TD with conf.(CurTargetData) in H0; [|subst; ss].
    replace gl with conf.(Globals) in H0; [|subst; ss].
    hexploit getOperandValue_diffblock; ss; try exact H0; eauto; [apply MEM|apply MEM|]; intro DIFFBLOCK1.
    eapply incl_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    rename H2 into INSERT.
    apply insertValue_sub in INSERT.
    des; cycle 1.
    { eapply undef_implies_diffblock_with_blocks; eauto. }
    remember {| CurSystem := S;
                CurTargetData := TD;
                CurProducts := Ps;
                Globals := gl;
                FunTable := fs |} as conf.
    replace TD with conf.(CurTargetData) in H0, H1; [|subst; ss].
    (* replace TD with conf.(CurTargetData) in *; [|subst; ss]. *)
    (* Heconf becomes recursive!! ?? *)
    replace gl with conf.(Globals) in H0, H1; [|subst; ss].
    hexploit getOperandValue_diffblock; ss; try exact H0; eauto; try apply MEM; intro DIFFBLOCK1.
    hexploit getOperandValue_diffblock; ss; try exact H1; eauto; try apply MEM; intro DIFFBLOCK2.
    eapply incl_diffblock_with_blocks; eauto.
    eapply app_diffblock_with_blocks; eauto.
  - (* free *) eapply UNIQUE_PARENT_LOCAL; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    ii.
    clear H0 H1 NONCALL UNIQUE_PARENT_LOCAL.
    cbn in *. des; ss. clarify.
    exploit PRIVATE_PARENT_BEFORE; eauto.
    { eapply sublist_In; eauto. apply MEM. }
    intro VALID_PTR.
    clear - H2 VALID_PTR.
    eapply alloca_result in H2. subst.
    apply Pos.lt_irrefl in VALID_PTR. ss.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply MEM; eauto.
  - (* store *) eapply UNIQUE_PARENT_LOCAL; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    remember {| CurSystem := S;
                CurTargetData := TD;
                CurProducts := Ps;
                Globals := gl;
                FunTable := fs |} as conf.
    replace TD with conf.(CurTargetData) in H0, H1; [|subst; ss].
    replace gl with conf.(Globals) in H0, H1; [|subst; ss].
    hexploit getOperandValue_diffblock; try exact H0; eauto; try apply MEM.
    i; des.
    apply dopsem.GEP_inv in H2.
    des.
    { eapply undef_implies_diffblock_with_blocks; eauto. }
    clarify.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply TRUNC_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply EXT_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    idtac.
    eapply CAST_diffblock_with_blocks; eauto.
    i.
    eapply getOperandValue_diffblock; eauto; try apply MEM.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply ICMP_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    eapply FCMP_diffblock_with_blocks; eauto.
  - des_lookupAL_updateAddAL; [|eapply UNIQUE_PARENT_LOCAL; eauto].
    clear NONCALL.
    remember {| CurSystem := S;
                CurTargetData := TD;
                CurProducts := Ps;
                Globals := gl;
                FunTable := fs |} as conf.
    { unfold SELECT in *. des_ifs.
      unfold mselect, fit_chunk_gv in *.
      des_ifs; try (by eapply undef_implies_diffblock_with_blocks; eauto).
      - hexploit getOperandValue_diffblock; try apply MEM; ss; try exact Heq0; eauto.
      - hexploit getOperandValue_diffblock; try apply MEM; ss; try exact Heq1; eauto.
    }
Unshelve.
ss.
Qed.

Lemma step_unique_preserved_except
      conf st0 st1 evt
      invst assnmem inv0
      cmd cmds
      gmax public
      (STATE: AssnState.Unary.sem conf (mkState st0.(EC) st0.(ECS) st1.(Mem)) invst assnmem gmax public inv0)
      (WF_LC_BEFORE: wf_lc st0.(Mem) st0.(EC).(Locals))
      (PRIVATE_PARENT_BEFORE:
         forall b (IN: In b assnmem.(AssnMem.Unary.private_parent)),
           (b < Memory.Mem.nextblock st0.(Mem))%positive)
      (MEM: AssnMem.Unary.sem conf gmax public st1.(Mem) assnmem)
      (NONCALL: Instruction.isCallInst cmd = false)
      (NONMALLOC: isMallocInst cmd = false)
      (CMDS : CurCmds st0.(EC) = cmd :: cmds)
      (STEP : sInsn conf st0 st1 evt)
  : unique_preserved_except conf inv0 assnmem.(AssnMem.Unary.unique_parent) st1 gmax
                            (AtomSetImpl.union (AtomSetImpl_from_list (Cmd.get_def cmd))
                                               (AtomSetImpl_from_list (Cmd.get_leaked_ids cmd))).
Proof.
  hexploit step_unique_preserved_except_current; eauto. i.
  hexploit step_unique_preserved_except_parent; eauto. i.
  inv STATE. inv MEM.
  econs; eauto.
Qed.




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
      inv invst assnmem
      (EQUIV : state_equiv_except defs st0 st1)
      (UNIQUE_PRESERVED : unique_preserved_except conf inv assnmem.(AssnMem.Unary.unique_parent) st1 gmax (AtomSetImpl.union defs leaks))
      (STATE : AssnState.Unary.sem conf st0 invst assnmem gmax public inv)
      (WF_LC: memory_props.MemProps.wf_lc st1.(Mem) st1.(EC).(Locals))
      (EQ_FUNC: st0.(EC).(CurFunction) = st1.(EC).(CurFunction))
      (ALLOCAS_PARENT: list_disjoint (Allocas (EC st1)) (AssnMem.Unary.private_parent assnmem))
      (ALLOCAS_VALID: Forall (Memory.Mem.valid_block (Mem st1)) st1.(EC).(Allocas))
      (WF_EC: OpsemAux.wf_EC st1.(EC))
  : AssnState.Unary.sem conf st1 invst assnmem gmax public (ForgetStack.unary defs leaks inv).
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
    red in PRIVATE.
    red in PRIVATE.
    exploit PRIVATE; eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
  - inv UNIQUE_PRESERVED. eauto.
  - rewrite <- EQ_FUNC. ss.
Qed.

Lemma forget_stack_sound
      conf_src st0_src
      conf_tgt st0_tgt
      st1_src st1_tgt
      invst assnmem inv0
      defs_src defs_tgt
      leaks_src leaks_tgt
      (STATE: AssnState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst assnmem inv0)
      (EQUIV_SRC: state_equiv_except defs_src st0_src st1_src)
      (EQUIV_TGT: state_equiv_except defs_tgt st0_tgt st1_tgt)
      (UNIQUE_SRC: unique_preserved_except
                     conf_src inv0.(Assertion.src)
                     assnmem.(AssnMem.Rel.src).(AssnMem.Unary.unique_parent)
                     st1_src assnmem.(AssnMem.Rel.gmax)
                     (AtomSetImpl.union defs_src leaks_src))
      (UNIQUE_TGT: unique_preserved_except
                     conf_tgt inv0.(Assertion.tgt)
                     assnmem.(AssnMem.Rel.tgt).(AssnMem.Unary.unique_parent)
                     st1_tgt assnmem.(AssnMem.Rel.gmax)
                     (AtomSetImpl.union defs_tgt leaks_tgt))
      (WF_LC_SRC: memory_props.MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_LC_TGT: memory_props.MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))
      (EQ_FUNC_SRC: st0_src.(EC).(CurFunction) = st1_src.(EC).(CurFunction))
      (EQ_FUNC_TGT: st0_tgt.(EC).(CurFunction) = st1_tgt.(EC).(CurFunction))
      (ALLOCAS_PARENT_SRC: list_disjoint (Allocas (EC st1_src))
                                         (AssnMem.Unary.private_parent (AssnMem.Rel.src assnmem)))
      (ALLOCAS_PARENT_TGT: list_disjoint (Allocas (EC st1_tgt))
                                         (AssnMem.Unary.private_parent (AssnMem.Rel.tgt assnmem)))
      (ALLOCAS_VALID_SRC: Forall (Memory.Mem.valid_block (Mem st1_src)) st1_src.(EC).(Allocas))
      (ALLOCAS_VALID_TGT: Forall (Memory.Mem.valid_block (Mem st1_tgt)) st1_tgt.(EC).(Allocas))
      (INJECT_ALLOCAS: AssnState.Rel.inject_allocas (AssnMem.Rel.inject assnmem)
                                   st1_src.(EC).(Allocas) st1_tgt.(EC).(Allocas))
      (WF_EC_SRC: OpsemAux.wf_EC st1_src.(EC))
      (WF_EC_TGT: OpsemAux.wf_EC st1_tgt.(EC))
  : <<STATE_FORGET: AssnState.Rel.sem conf_src conf_tgt st1_src st1_tgt
                                     invst assnmem (ForgetStack.t defs_src defs_tgt leaks_src leaks_tgt inv0)>>.
Proof.
  inv STATE.
  econs; ss.
  - eapply forget_stack_unary_sound; eauto.
  - eapply forget_stack_unary_sound; eauto.
  - eapply AtomSetFacts.Empty_s_m_Proper; eauto. red.
    ii.
    apply AtomSetFacts.filter_iff in H; [|solve_compat_bool]. des. ss.
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
