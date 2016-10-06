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


Definition noalias_with_def_memory (conf:Config) (def_memory:option (GenericValue * typ)) (ptr:GenericValue) (ty:typ): Prop :=
  forall gptr_def ty_def
         (DEF: def_memory = Some (gptr_def, ty_def)),
    InvState.Unary.sem_noalias conf gptr_def ptr ty_def ty.

Inductive mem_change : Type :=
| mem_change_alloc
    (gsz:sz) (gn:GenericValue) (a:align)
| mem_change_store
    (ptr:GenericValue) (ty:typ) (gv:GenericValue) (a:align)
| mem_change_free
    (ptr:GenericValue)
| mem_change_none
.

(* Definition ptr_to_genericvalue conf st invst ptr: option (GenericValue * typ) := *)
(*   match InvState.Unary.sem_valueT conf st invst ptr.(fst) with *)
(*   | Some gv => Some (gv, ptr.(snd)) *)
(*   | None => None *)
(*   end. *)

Inductive mem_change_inject conf_src conf_tgt invmem: mem_change -> mem_change -> Prop :=
| mem_change_inject_alloc_alloc
    gsz gn0 gn1 a
    (N_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gn0 gn1)
  : mem_change_inject conf_src conf_tgt invmem (mem_change_alloc gsz gn0 a) (mem_change_alloc gsz gn1 a)
| mem_change_inject_alloc_none
    gsz gn a
  : mem_change_inject conf_src conf_tgt invmem (mem_change_alloc gsz gn a) mem_change_none
| mem_change_inject_none_alloc
    gsz gn a
  : mem_change_inject conf_src conf_tgt invmem mem_change_none (mem_change_alloc gsz gn a)
| mem_change_inject_store_store
    ptr0 ptr1 gv0 gv1 ty a
    (PTR_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) ptr0 ptr1)
    (VAL_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gv0 gv1)
  : mem_change_inject conf_src conf_tgt invmem (mem_change_store ptr0 ty gv0 a) (mem_change_store ptr1 ty gv1 a)
| mem_change_inject_store_nop
    ptr gv ty a b ofs
    (GV2PTR: GV2ptr conf_src.(CurTargetData) (getPointerSize conf_tgt.(CurTargetData)) ptr = Some (Values.Vptr b ofs))
    (IN: In b invmem.(InvMem.Rel.src).(InvMem.Unary.private))
  : mem_change_inject conf_src conf_tgt invmem (mem_change_store ptr ty gv a) mem_change_none
| mem_change_inject_free
    ptr0 ptr1
    (PTR_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) ptr0 ptr1)
    : mem_change_inject conf_src conf_tgt invmem (mem_change_free ptr0) (mem_change_free ptr1)
| mem_change_inject_none
    : mem_change_inject conf_src conf_tgt invmem mem_change_none mem_change_none
.

(* Inductive mem_change_rel conf st: mem_change -> cmd -> Prop := *)
(* | mem_change_rel_alloca *)
(*     id ty v *)
(*     tsz gn a *)
(*     (TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz) *)
(*     (VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals)) *)
(*   : mem_change_rel conf st (mem_change_alloc tsz gn a) (insn_alloca id ty v a) *)
(* | mem_change_rel_malloc *)
(*     id ty v *)
(*     tsz gn a *)
(*     (TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz) *)
(*     (VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals)) *)
(*   : mem_change_rel conf st (mem_change_alloc tsz gn a) (insn_malloc id ty v a) *)
(* | mem_change_rel_store *)
(*     v_val gv_val *)
(*     v_ptr gv_ptr *)
(*     ty a sid *)
(*     (VAL: getOperandValue conf.(CurTargetData) v_val st.(EC).(Locals) conf.(Globals) = Some gv_val) *)
(*     (PTR: getOperandValue conf.(CurTargetData) v_ptr st.(EC).(Locals) conf.(Globals) = Some gv_ptr) *)
(*   : mem_change_rel conf st (mem_change_store gv_ptr ty gv_val a) *)
(*                    (insn_store sid ty v_val v_ptr a) *)
(* | mem_change_rel_free *)
(*     v_ptr gv_ptr fid ty *)
(*     (PTR: getOperandValue conf.(CurTargetData) v_ptr st.(EC).(Locals) conf.(Globals) = Some gv_ptr) *)
(*   : mem_change_rel conf st (mem_change_free gv_ptr) (insn_free fid ty v_ptr). *)
(* | mem_change_rel_none *)
(*     cmd *)
(*     (NON_ALLOCA =  *)
(*   : mem_change_rel conf st mem_change_none cmd *)

Definition mem_change_rel conf st mc cmd: Prop :=
  match cmd with
  | insn_alloca _ ty v a =>
    exists tsz gn,
    <<TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz>> /\
    <<VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gn>> /\
    <<MEM_CH: mc = mem_change_alloc tsz gn a>>
  | insn_malloc _ ty v a =>
    exists tsz gn,
    <<TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz>> /\
    <<VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gn>> /\
    <<MEM_CH: mc = mem_change_alloc tsz gn a>>
  | insn_store _ ty v_val v_ptr a =>
    exists gv_val gv_ptr,
    <<VAL: getOperandValue conf.(CurTargetData) v_val st.(EC).(Locals) conf.(Globals) = Some gv_val>> /\
    <<PTR: getOperandValue conf.(CurTargetData) v_ptr st.(EC).(Locals) conf.(Globals) = Some gv_ptr>> /\
    <<MEM_CH: mc = mem_change_store gv_ptr ty gv_val a>>
  | insn_free _ _ v_ptr =>
    exists gv_ptr,
    <<PTR: getOperandValue conf.(CurTargetData) v_ptr st.(EC).(Locals) conf.(Globals) = Some gv_ptr>> /\
    <<MEM_CH: mc = mem_change_free gv_ptr>>
  | _ => mc = mem_change_none
  end.

Definition mem_change_rel2 conf st mc cmd: Prop :=
  match cmd with
  | insn_alloca _ ty v a =>
    exists tsz gn,
    <<MEM_CH: mc = mem_change_alloc tsz gn a>>
  | insn_malloc _ ty v a =>
    exists tsz gn,
    <<MEM_CH: mc = mem_change_alloc tsz gn a>>
  | insn_store _ ty _ v_ptr a =>
    exists gv_val gv_ptr,
    <<PTR: getOperandValue conf.(CurTargetData) v_ptr st.(EC).(Locals) conf.(Globals) = Some gv_ptr>> /\
    <<MEM_CH: mc = mem_change_store gv_ptr ty gv_val a>>
  | insn_free _ _ v_ptr =>
    exists gv_ptr,
    <<PTR: getOperandValue conf.(CurTargetData) v_ptr st.(EC).(Locals) conf.(Globals) = Some gv_ptr>> /\
    <<MEM_CH: mc = mem_change_free gv_ptr>>
  | _ => mc = mem_change_none
  end.

Inductive mem_change_equiv (conf:Config) (mem0 mem1:mem): mem_change -> Prop :=
| mem_change_equiv_alloc
    mb bsz gn a
    (MALLOC: Some (mem1, mb) = malloc conf.(CurTargetData) mem0 bsz gn a)
  : mem_change_equiv conf mem0 mem1 (mem_change_alloc bsz gn a)
| mem_change_equiv_store
    ptr ty gv a
    (STORE: Some mem1 = mstore conf.(CurTargetData) mem0 ptr ty gv a)
  : mem_change_equiv conf mem0 mem1 (mem_change_store ptr ty gv a)
| mem_change_equiv_free
    ptr
    (FREE: Some mem1 = free conf.(CurTargetData) mem0 ptr)
  : mem_change_equiv conf mem0 mem1 (mem_change_free ptr)
| mem_change_equiv_none
    (MEM_EQ: mem0 = mem1)
  : mem_change_equiv conf mem0 mem1 mem_change_none
.

Inductive state_equiv_except_mem (conf:Config) (st0 st1:State) (mem_chng:mem_change) :=
| state_equiv_except_mem_intro
    (LOCALS_EQ: st0.(EC).(Locals) = st1.(EC).(Locals))
    (MEM_CHANGE_EQUIV: mem_change_equiv conf st0.(Mem) st1.(Mem) mem_chng)
.

Definition unique_preserved_mem conf st inv: Prop :=
  forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true),
    InvState.Unary.sem_unique conf st u.

(* Definition ptr_to_genericvalue conf st invst ptr: option (GenericValue * typ) := *)
(*   match InvState.Unary.sem_valueT conf st invst ptr.(fst) with *)
(*   | Some gv => Some (gv, ptr.(snd)) *)
(*   | None => None *)
(*   end. *)

Lemma some_injective A (a b:A):
  Some a = Some b -> a = b.
Proof.
  congruence.
Qed.

(* monotonic feature of ForgetMemory *)

Lemma not_in_maydiff_forget_memory_monotone
      def_mem_src def_mem_tgt inv0 v
      (NOT_MD: Invariant.not_in_maydiff (ForgetMemory.t def_mem_src def_mem_tgt inv0) v = true)
  : Invariant.not_in_maydiff inv0 v = true.
Proof.
  unfold Invariant.not_in_maydiff in *.
  unfold ForgetMemory.t in *.
  destruct def_mem_tgt; destruct def_mem_src; ss.
Qed.

Lemma ExprPairSet_forget_memory_monotone
      ep def_mem inv0
      (INJECT: ExprPairSet.mem ep (Invariant.lessdef (ForgetMemory.unary def_mem inv0)) = true)
  : ExprPairSet.mem ep (Invariant.lessdef inv0) = true.
Proof.
  unfold ForgetMemory.unary in *.
  des_ifs. ss.
  rewrite ExprPairSetFacts.filter_b in *; try by solve_compat_bool.
  rewrite andb_true_iff in *. des. eauto.
Qed.

Lemma inject_value_forget_memory_monotone
      v1 def_mem_src
      v2 def_mem_tgt
      inv0
      (INJECT: Invariant.inject_value
                 (ForgetMemory.t def_mem_src def_mem_tgt inv0) v1 v2)
  : Invariant.inject_value inv0 v1 v2.
Proof.
  unfold Invariant.inject_value in *.
  unfold is_true in *.
  repeat rewrite orb_true_iff in INJECT.
  repeat rewrite orb_true_iff.
  des.
  - left. left. left.
    solve_des_bool.
    apply andb_true_iff; split; eauto using not_in_maydiff_forget_memory_monotone.
  - left. left. right.
    solve_des_bool.
    apply andb_true_iff; split; eauto using not_in_maydiff_forget_memory_monotone.
    destruct def_mem_src; destruct def_mem_tgt; ss;
      eapply ExprPairSet_forget_memory_monotone; eauto.
  - left. right.
    solve_des_bool.
    apply andb_true_iff; split; eauto using not_in_maydiff_forget_memory_monotone.
    destruct def_mem_src; destruct def_mem_tgt; ss;
      eapply ExprPairSet_forget_memory_monotone; eauto.
  - right.
    rewrite <- ExprPairSetFacts.exists_iff in *;try by solve_compat_bool.
    unfold ExprPairSet.Exists in *. des.
    apply InvState.get_rhs_in_spec in INJECT. des.
    esplits.
    + eapply InvState.get_rhs_in_spec2; eauto.
      destruct def_mem_src; destruct def_mem_tgt; ss;
        rewrite ExprPairSetFacts.mem_iff in *;
        eapply ExprPairSet_forget_memory_monotone; eauto.
    + solve_des_bool.
      apply andb_true_iff.
      split.
      * destruct def_mem_src; destruct def_mem_tgt; ss;
          rewrite ExprPairSetFacts.mem_iff in *;
          eapply ExprPairSet_forget_memory_monotone; eauto.
      * unfold Invariant.not_in_maydiff_expr in *.
        apply forallb_forall. i.
        eapply forallb_forall in INJECT2; eauto.
        eapply not_in_maydiff_forget_memory_monotone; eauto.
Qed.

(* soundness *)

Lemma mem_inject_change
      conf_src mem0_src mem1_src mem_change_src
      conf_tgt mem0_tgt mem1_tgt mem_change_tgt
      invmem0
      (MEM_CHANGE_EQUIV_SRC : mem_change_equiv conf_src mem0_src mem1_src mem_change_src)
      (MEM_CHANGE_EQUIV_TGT : mem_change_equiv conf_tgt mem0_tgt mem1_tgt mem_change_tgt)
      (MEM_CHANGE_INJECT : mem_change_inject conf_src conf_tgt invmem0 mem_change_src mem_change_tgt)
      (INJECT : Memory.Mem.inject invmem0.(InvMem.Rel.inject) mem0_src mem0_tgt)
  : Memory.Mem.inject invmem0.(InvMem.Rel.inject) mem1_src mem1_tgt.
Proof.
  inv MEM_CHANGE_INJECT.
  - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold malloc in *.
    apply some_injective in MALLOC.
    apply some_injective in MALLOC0.
    econs.
    + eapply Memory.Mem.alloc_right_inj; eauto.
      eapply Memory.Mem.alloc_left_unmapped_inj; eauto.
      apply mi_freeblocks.
      eapply Memory.Mem.fresh_block_alloc; eauto.
    + i. apply mi_freeblocks. ii.
      exploit Memory.Mem.valid_block_alloc; try (symmetry; exact MALLOC); eauto.
    + ii. exploit mi_mappedblocks; eauto. i.
      eapply Memory.Mem.valid_block_alloc; eauto.
    + ii. exploit mi_no_overlap; eauto.
      * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
      * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
    + ii. exploit mi_representable; eauto. des.
      * left.
        eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
      * right.
        eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
  - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold malloc in *.
    apply some_injective in MALLOC.
    econs.
    + eapply Memory.Mem.alloc_left_unmapped_inj; eauto.
      apply mi_freeblocks.
      eapply Memory.Mem.fresh_block_alloc; eauto.
    + i. apply mi_freeblocks. ii.
      exploit Memory.Mem.valid_block_alloc; try (symmetry; exact MALLOC); eauto.
    + ii. exploit mi_mappedblocks; eauto.
    + ii. exploit mi_no_overlap; eauto.
      * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
      * eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
    + ii. exploit mi_representable; eauto. des.
      * left.
        eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
      * right.
        eapply Memory.Mem.perm_alloc_4; try (symmetry; exact MALLOC); eauto.
        ii. subst.
        hexploit Memory.Mem.fresh_block_alloc; try (symmetry; exact MALLOC); eauto. i.
        exploit mi_freeblocks; eauto. i. clarify.
  - inv INJECT. inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold malloc in *.
    apply some_injective in MALLOC.
    econs.
    + eapply Memory.Mem.alloc_right_inj; eauto.
    + i. apply mi_freeblocks. eauto.
    + ii. exploit mi_mappedblocks; eauto. i.
      eapply Memory.Mem.valid_block_alloc; eauto.
    + ii. exploit mi_no_overlap; eauto.
    + ii. exploit mi_representable; eauto.
  - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold mstore in *. des_ifs.
    (* exploit genericvalues_inject.mem_inj_mstore_aux; eauto. *)
    
    (* Memory.Mem.mem_inj *)
    (*   memory_sim.MoreMem.mem_inj *)
    admit. (* store - store *)
  - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold mstore in *. des_ifs.
    admit. (* store to private *)
    
  - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    unfold free in *. des_ifs.
    eapply Memory.Mem.free_left_inject; eauto.
    eapply Memory.Mem.free_right_inject; eauto.
    admit. (* free - free *)
  - inv MEM_CHANGE_EQUIV_SRC. inv MEM_CHANGE_EQUIV_TGT.
    eauto.
Admitted.

Lemma forget_memory_maydiff_preserved
      conf_src st0_src st1_src mem_change_src def_mem_src
      conf_tgt st0_tgt st1_tgt mem_change_tgt def_mem_tgt
      invst0 invmem0 inv0
      (MEM_EQUIV_SRC : state_equiv_except_mem conf_src st0_src st1_src mem_change_src)
      (MEM_EQUIV_TGT : state_equiv_except_mem conf_tgt st0_tgt st1_tgt mem_change_tgt)
      (MAYDIFF : forall id : Tag.t * id,
          IdTSet.mem id (Invariant.maydiff inv0) = false ->
          InvState.Rel.sem_inject st0_src st0_tgt invst0 (InvMem.Rel.inject invmem0) id)
  : <<RES: forall id : Tag.t * id,
      IdTSet.mem id (Invariant.maydiff (ForgetMemory.t def_mem_src def_mem_tgt inv0)) = false ->
      InvState.Rel.sem_inject st1_src st1_tgt invst0 (InvMem.Rel.inject invmem0) id>>.
Proof.
  ii.
  assert (DROP_FORGET_MEMORY:IdTSet.mem id0 (Invariant.maydiff inv0) = false).
  { destruct def_mem_src; destruct def_mem_tgt; ss. }
  exploit MAYDIFF; eauto.
  { inv MEM_EQUIV_SRC.
    unfold InvState.Unary.sem_idT in *.
    destruct id0 as [[] x]; eauto.
    ss. rewrite LOCALS_EQ. eauto.
  }
  i. des.
  esplits; eauto.
  inv MEM_EQUIV_TGT.
  unfold InvState.Unary.sem_idT in *.
  destruct id0 as [[] x]; eauto.
  ss. rewrite <- LOCALS_EQ. eauto.
Qed.

Lemma sem_idT_eq_locals
      st0 st1 invst0 x gv
      (SEM_IDT: InvState.Unary.sem_idT st1 invst0 x = Some gv)
      (LOCALS_EQ : Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_idT st0 invst0 x = Some gv.
Proof.
  destruct x as [[] x]; unfold InvState.Unary.sem_idT in *; ss.
  rewrite LOCALS_EQ; eauto.
Qed.    

Lemma sem_valueT_eq_locals
      conf st0 st1 invst0 v gv
      (SEM_EXPR: InvState.Unary.sem_valueT conf st0 invst0 v = Some gv)
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_valueT conf st1 invst0 v = Some gv.
Proof.
  destruct v; eauto.
  eapply sem_idT_eq_locals; eauto.
Qed.

Lemma sem_list_valueT_eq_locals
      conf st0 st1 invst0 lsv lgv
      (SEM_EXPR: InvState.Unary.sem_list_valueT conf st0 invst0 lsv = Some lgv)
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_list_valueT conf st1 invst0 lsv = Some lgv.
Proof.
  revert lgv SEM_EXPR.
  induction lsv; ss; i.
  des_ifs.
  - exploit IHlsv; eauto. i.
    symmetry in LOCALS_EQ.
    exploit sem_valueT_eq_locals; eauto. i. clarify.
  - exploit IHlsv; eauto. i.
    clarify.
  - exploit sem_valueT_eq_locals; eauto. i. clarify.
Qed.

Ltac sem_valueT_congruence :=
      repeat
        match goal with
        | [H1: InvState.Unary.sem_valueT ?conf ?st1 ?invst ?v = Some ?gv1,
               H2: InvState.Unary.sem_valueT ?conf ?st2 ?invst ?v = _,
                   LOCALS: Locals (EC ?st1) = Locals (EC ?st2) |- _] =>
          erewrite sem_valueT_eq_locals in H2; try exact H1; try exact LOCALS; inv H2
        | [H1: InvState.Unary.sem_list_valueT ?conf ?st1 ?invst ?lsv = Some ?lgv,
               H2: InvState.Unary.sem_list_valueT ?conf ?st2 ?invst ?lsv = _,
                   LOCALS: Locals (EC ?st1) = Locals (EC ?st2) |- _] =>
          erewrite sem_list_valueT_eq_locals in H2; try exact H1; try exact LOCALS; inv H2
        end;
      eauto; try congruence.

Lemma sem_expr_eq_locals_mem
      conf st0 st1 invst0 e gv
      (SEM_EXPR: InvState.Unary.sem_expr conf st0 invst0 e = Some gv)
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
      (MEM_EQ: Mem st0 = Mem st1)
  : InvState.Unary.sem_expr conf st1 invst0 e = Some gv.
Proof.
  destruct e; ss;
    des_ifs; sem_valueT_congruence; clarify.
  eapply sem_valueT_eq_locals; eauto.
Qed.

Lemma unary_sem_eq_locals_mem
      conf st0 st1 invst0 invmem0 inv0
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
      (MEM_EQ : Mem st0 = Mem st1)
  : InvState.Unary.sem conf st1 invst0 invmem0 inv0.
Proof.
  inv STATE.
  econs.
  - ii.
    exploit LESSDEF; eauto.
    { eapply sem_expr_eq_locals_mem; eauto. }
    i. des.
    esplits; eauto.
    exploit sem_expr_eq_locals_mem; eauto.
  - inv NOALIAS.
    econs; i; [exploit DIFFBLOCK | exploit NOALIAS0]; eauto;
      eapply sem_valueT_eq_locals; eauto.
  - ii. exploit UNIQUE; eauto. intro UNIQ_X. inv UNIQ_X.
    econs; try rewrite <- LOCALS_EQ; try rewrite <- MEM_EQ; eauto.
  - ii. exploit PRIVATE; eauto.
    eapply sem_idT_eq_locals; eauto.
Qed.

Lemma forget_memory_unary_sound1
      conf st0 invst0 invmem0 inv0
      cmd st1 public gmax mem_change def_memory
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
      (DEF_MEM: Cmd.get_def_memory cmd = Some def_memory)
      (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0)
      (MEM_EQUIV: state_equiv_except_mem conf st0 st1 mem_change)
      (MEM_CHANGE: mem_change_rel2 conf st0 mem_change cmd)
      (UNIQUE_PRSV: unique_preserved_mem conf st1 inv0)
  : <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem0 (ForgetMemory.unary def_memory inv0)>> /\
                   <<MEM_UNARY: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0>>.
Proof.
  destruct mem_change;
    try by (destruct cmd; ss; des; congruence).
  - splits.
    + inv STATE.
      (* econs; eauto. *)
      (* { ii. exploit LESSDEF; eauto. *)
      admit. (* lessdef - should treat load *)
    + inv MEM_EQUIV.
      inv MEM_CHANGE_EQUIV.
      inv MEM.
      admit. (* mstore, mstore_aux *)
  - splits.
    + inv STATE.
      (* econs. *)
      (* { ii. *)
      (*   exploit LESSDEF. *)
      (*   { admit. (* in - monotone *) } *)
      (*   { admit. (* sem_expr monotone? *) } *)
      (*   i. des. *)
      (*   esplits; eauto. *)
      (*   admit. *)
      (* } *)
      admit.
    + inv MEM_EQUIV.
      inv MEM_CHANGE_EQUIV.
      inv MEM.
      unfold free in *. des_ifs.
      econs; eauto.
      * i. exploit PRIVATE; eauto. i. des.
        split; eauto.
        exploit Memory.Mem.valid_block_free_1; eauto.
      * i. exploit PRIVATE_PARENT; eauto. i. des.
        split; eauto.
        exploit Memory.Mem.valid_block_free_1; eauto.
      *  i. exploit MEM_PARENT; eauto.
         admit. (* should handle mload_aux *)
Admitted.

Lemma forget_memory_unary_sound2
      conf st0 st1 mem_change
      cmd invst0 invmem0 inv0 gmax public
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
      (DEF_MEM: Cmd.get_def_memory cmd = None)
      (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0)
      (MEM_EQUIV : state_equiv_except_mem conf st0 st1 mem_change)
      (MEM_CHANGE : mem_change_rel2 conf st0 mem_change cmd)
      (UNIQUE_PRSV: unique_preserved_mem conf st1 inv0)
  : <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem0 inv0>> /\
    <<MEM_UNARY: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0>>.
Proof.
  destruct mem_change.
  - admit.
  - destruct cmd; ss; des; congruence.
  - destruct cmd; ss; des; congruence.
  - inv MEM_EQUIV. inv MEM_CHANGE_EQUIV.
    rewrite <- MEM_EQ.
    esplits; eauto.
    eapply unary_sem_eq_locals_mem; eauto.
Admitted.

Lemma forget_memory_sound
      conf_src st0_src st1_src mem_change_src cmd_src
      conf_tgt st0_tgt st1_tgt mem_change_tgt cmd_tgt
      invst0 invmem0 inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem0)
      (MEM_EQUIV_SRC: state_equiv_except_mem
                        conf_src
                        st0_src st1_src
                        mem_change_src)
      (MEM_EQUIV_TGT: state_equiv_except_mem
                        conf_tgt
                        st0_tgt st1_tgt
                        mem_change_tgt)
      (MEM_CHANGE_SRC: mem_change_rel2 conf_src st0_src mem_change_src cmd_src)
      (MEM_CHANGE_TGT: mem_change_rel2 conf_tgt st0_tgt mem_change_tgt cmd_tgt)
      (MEM_CHANGE_INJECT: mem_change_inject conf_src conf_tgt invmem0 mem_change_src mem_change_tgt)
      (UNIQUE_PRSV_SRC: unique_preserved_mem conf_src st1_src inv0.(Invariant.src))
      (UNIQUE_PRSV_TGT: unique_preserved_mem conf_tgt st1_tgt inv0.(Invariant.tgt))
  : <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0
                              (ForgetMemory.t (Cmd.get_def_memory cmd_src) (Cmd.get_def_memory cmd_tgt) inv0) >> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem0>>.
Proof.
  inv STATE. inv MEM.
  
  destruct (Cmd.get_def_memory cmd_src) eqn:DEF_MEM_SRC;
    destruct (Cmd.get_def_memory cmd_tgt) eqn:DEF_MEM_TGT.
  - hexploit forget_memory_unary_sound1; try exact SRC; try exact DEF_MEM_SRC; eauto. i. des.
    hexploit forget_memory_unary_sound1; try exact TGT; try exact DEF_MEM_TGT; eauto. i. des.
    hexploit forget_memory_maydiff_preserved; try exact MAYDIFF; eauto. i. des.
    inv MEM_EQUIV_SRC. inv MEM_EQUIV_TGT.
    hexploit mem_inject_change; try exact MEM_CHANGE_INJECT; eauto. i.
    esplits; econs; eauto.
  - hexploit forget_memory_unary_sound1; try exact SRC; try exact DEF_MEM_SRC; eauto. i. des.
    hexploit forget_memory_unary_sound2; try exact TGT; try exact DEF_MEM_TGT; eauto. i. des.
    hexploit forget_memory_maydiff_preserved; try exact MAYDIFF; eauto. i. des.
    inv MEM_EQUIV_SRC. inv MEM_EQUIV_TGT.
    hexploit mem_inject_change; try exact MEM_CHANGE_INJECT; eauto. i.
    esplits; econs; eauto.
  - hexploit forget_memory_unary_sound2; try exact SRC; try exact DEF_MEM_SRC; eauto. i. des.
    hexploit forget_memory_unary_sound1; try exact TGT; try exact DEF_MEM_TGT; eauto. i. des.
    hexploit forget_memory_maydiff_preserved; try exact MAYDIFF; eauto. i. des.
    inv MEM_EQUIV_SRC. inv MEM_EQUIV_TGT.
    hexploit mem_inject_change; try exact MEM_CHANGE_INJECT; eauto. i.
    esplits; econs; eauto.
  - hexploit forget_memory_unary_sound2; try exact SRC; try exact DEF_MEM_SRC; eauto. i. des.
    hexploit forget_memory_unary_sound2; try exact TGT; try exact DEF_MEM_TGT; eauto. i. des.
    hexploit forget_memory_maydiff_preserved; try exact MAYDIFF; eauto. i. des.
    inv MEM_EQUIV_SRC. inv MEM_EQUIV_TGT.
    hexploit mem_inject_change; try exact MEM_CHANGE_INJECT; eauto. i.
    esplits; econs; eauto.
Qed.
    
(*     esplits. *)
(*     + econs; eauto. *)
(*       ss. i. *)
(*       hexploit MAYDIFF; eauto. i. *)
(*       ii. *)
(*       i. *)
(*       ss. eauto. *)
(*       admit. *)
(*     + econs; eauto. *)
(*       eapply mem_inject_change; eauto. *)
(*       * inv MEM_EQUIV_SRC; eauto. *)
(*       * inv MEM_EQUIV_TGT; eauto. *)
(*   - *)
  
(*   inv STATE. *)
(*   destruct mem_change_src; destruct mem_change_tgt; inv MEM_CHANGE_INJECT. *)
(*   - destruct cmd_src eqn:CMDSRC; destruct cmd_tgt eqn:CMDTGT; ss; des; *)
(*       try congruence. *)
(*     + inv MEM_CH; inv MEM_CH0. *)
(*     +  *)

(*     admit. (* alloc - alloc *) } *)
(*   { admit. (* alloc - none *) } *)
(*   { admit. (* store - store *) } *)
(*   { admit. (* store - none *) } *)
(*   { admit. (* free - free *) } *)
(*   { admit. (* none - alloc *) } *)
(*   { admit. (* none - none *) } *)


  
(*   destruct (Cmd.get_def_memory cmd_src) eqn:DEF_MEM_SRC; *)
(*     destruct (Cmd.get_def_memory cmd_tgt) eqn:DEF_MEM_TGT. *)
(*   - destruct cmd_src; destruct cmd_tgt; ss. *)
(*     + admit. (* free - free *) *)
(*     + admit. (* free - store : cont. *) *)
(*     + admit. (* store - free : cont.  *) *)
(*     + admit. (* store - store *) *)
(*   - (* destruct cmd_src; destruct cmd_tgt; ss. *) *)
(*     admit. *)
(*   - admit. *)
(*   - ss. *)
(*     unfold mem_change_rel2 in *. *)
(*     destruct cmd_src; destruct cmd_tgt; ss. *)




  
(*   unfold ForgetMemory.t. *)
(*   destruct def_memory_src as [[]|], def_memory_tgt as [[]|]; ss. *)
(*   inv MEM. *)

(*   - exploit forget_memory_unary_sound1; try exact SRC; eauto. i. des. *)
(*     exploit forget_memory_unary_sound1; try exact TGT; eauto. i. des. *)
(*     splits. *)
(*     + econs; ss; eauto. i. *)
(*       hexploit MAYDIFF; eauto. i. *)
(*       ii. exploit H. *)
(*       { destruct id0 as [[]]; eauto. *)
(*         inv MEM_EQUIV_SRC; solve_sem_idT. *)
(*         rewrite -> LOCALS_EQ; eauto. *)
(*       } *)
(*       i. des. *)
(*       esplits; eauto. *)
(*       destruct id0 as [[]]; eauto. *)
(*       inv MEM_EQUIV_TGT; *)
(*         solve_sem_idT; rewrite <- LOCALS_EQ; eauto. *)
(*     + econs; ss; eauto. *)
(*       inv MEM_EQUIV_SRC. *)
(*       inv MEM_EQUIV_TGT. *)

(*       eapply mem_inject_change; eauto. *)
      
(*   - inv MEM. *)
(*     exploit forget_memory_unary_sound1; try exact SRC; eauto. i. des. *)
(*     exploit forget_memory_unary_sound2; try exact TGT; eauto. i. des. *)
(*     splits. *)
(*     + econs; ss; eauto. *)
(*       i. *)
(*       hexploit MAYDIFF; eauto. i. *)
(*       ii. exploit H. *)
(*       { destruct id0 as [[]]; eauto. *)
(*         inv MEM_EQUIV_SRC; solve_sem_idT. *)
(*         rewrite -> LOCALS_EQ; eauto. *)
(*       } *)
(*       i. des. *)
(*       esplits; eauto. *)
(*       destruct id0 as [[]]; eauto. *)
(*       inv MEM_EQUIV_TGT; *)
(*         solve_sem_idT; rewrite <- LOCALS_EQ; eauto. *)
(*     + econs; ss; eauto. *)
(*       inv MEM_EQUIV_SRC. *)
(*       inv MEM_EQUIV_TGT. *)
(*       eapply mem_inject_change; eauto. *)
(*   - inv MEM. *)
(*     exploit forget_memory_unary_sound2; try exact SRC; eauto. i. des. *)
(*     exploit forget_memory_unary_sound1; try exact TGT; eauto. i. des. *)
(*     splits. *)
(*     + econs; ss; eauto. *)
(*       i. *)
(*       hexploit MAYDIFF; eauto. i. *)
(*       ii. exploit H. *)
(*       { destruct id0 as [[]]; eauto. *)
(*         inv MEM_EQUIV_SRC; solve_sem_idT. *)
(*         rewrite -> LOCALS_EQ; eauto. *)
(*       } *)
(*       i. des. *)
(*       esplits; eauto. *)
(*       destruct id0 as [[]]; eauto. *)
(*       inv MEM_EQUIV_TGT; *)
(*         solve_sem_idT; rewrite <- LOCALS_EQ; eauto. *)
(*     + econs; ss; eauto. *)
(*       inv MEM_EQUIV_SRC. *)
(*       inv MEM_EQUIV_TGT. *)
(*       eapply mem_inject_change; eauto. *)
(*   - inv MEM. *)
(*     exploit forget_memory_unary_sound2; try exact SRC; eauto. i. des. *)
(*     exploit forget_memory_unary_sound2; try exact TGT; eauto. i. des. *)
(*     splits. *)
(*     + econs; ss; eauto. *)
(*       i. *)
(*       hexploit MAYDIFF; eauto. i. *)
(*       ii. exploit H. *)
(*       { destruct id0 as [[]]; eauto. *)
(*         inv MEM_EQUIV_SRC; solve_sem_idT. *)
(*         rewrite -> LOCALS_EQ; eauto. *)
(*       } *)
(*       i. des. *)
(*       esplits; eauto. *)
(*       destruct id0 as [[]]; eauto. *)
(*       inv MEM_EQUIV_TGT; *)
(*         solve_sem_idT; rewrite <- LOCALS_EQ; eauto. *)
(*     + econs; ss; eauto. *)
(*       inv MEM_EQUIV_SRC. *)
(*       inv MEM_EQUIV_TGT. *)
(*       eapply mem_inject_change; eauto. *)
(* Admitted. *)
