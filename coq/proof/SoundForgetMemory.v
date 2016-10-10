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
    (def_var:id) (b:mblock) (ty:typ) (s:sz) (gn:GenericValue) (a:align)
| mem_change_store
    (ptr:GenericValue) (ty:typ) (gv:GenericValue) (a:align)
| mem_change_free
    (ptr:GenericValue)
| mem_change_none
.

Inductive mem_change_inject (conf_src conf_tgt:Config) invmem: mem_change -> mem_change -> Prop :=
| mem_change_inject_alloc_alloc
    gsz gn0 gn1 a
    b_src b_tgt ty dv
    (N_INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gn0 gn1)
  : mem_change_inject conf_src conf_tgt invmem (mem_change_alloc dv b_src ty gsz gn0 a) (mem_change_alloc dv b_tgt ty gsz gn1 a)
| mem_change_inject_alloc_none
    gsz gn a b ty dv
  : mem_change_inject conf_src conf_tgt invmem (mem_change_alloc dv b ty gsz gn a) mem_change_none
| mem_change_inject_none_alloc
    gsz gn a b ty dv
  : mem_change_inject conf_src conf_tgt invmem mem_change_none (mem_change_alloc dv b ty gsz gn a)
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

Inductive states_mem_change (conf:Config) (st0 st1:State): mem_change -> Prop :=
| states_mem_change_alloc
    mb ty bsz gn a dv
    (MALLOC: Some (st1.(Mem), mb) = malloc conf.(CurTargetData) st0.(Mem) bsz gn a)
    (UNIQUE: InvState.Unary.sem_unique conf st0 dv)
    (DEF_VAR: lookupAL _ st1.(EC).(Locals) dv = Some (blk2GV conf.(CurTargetData) mb))
  : states_mem_change conf st0 st1 (mem_change_alloc dv mb ty bsz gn a)
| states_mem_change_store
    ptr ty gv a
    (STORE: Some st1.(Mem) = mstore conf.(CurTargetData) st0.(Mem) ptr ty gv a)
  : states_mem_change conf st0 st1 (mem_change_store ptr ty gv a)
| states_mem_change_free
    ptr
    (FREE: Some st1.(Mem) = free conf.(CurTargetData) st0.(Mem) ptr)
  : states_mem_change conf st0 st1 (mem_change_free ptr)
| states_mem_change_none
    (MEM_EQ: st0.(Mem) = st1.(Mem))
  : states_mem_change conf st0 st1 mem_change_none
.

Inductive state_equiv_except_mem (conf:Config) (st0 st1:State) (mem_chng:mem_change) :=
| state_equiv_except_mem_intro
    (LOCALS_EQ: st0.(EC).(Locals) = st1.(EC).(Locals))
    (STATES_MEM_CHANGE: states_mem_change conf st0 st1 mem_chng)
.

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

(* Difference btw rel and rel_after: changing locals & forget *)

Definition mem_change_cmd conf st mc cmd: Prop :=
  match cmd with
  | insn_alloca dv ty v a =>
    exists mb tsz gn,
    <<TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz>> /\
    <<VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gn>> /\
    <<MEM_CH: mc = mem_change_alloc dv mb ty tsz gn a>>
  | insn_malloc dv ty v a =>
    exists mb tsz gn,
    <<TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz>> /\
    <<VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gn>> /\
    <<MEM_CH: mc = mem_change_alloc dv mb ty tsz gn a>>
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

Definition mem_change_cmd_after conf st mc cmd inv0: Prop :=
  match cmd with
  | insn_alloca dv ty v a =>
    exists mb tsz gn,
    <<TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz>> /\
    (* <<VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gn>> /\ *)
    <<FORGET: inv_unary_forgot inv0 (AtomSetImpl.singleton dv)>> /\
    <<MEM_CH: mc = mem_change_alloc dv mb ty tsz gn a>>
  | insn_malloc dv ty v a =>
    exists mb tsz gn,
    <<TYPE: getTypeAllocSize conf.(CurTargetData) ty = Some tsz>> /\
    (* <<VAL: getOperandValue conf.(CurTargetData) v st.(EC).(Locals) conf.(Globals) = Some gn>> /\ *)
    <<FORGET: inv_unary_forgot inv0 (AtomSetImpl.singleton dv)>> /\
    <<MEM_CH: mc = mem_change_alloc dv mb ty tsz gn a>>
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

Definition unique_preserved_mem conf st inv: Prop :=
  forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true),
    InvState.Unary.sem_unique conf st u.

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

Lemma forget_memory_unary_sound1
      conf st0 invst0 invmem0 inv0
      cmd st1 public gmax mem_change def_memory
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
      (DEF_MEM: Cmd.get_def_memory cmd = Some def_memory)
      (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0)
      (MEM_EQUIV: state_equiv_except_mem conf st0 st1 mem_change)
      (MEM_CHANGE: mem_change_cmd_after conf st0 mem_change cmd inv0)
      (NO_PRIVATE_PARENT: mem_change_no_private_parent conf mem_change invmem0.(InvMem.Unary.private_parent))
      (UNIQUE_PRSV: unique_preserved_mem conf st1 inv0)
  : <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem0 (ForgetMemory.unary def_memory inv0)>> /\
                   <<MEM_UNARY: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0>>.
Proof.
  destruct mem_change;
    try by (destruct cmd; ss; des; congruence).
  - splits.
    admit.
    admit.
    
    
    (* + econs. *)
    (*   { ii. ss. unfold ForgetMemory.unary in *. *)
    (*     exploit forget_memory_def_sep_mem; eauto. i. *)
    (*     exploit sem_expr_equiv_except_mem; eauto. *)
    (*     { instantiate (1:= (fst x)). *)
    (*       des; try by left; eauto. *)
    (*       right. unfold ForgetMemory.is_noalias_ExprPair in *. des_bool. des. ss. *)
    (*     } *)
    (*     exploit sem_expr_equiv_except_mem; eauto. *)
    (*     { instantiate (1:= (snd x)). *)
    (*       des; try by left; eauto. *)
    (*       right. unfold ForgetMemory.is_noalias_ExprPair in *. des_bool. des. ss. *)
    (*     } *)
    (*     i. *)
    (*     inv STATE. *)
    (*     exploit LESSDEF. *)
    (*     { des_ifs; eauto. *)
    (*       ss. eapply ExprPairSetFacts.filter_iff in H; eauto; try by solve_compat_bool. inv H; eauto. *)
    (*     } *)
    (*     { rewrite x0. eauto. } *)
    (*     i. rewrite <- x2. eauto. *)
    (*   } *)
    (*   { admit. (* alias *) } *)
    (*   { admit. } *)
    (*   { admit. } *)
    (* + inv MEM_EQUIV. *)
    (*   inv MEM_CHANGE_EQUIV. *)
    (*   inv MEM. *)
    (*   econs; eauto. *)
    (*   { i. exploit PRIVATE; eauto. i. des. *)
    (*     split; eauto. *)
    (*     admit. (* nextblock preserved after mstore *) } *)
    (*   { i. exploit PRIVATE_PARENT; eauto. i. des. *)
    (*     split; eauto. *)
    (*     admit. (* same *) } *)
    (*   { unfold mem_change_no_private_parent in *. *)
    (*     i. exploit MEM_PARENT; eauto. *)
    (*     i. rewrite x. *)
    (*     (* STORE: (Mem st1) = mstore (Mem st0) ptr .. *) *)
    (*     (* mstore says GV2ptr ptr = Some Vptr .. *) *)
    (*     (* NO_PRIVATE_PARENT tells us ~In b_ptr (private_parent) *) *)
    (*     (* since b is In private_parent, mload_aux ?mem b should be preserved *) *)
    (*     admit. *)
    (*   } *)
  
  - admit. (* free case - almost same as above *)
Admitted.

Lemma forget_memory_unary_sound2
      conf st0 st1 mem_change
      cmd invst0 invmem0 inv0 gmax public
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 inv0)
      (DEF_MEM: Cmd.get_def_memory cmd = None)
      (MEM: InvMem.Unary.sem conf gmax public st0.(Mem) invmem0)
      (MEM_EQUIV : state_equiv_except_mem conf st0 st1 mem_change)
      (MEM_CHANGE : mem_change_cmd_after conf st0 mem_change cmd inv0)
      (NO_PRIVATE_PARENT: mem_change_no_private_parent conf mem_change invmem0.(InvMem.Unary.private_parent))
      (UNIQUE_PRSV: unique_preserved_mem conf st1 inv0)
  : <<STATE_UNARY: InvState.Unary.sem conf st1 invst0 invmem0 inv0>> /\
    <<MEM_UNARY: InvMem.Unary.sem conf gmax public st1.(Mem) invmem0>>.
Proof.
  destruct mem_change.
  - destruct cmd; ss.
    + admit. (* TODO: doing here *)
    + admit. (* exactly same as above *)
  - destruct cmd; ss; des; congruence.
  - destruct cmd; ss; des; congruence.
  - inv MEM_EQUIV. inv STATES_MEM_CHANGE.
    rewrite <- MEM_EQ.
    esplits; eauto.
    eapply unary_sem_eq_locals_mem; try (symmetry in LOCALS_EQ; exact LOCALS_EQ); eauto.
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

Lemma some_injective A (a b:A):
  Some a = Some b -> a = b.
Proof.
  congruence.
Qed.

Lemma mem_inject_change
      conf_src st0_src st1_src mem_change_src
      conf_tgt st0_tgt st1_tgt mem_change_tgt
      invmem0
      (MEM_CHANGE_EQUIV_SRC : states_mem_change conf_src st0_src st1_src mem_change_src)
      (MEM_CHANGE_EQUIV_TGT : states_mem_change conf_tgt st0_tgt st1_tgt mem_change_tgt)
      (MEM_CHANGE_INJECT : mem_change_inject conf_src conf_tgt invmem0 mem_change_src mem_change_tgt)
      (INJECT : Memory.Mem.inject invmem0.(InvMem.Rel.inject) st0_src.(Mem) st0_tgt.(Mem))
  : Memory.Mem.inject invmem0.(InvMem.Rel.inject) st1_src.(Mem) st1_tgt.(Mem).
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
    rewrite <- MEM_EQ; clear MEM_EQ.
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
    rewrite <- MEM_EQ; clear MEM_EQ.
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

Lemma forget_memory_sound
      m_src conf_src st0_src st1_src mem_change_src cmd_src
      m_tgt conf_tgt st0_tgt st1_tgt mem_change_tgt cmd_tgt
      invst0 invmem0 inv0
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
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
      (MEM_CHANGE_SRC: mem_change_cmd_after conf_src st0_src mem_change_src cmd_src inv0.(Invariant.src))
      (MEM_CHANGE_TGT: mem_change_cmd_after conf_tgt st0_tgt mem_change_tgt cmd_tgt inv0.(Invariant.tgt))
      (MEM_CHANGE_INJECT: mem_change_inject conf_src conf_tgt invmem0 mem_change_src mem_change_tgt)
      (UNIQUE_PRSV_SRC: unique_preserved_mem conf_src st1_src inv0.(Invariant.src))
      (UNIQUE_PRSV_TGT: unique_preserved_mem conf_tgt st1_tgt inv0.(Invariant.tgt))
  : <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0
                              (ForgetMemory.t (Cmd.get_def_memory cmd_src) (Cmd.get_def_memory cmd_tgt) inv0) >> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem0>>.
Proof.
  exploit mem_change_inject_no_private_parent_src; eauto. intro NO_PRIVATE_PARENT_SRC.
  exploit mem_change_inject_no_private_parent_tgt; eauto. intro NO_PRIVATE_PARENT_TGT.
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
