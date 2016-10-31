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
Require Import SoundForgetMemory.

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

Lemma valid_ptr_malloc_diffblock
      SRC_MEM val'
      (VALID_PTR: MemProps.valid_ptrs (Memory.Mem.nextblock SRC_MEM) val')
      TD align0 tsz gn SRC_MEM_STEP mb
      (MALLOC: malloc TD SRC_MEM tsz gn align0 = Some (SRC_MEM_STEP, mb))
      conf_src
  :
    <<DIFFBLOCK: InvState.Unary.sem_diffblock conf_src (blk2GV TD mb) val'>>
.
Proof.
  exploit MemProps.nextblock_malloc; try apply MALLOC; []; ii; des.
  exploit MemProps.malloc_result; try apply MALLOC; []; ii; des.
  subst.

  unfold InvState.Unary.sem_diffblock.
  destruct val'; ss.
  destruct p; ss.
  destruct v; ss.
  des.
  destruct val'; ss.
  unfold not; ii; subst.
  exploit Pos.lt_irrefl; eauto.
Qed.

Lemma locals_malloc_diffblock
      conf_src mem locals
      TD tsz gn align0 SRC_MEM_STEP mb
      reg val
      (MALLOC: malloc TD mem tsz gn align0 = Some (SRC_MEM_STEP, mb))
      (VAL: lookupAL GenericValue locals reg = Some val)
      (WF_LOCAL: MemProps.wf_lc mem locals)
  :
  <<DIFFBLOCK: InvState.Unary.sem_diffblock conf_src (blk2GV TD mb) val>>
.
Proof.
  exploit WF_LOCAL; eauto; []; intro WF; des.
  eapply valid_ptr_malloc_diffblock; eauto.
Qed.

Lemma globals_malloc_diffblock
      align0 TD gn SRC_MEM SRC_MEM_STEP
      tsz conf_src mb gid val
      gmax
      (WF_GLOBALS: genericvalues_inject.wf_globals gmax (Globals conf_src))
      (MALLOC: malloc TD SRC_MEM tsz gn align0 = Some (SRC_MEM_STEP, mb))
      (WF_MEM: MemProps.wf_Mem gmax (CurTargetData conf_src) SRC_MEM)
      (VAL: lookupAL GenericValue (Globals conf_src) gid = Some val)
  :
    <<DIFFBLOCK: InvState.Unary.sem_diffblock conf_src (blk2GV TD mb) val>>
.
Proof.
  unfold MemProps.wf_Mem in *. des.
  induction (Globals conf_src); ii; ss.
  destruct a; ss.
  destruct (gid == i0); ss; clarify.
  - (* gid == i0 *)
    clear IHg.
    destruct val; ss.
    destruct p; ss.
    destruct v; ss.
    des. red.
    unfold InvState.Unary.sem_diffblock. ss.
    destruct val; ss.
    exploit MemProps.nextblock_malloc; try apply MALLOC; []; ii; des. clarify.
    exploit MemProps.malloc_result; try apply MALLOC; []; ii; des. clarify.
    clear - WF_MEM0 WF_GLOBALS.
    exploit Pos.le_lt_trans; eauto; []; ii; des.
    exploit Pos.lt_irrefl; eauto.
  - (* IH case *)
    des.
    eapply IHg; eauto.
Qed.

Lemma mload_malloc_diffblock
  align0 TD gn tsz conf_src SRC_MEM SRC_MEM_STEP mb
  (MALLOC: malloc TD SRC_MEM tsz gn align0 = Some (SRC_MEM_STEP, mb))
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
  exploit MemProps.malloc_preserves_mload_inv; try apply LOAD; eauto; []; ii.
  des.
  - exploit WF_A; try apply LOAD; eauto; []; clear WF_A; intros WF_A; des.
    clear - MALLOC WF_A.
    eapply valid_ptr_malloc_diffblock; eauto.
  - unfold not in x1.
    unfold InvState.Unary.sem_diffblock.
    destruct val'; ss.
    destruct p; ss.
    exploit x0; eauto; []; ii; des.
    subst. ss.
Unshelve.
eauto.
Qed.

(* CALL FOR DISCUSSION *)
(* Stronger premise, *)
(* easier to prove, harder to use in theory *)
(* However, actually it is more convenient to use, as we do not need to inv MEM *)

(* Heard weird behavior of "apply" from @jhk, now I will state in fine-grained way.
Added space in Axio m in order to avoid grep

Axio m P: Prop.
Axio m Q: Prop.
Axio m R: Prop.
Axio m S: Prop.
Inductive PQ: Prop :=
| PQ_intro: P -> Q -> PQ
.
Inductive RS: Prop :=
| RS_intro: R -> S -> RS
.
Inductive PQRS: Prop :=
| PQRS_intro:  PQ -> RS -> PQRS
.

Goal PQ -> P. ii. auto. eauto. apply H. Qed.
Goal PQRS -> P. ii. auto. eauto. apply H. Qed.
 *)

(* Will later be substituted by @yoonseung's implementation *)
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

Lemma add_unique_malloc
  cmds_src
  id0
  align0
  inv_unary
  TD
  F
  B
  lc
  gn
  ECS0
  tmn
  SRC_MEM
  als
  SRC_MEM_STEP
  tsz
  mb
  conf_src
  gmax
  (MALLOC: malloc TD SRC_MEM tsz gn align0 = Some (SRC_MEM_STEP, mb))
  (UNIQUE: AtomSetImpl.For_all
             (InvState.Unary.sem_unique conf_src
                {|
                EC := {|
                      CurFunction := F;
                      CurBB := B;
                      CurCmds := cmds_src;
                      Terminator := tmn;
                      Locals := updateAddAL GenericValue lc id0 (blk2GV TD mb);
                      Allocas := mb :: als |};
                ECS := ECS0;
                Mem := SRC_MEM_STEP |}) (Invariant.unique inv_unary))
  (WF : MemProps.wf_Mem gmax (CurTargetData conf_src) SRC_MEM)
  (GLOBALS : genericvalues_inject.wf_globals gmax (Globals conf_src))
  (WF_LOCAL : MemProps.wf_lc SRC_MEM lc)
  :
  <<UNIQUE_ADD: AtomSetImpl.For_all
    (InvState.Unary.sem_unique conf_src
       {|
       EC := {|
             CurFunction := F;
             CurBB := B;
             CurCmds := cmds_src;
             Terminator := tmn;
             Locals := updateAddAL GenericValue lc id0 (blk2GV TD mb);
             Allocas := mb :: als |};
       ECS := ECS0;
       Mem := SRC_MEM_STEP |}) (add id0 (Invariant.unique inv_unary))>>
.
Proof.
  intros x xIn.
  apply AtomSetFacts.add_iff in xIn.
  des; [clear UNIQUE; subst id0|apply UNIQUE; auto].
  econs; eauto; ss.
  +
    (* VAL *)
    des_lookupAL_updateAddAL.
  +
    (* LOCALS *)
    ii.
    des_lookupAL_updateAddAL.
    eapply locals_malloc_diffblock; ss; eauto.
  +
    (* MEM *)
    ii. eapply mload_malloc_diffblock; eauto.
  +
    (* GLOBALS *)
    ii. eapply globals_malloc_diffblock; eauto.
Qed.

Lemma add_private
  id5
  typ5
  value5
  align5
  cmds_src
  invst_unary
  invmem_unary
  inv_unary
  S
  TD
  Ps
  F
  B
  lc
  gl fs
  gn
  ECS0
  tmn
  Mem0
  als
  Mem'
  tsz
  mb
  (MALLOC : malloc TD Mem0 tsz gn align5 = Some (Mem', mb))
  (H1 : getOperandValue TD value5 lc gl = Some gn)
  (H0 : getTypeAllocSize TD typ5 = Some tsz)
  (ALLOC_PRIVATE : forall (x : id) (ty : typ) (v : value) (a : align),
                  GVsMap ->
                  insn_alloca id5 typ5 value5 align5 = insn_alloca x ty v a ->
                  Some mem_change_none = Some mem_change_none ->
                  exists gptr : GenericValue,
                    In (Memory.Mem.nextblock Mem0) (InvMem.Unary.private invmem_unary) /\
                    lookupAL GenericValue (updateAddAL GenericValue lc id5 (blk2GV TD mb)) x = Some gptr /\
                    GV2ptr TD (getPointerSize TD) gptr =
                    Some (Values.Vptr (Memory.Mem.nextblock Mem0) (Integers.Int.zero 31)))
  (PRIVATE : IdTSet.For_all
              (InvState.Unary.sem_private
                 {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}
                 {|
                 EC := {|
                       CurFunction := F;
                       CurBB := B;
                       CurCmds := cmds_src;
                       Terminator := tmn;
                       Locals := updateAddAL GenericValue lc id5 (blk2GV TD mb);
                       Allocas := mb :: als |};
                 ECS := ECS0;
                 Mem := Mem' |} invst_unary (InvMem.Unary.private invmem_unary))
              (Invariant.private inv_unary))
  :
  <<PRIVATE_ADD: IdTSet.For_all
    (InvState.Unary.sem_private
       {| CurSystem := S; CurTargetData := TD; CurProducts := Ps; Globals := gl; FunTable := fs |}
       {|
       EC := {|
             CurFunction := F;
             CurBB := B;
             CurCmds := cmds_src;
             Terminator := tmn;
             Locals := updateAddAL GenericValue lc id5 (blk2GV TD mb);
             Allocas := mb :: als |};
       ECS := ECS0;
       Mem := Mem' |} invst_unary (InvMem.Unary.private invmem_unary))
    (IdTSet.add (IdT.lift Tag.physical id5) (Invariant.private inv_unary))>>
.
Proof.
  intros ____id____ IN. (* SHOULD NOT USE ii HERE, OR BELOW eauto WILL NOT WORK!! WHY? *)
  eapply IdTSetFacts.add_iff in IN.
  des; [|eauto]; [].
  subst.
  ii. ss.
  u. ss. des_lookupAL_updateAddAL. clear_true.
  ss.
  destruct invmem_unary; simpl.
  ss.
  assert(GGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGGG: True)
    by auto.
  move mb at bottom.
  move private at bottom.
  unfold alloc_private in *.
  unfold alloc_private_unary in *.
  des.
  remember {|
      EC := {|
             CurFunction := F;
             CurBB := B;
             CurCmds := cmds_src;
             Terminator := tmn;
             Locals := updateAddAL GenericValue lc id5 (blk2GV TD mb);
             Allocas := mb :: als |};
      ECS := ECS0;
      Mem := Mem' |} as st_src.
  ss.
  exploit ALLOC_PRIVATE; eauto; []; ii; des.
  exploit MemProps.malloc_result; try apply MALLOC; []; intro MALLOC_RES1; des.
  subst. ss.
Qed.

(* TODO: let's ignore insn_malloc for now.  Revise the validator so that it rejects any occurence of insn_malloc. *)
Lemma postcond_cmd_add_inject_sound
      m_src conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
      m_tgt conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt
      invst1 invmem1 inv1
      invst0 invmem0 inv0
      evt
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (POSTCOND_CHECK: Postcond.postcond_cmd_check
                   cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
      (STATE_STEP: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1 inv1)
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
      (ALLOC_INJECT: alloc_inject conf_src conf_tgt st0_src st0_tgt
                                  st1_src st1_tgt cmd_src cmd_tgt invmem1)
      (ALLOC_PRIVATE: alloc_private conf_src conf_tgt cmd_src cmd_tgt st0_src st0_tgt
                                    st1_src st1_tgt invmem1)
      (* (ALLOC_INJECT: InvMem.Rel.inject invmem1 (st0_src.(Mem).(Memory.Mem.nextblock)) = *)
      (*                Some((st0_tgt.(Mem).(Memory.Mem.nextblock)), 0)) *)
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
  destruct (classic (Postcond.postcond_cmd_add_inject cmd_src cmd_tgt inv1 = inv1)).
  { rewrite H in *. esplits; eauto. }
  destruct cmd_src, cmd_tgt; ss.
  - (* alloca, nop *)
    clear ALLOC_INJECT.
    unfold postcond_cmd_check in *. des_ifs; des_bool; clarify.
    ss. clear_true.
    splits; ss.
    apply_all_once AtomSetImpl_from_list_inter_is_empty.
    simpl_list.

    inv STATE_STEP.

    ((inv STEP_SRC; ss); []).
    (* inv SRC. *)
    inv CMDS_SRC.

    econs; eauto; [].

    ((inv STEP_TGT; ss); []).
    (* inv TGT. *)
    inv CMDS_TGT.
    ss.
    clear MAYDIFF.

    inv TGT.
    clear H H2.
    clear MEM_STEP.
    clear CONF.
    (* inv TGT. clear LESSDEF0 NOALIAS0 UNIQUE0 PRIVATE0 WF_LOCAL0. *)
    unfold alloc_private, alloc_private_unary in *. ss.
    destruct ALLOC_PRIVATE as [_ ALLOC_PRIVATE].
    econs; eauto; [|]; clear LESSDEF NOALIAS WF_LOCAL.
    +
      clear ALLOC_PRIVATE.
      clear PRIVATE.
      unfold Invariant.update_src. ss.
      intros ____id____ IN.
      eapply AtomSetFacts.add_iff in IN.
      des; [|eauto]; [].
      subst.
      (* TODO BELOW IS EXACTLY COPIED FROM ALLOCA/ALLOCA CASE *)
      eapply add_unique_malloc; eauto; try apply MEM; try apply STATE.
    + clear UNIQUE.
      clear MEM SRC STATE.
      unfold Invariant.update_private. ss.
      eapply add_private; eauto.
  - (* nop, allica *)
    clear ALLOC_INJECT.
    unfold postcond_cmd_check in *. des_ifs; des_bool; clarify.
    ss. clear_true.
    splits; ss.
    apply_all_once AtomSetImpl_from_list_inter_is_empty.
    simpl_list.

    inv STATE_STEP.

    ((inv STEP_SRC; ss); []).
    (* inv SRC. *)
    inv CMDS_SRC.

    econs; eauto; [].

    ((inv STEP_TGT; ss); []).
    (* inv TGT. *)
    inv CMDS_TGT.
    ss.
    clear MAYDIFF.

    inv SRC.
    clear H H2.
    clear MEM_STEP.
    clear CONF.
    (* inv TGT. clear LESSDEF0 NOALIAS0 UNIQUE0 PRIVATE0 WF_LOCAL0. *)
    unfold alloc_private, alloc_private_unary in *. ss.
    destruct ALLOC_PRIVATE as [ALLOC_PRIVATE _].
    econs; eauto; [|]; clear LESSDEF NOALIAS WF_LOCAL.
    +
      clear ALLOC_PRIVATE.
      clear PRIVATE.
      unfold Invariant.update_src. ss.
      intros ____id____ IN.
      eapply AtomSetFacts.add_iff in IN.
      des; [|eauto]; [].
      subst.
      (* TODO BELOW IS EXACTLY COPIED FROM ALLOCA/ALLOCA CASE *)
      eapply add_unique_malloc; eauto; try apply MEM; try apply STATE.
    + clear UNIQUE.
      clear MEM TGT STATE.
      unfold Invariant.update_private. ss.
      eapply add_private; eauto.
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
    clear ALLOC_PRIVATE.
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

    inv STATE_STEP.

    ((inv STEP_SRC; ss); []).
    (* inv SRC. *)
    inv CMDS_SRC.

    ((inv STEP_TGT; ss); []).
    (* inv TGT. *)
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
        clear TGT MAYDIFF.
        clear ALLOC_INJECT.
        clear Heq6 H Heq5.
        clear H2 H4.
        clear H1 H0 H6 H5.
        clear H7.
        clear CONF.
        clear MEM_STEP.
        subst EC_src.
        inv SRC.
        econs; eauto; [].
        clear LESSDEF NOALIAS PRIVATE.
        ss.
        inv MEM. clear TGT INJECT WF.
        inv STATE. clear TGT MAYDIFF.
        eapply add_unique_malloc; eauto; try apply SRC; try apply SRC0.
      - inv TGT. inv MEM. inv STATE.
        econs; eauto; []. ss.
        eapply add_unique_malloc; eauto; try apply TGT; try apply TGT0.
      -
        (* MAYDIFF *)
        inv SRC. inv TGT.
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

        (* exploit MemProps.nextblock_malloc; try apply H3; []; ii; des. *)
        (* exploit MemProps.nextblock_malloc; try apply H7; []; ii; des. *)
        exploit MemProps.malloc_result; try apply H3; []; intro MALLOC_RES1; des.
        exploit MemProps.malloc_result; try apply H7; []; intro MALLOC_RES2; des.
        rewrite MALLOC_RES1. rewrite MALLOC_RES2. (* subst, clarify ruin ordering of premisses *)

        move ALLOC_INJECT at bottom.
        unfold alloc_inject in ALLOC_INJECT.
        exploit ALLOC_INJECT; eauto; []; ii; des; clear ALLOC_INJECT.
        destruct invmem1; ss.
        unfold alloc_inject_unary in *. des. ss.
        des_lookupAL_updateAddAL.

        econs; eauto.
    }
Qed.

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
    eapply SoundBase.postcond_cmd_inject_event_Subset in Heq1.
    des. unfold is_true in Heq1.
    rewrite Heq1 in Heq3. ss.
    destruct inv0; ss.
    unfold Invariant.update_src.
    unfold Invariant.update_lessdef.
    econs; eauto; ss.
    + destruct src1; ss.
      econs; eauto; ss.
      eapply postcond_cmd_add_lessdef_Subset.
      splits; ss.
    + reflexivity.
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
    eapply SoundBase.postcond_cmd_inject_event_Subset in Heq1.
    des. unfold is_true in Heq1.
    rewrite Heq1 in Heq3. ss.
    destruct inv0; ss.
    unfold Invariant.update_src.
    unfold Invariant.update_lessdef.
    econs; eauto; ss.
    + reflexivity.
    + destruct tgt1; ss.
      econs; eauto; ss.
      eapply postcond_cmd_add_lessdef_Subset.
      splits; ss.
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
        invst0 invmem0 inv0
        evt
        (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
        (POSTCOND: Postcond.postcond_cmd_check cmd_src cmd_tgt
                                               def_src def_tgt uses_src uses_tgt inv1)
        (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem0 inv0)
        (STATE_STEP: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1 inv1)
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
        (ALLOC_INJECT: alloc_inject conf_src conf_tgt st0_src st0_tgt
                                    st1_src st1_tgt cmd_src cmd_tgt invmem1)
        (* (ALLOC_INJECT: InvMem.Rel.inject invmem1 (st0_src.(Mem).(Memory.Mem.nextblock)) = *)
        (*                Some((st0_tgt.(Mem).(Memory.Mem.nextblock)), 0)) *)
  :
  exists invst2 invmem2,
    <<STATE_STEP: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst2 invmem2
                              (Postcond.postcond_cmd_add cmd_src cmd_tgt inv1)>> /\
             <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem2>> /\
                    <<MEMLE: InvMem.Rel.le invmem1 invmem2>>.
Proof.
  unfold postcond_cmd_add.
  exploit postcond_cmd_add_inject_sound; try apply CONF;
    try apply STEP_SRC; try apply STEP_TGT; eauto; []; ii; des.
  exploit x0; eauto; ii; des; clear x0.
  exploit postcond_cmd_add_lessdef_src_sound; try apply STATE_STEP0; eauto; []; ii; des.
  exploit postcond_cmd_add_lessdef_tgt_sound; try apply STATE_STEP1; eauto; []; ii; des.
  exploit reduce_maydiff_sound; try apply STATE_STEP2; eauto; []; ii; des.
  esplits; eauto.
  reflexivity.
Qed.
