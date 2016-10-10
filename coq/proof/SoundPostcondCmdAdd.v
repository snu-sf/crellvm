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
Require Import SoundReduceMaydiff.

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

Lemma postcond_cmd_add_private_unique_sound
      conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
      conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt
      invst0 invmem0 inv0
      evt
      (POSTCOND: Postcond.postcond_cmd_check
                   cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv0)
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
  exists invmem1,
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt st1_src st1_tgt invst0 invmem1
               (Postcond.postcond_cmd_add_private_unique cmd_src cmd_tgt inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>> /\
    <<POSTCOND: Postcond.postcond_cmd_check
                  cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt
                  (Postcond.postcond_cmd_add_private_unique cmd_src cmd_tgt inv0)>>
.
Proof.
Admitted.

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

Lemma postcond_cmd_inject_event_Subset src tgt inv0 inv1
      (INJECT_EVENT: postcond_cmd_inject_event src tgt inv0)
      (SUBSET_SRC: ExprPairSet.Subset
                 (inv0.(Invariant.src).(Invariant.lessdef))
                 (inv1.(Invariant.src).(Invariant.lessdef)))
      (SUBSET_TGT: ExprPairSet.Subset
                 (inv0.(Invariant.tgt).(Invariant.lessdef))
                 (inv1.(Invariant.tgt).(Invariant.lessdef)))
  :
    <<INJECT_EVENT: postcond_cmd_inject_event src tgt inv1>>
.
Proof.
  red.
  destruct src, tgt; ss.
  -
    apply ExprPairSetFacts.exists_iff; try by solve_compat_bool.
    apply ExprPairSetFacts.exists_iff in INJECT_EVENT; try by solve_compat_bool.
    unfold ExprPairSet.Exists in *.
    des.
    esplits; eauto.
  - repeat (des_bool; des).
    clarify. repeat des_bool.
    apply andb_true_iff; splits; [auto|]. (* TODO Why des_bool does not clear this?????? *)
    admit.
Admitted.

Ltac simpl_ep_set :=
  repeat
    match goal with
    | [H: ExprPairSet.In _ (ExprPairSet.add _ _) |- _] =>
      eapply ExprPairSetFacts.add_iff in H; des; clarify
    end.

Ltac u := autounfold in *.
Hint Unfold InvState.Unary.sem_idT.
Hint Unfold Cmd.get_ids.

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
  destruct inv0.
  unfold Invariant.update_lessdef. ss.
  destruct cmd; ss; (inv NONCALL; []); (inv STATE; []); ss; ((inv STEP; ss); []);
    try (econs; eauto; []; apply lessdef_add; ss;
         rewrite ? InvState.Unary.sem_valueT_physical in *; ss;
         apply AtomSetImpl_from_list_inter_is_empty in POSTCOND_CHECK; [];
         repeat match goal with
                | [ v: value |- _ ] => destruct v
                end; u; ss; simpl_list; des_lookupAL_updateAddAL; des_ifs; fail).
  -
    econs; eauto; [].
    unfold postcond_cmd_add_lessdef. ss.
    inv CMDS.
    admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

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
    eapply postcond_cmd_inject_event_Subset in Heq1.
    des. unfold is_true in Heq1.
    rewrite Heq1 in Heq3. ss.
    ss.
    eapply postcond_cmd_add_lessdef_Subset.
    ss.
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
    eapply postcond_cmd_inject_event_Subset in Heq1.
    des. unfold is_true in Heq1.
    rewrite Heq1 in Heq3. ss.
    ss.
    eapply postcond_cmd_add_lessdef_Subset.
Qed.

Lemma postcond_cmd_add_remove_def_from_maydiff_sound
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
               (remove_def_from_maydiff cmd_src cmd_tgt inv0)>>
.
Proof.
Admitted.

Theorem postcond_cmd_add_sound
      m_src conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
      m_tgt conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt
      invst0 invmem0 inv0
      evt
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (POSTCOND: Postcond.postcond_cmd_check cmd_src cmd_tgt
                                             def_src def_tgt uses_src uses_tgt inv0)
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
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst1 invmem1
                              (Postcond.postcond_cmd_add cmd_src cmd_tgt inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  unfold postcond_cmd_add.
  exploit postcond_cmd_add_private_unique_sound; eauto; []; ii; des.
  exploit postcond_cmd_add_lessdef_src_sound; try apply STATE0; eauto; []; ii; des.
  exploit postcond_cmd_add_lessdef_tgt_sound; try apply STATE1; eauto; []; ii; des.
  exploit postcond_cmd_add_remove_def_from_maydiff_sound; try apply STATE2;
    eauto; []; ii; des.
  exploit reduce_maydiff_sound; try apply STATE3; eauto; []; ii; des.
  esplits; eauto.
Qed.
