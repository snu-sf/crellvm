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
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt st1_src st1_tgt invst1 invmem1
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
  red.
  ii.
  specialize (EMPTY a).
  unfold not in EMPTY.
  apply EMPTY.
  apply AtomSetFacts.inter_iff; ss.
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
  generalize dependent l2.
  induction l1; ii; ss.
  apply AtomSetFacts.is_empty_iff in INTER_EMPTY.
  specialize (IHl1 l2).
  rewrite <- AtomSetFacts.is_empty_iff in IHl1.
  exploit IHl1.
  { ii. specialize (INTER_EMPTY a0).
    eapply AtomSetFacts.inter_s_m_Proper in H; eauto.
    - ii.
      unfold AtomSetImpl.Subset.
      apply_all_once AtomSetFacts.mem_iff.
      apply AtomSetFacts.mem_iff.
      apply_all_once AtomSetImpl_from_list_spec.
      apply AtomSetImpl_from_list_spec.
      ss. right; ss.
    - ii. ss.
  }
  ii. econs; ss.
  clear x. clear IHl1.
  {
    apply AtomSetImpl_inter_empty with (a:=a) in INTER_EMPTY; cycle 1.
    {
      apply AtomSetFacts.mem_iff.
      apply AtomSetImpl_from_list_spec.
      econs; ss.
    }
    clear l1.
    red in INTER_EMPTY.
    apply AtomSetFacts.not_mem_iff in INTER_EMPTY.
    assert(~ In a l2).
    {
      unfold not. i.
      apply AtomSetImpl_from_list_spec in H.
      rewrite INTER_EMPTY in H. ss.
    }
    apply Forall_forall.
    ii. clarify.
  }
Qed.

Ltac simpl_list :=
  repeat match goal with
         | [ H: Forall _ (_ :: _) |- _ ] => inv H
         | [ H: Forall _ [] |- _ ] => clear H
         end.

Ltac des_lookupAL_updateAddAL :=
  repeat match goal with
         | [ H: lookupAL ?t (updateAddAL ?t _ ?idA _) ?idB = _ |- _ ] =>
           destruct (eq_atom_dec idB idA);
           [ss; clarify; rewrite lookupAL_updateAddAL_eq in H |
            ss; clarify; rewrite <- lookupAL_updateAddAL_neq in H]; ss; clarify
         end.

Lemma postcond_cmd_add_lessdef_src_sound
      conf_src st0_src st1_src cmd_src cmds_src def_src uses_src
      conf_tgt st1_tgt cmd_tgt def_tgt uses_tgt
      (* conf_tgt st0_tgt st1_tgt cmd_tgt cmds_tgt def_tgt uses_tgt *)
      invst0 invmem0 inv0
      evt
      (POSTCOND: Postcond.postcond_cmd_check
                   cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt inv0)
      (STATE: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem0)
      (STEP_SRC: sInsn conf_src st0_src st1_src evt)
      (* (STEP_TGT: sInsn conf_tgt st0_tgt st1_tgt evt) *)
      (CMDS_SRC: st0_src.(EC).(CurCmds) = cmd_src :: cmds_src)
      (* (CMDS_TGT: st0_tgt.(EC).(CurCmds) = cmd_tgt :: cmds_tgt) *)
      (NONCALL_SRC: Instruction.isCallInst cmd_src = false)
      (* (NONCALL_TGT: Instruction.isCallInst cmd_tgt = false) *)
      (DEF_SRC: def_src = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_src)))
      (* (DEF_TGT: def_tgt = AtomSetImpl_from_list (option_to_list (Cmd.get_def cmd_tgt))) *)
      (USES_SRC: uses_src = AtomSetImpl_from_list (Cmd.get_ids cmd_src))
      (* (USES_TGT: uses_tgt = AtomSetImpl_from_list (Cmd.get_ids cmd_tgt)): *)
      :
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt st1_src st1_tgt invst1 invmem1
               (Invariant.update_src
                  (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd_src)) inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>> /\
    <<POSTCOND: Postcond.postcond_cmd_check
                  cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt
                  (Invariant.update_src
                     (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd_src)) inv0)>>
.
Proof.
  (* unfold postcond_cmd_add_lessdef in *. *)
  destruct inv0, src.
  unfold Invariant.update_src. ss.
  unfold Invariant.update_lessdef. ss.

  Time destruct cmd_src; ss; try by inv NONCALL_SRC.
  (* Finished transaction in 22.738 secs (22.705u,0.045s) (successful) *)
  - esplits; eauto; try by eapply InvMem.Rel.PreOrder_le_obligation_1.
  -
    inv STATE.
    inv SRC.
    esplits; eauto; try by eapply InvMem.Rel.PreOrder_le_obligation_1.
    instantiate (1 := invst0).
    unfold postcond_cmd_add_lessdef; ss.

    econs; eauto. ss.
    econs; eauto. ss.
    clear TGT MAYDIFF. (* from STATE *)
    clear NOALIAS UNIQUE PRIVATE. (* from SRC *)
    ii. (* DO NOT USE econs; eauto HERE!! early binding will mess up late proof a lot, *)
    destruct x; ss.
    (* unfold postcond_cmd_add_lessdef in H; ss. *)

    unfold postcond_cmd_check in POSTCOND; des_ifs; []. clear POSTCOND.
    des_bool.
    ss. clear Heq1.
    (* unfold Cmd.get_ids in Heq. *) (* unfolding here will ruin later des_ifs... *)
    (* unfold Cmd.get_values in Heq. *)
    apply AtomSetImpl_from_list_inter_is_empty in Heq.
    ss.

    eapply ExprPairSetFacts.add_iff in H.
    des; clarify.
    +
      {
        inv STEP_SRC; try (by (inv CMDS_SRC)); [].
        exists gvs3.
        ss. des_ifs; clarify; [].
        exploit opsem_props.OpsemProps.BOP_inversion; eauto; []; ii; des.
        esplits; eauto.
        * unfold InvState.Unary.sem_idT. ss.
          rewrite lookupAL_updateAddAL_eq. ss.
        * rewrite InvState.Unary.sem_valueT_physical in *. ss.
          clear MEM LESSDEF.
          unfold Cmd.get_ids in *. ss.
          destruct value1, value2; ss; clarify;
            repeat simpl_list;
            repeat des_lookupAL_updateAddAL; try apply GVs.lessdef_refl.
      }
    +
      eapply ExprPairSetFacts.add_iff in H.
      des; clarify.
      *
        {
          clear MEM LESSDEF.
          inv STEP_SRC; try (by (inv CMDS_SRC)); [].
          exists gvs3.
          simpl in CMDS_SRC. inv CMDS_SRC.
          exploit opsem_props.OpsemProps.BOP_inversion; eauto; []; ii; des.
          unfold Cmd.get_ids in *. (* WHY JUST SIMPL DOES NOT WORK??????????? *)
          destruct value1, value2; ss; clarify;
            simpl_list; unfold InvState.Unary.sem_idT; ss;
            des_ifs; des_lookupAL_updateAddAL.
          (* WHY SHOULD I unfold InvState.Unary.sem_idT MANUALLY ??????????? *)
          - esplits; eauto.
            unfold InvState.Unary.sem_idT in *. ss. (* WHY JOST ss or simpl does not work?? *)
            des_ifs; des_lookupAL_updateAddAL.
            apply GVs.lessdef_refl.
          - esplits; eauto.
            unfold InvState.Unary.sem_idT in *. ss. (* WHY JOST ss or simpl does not work?? *)
            des_ifs; des_lookupAL_updateAddAL.
            apply GVs.lessdef_refl.
          - esplits; eauto.
            unfold InvState.Unary.sem_idT in *. ss. (* WHY JOST ss or simpl does not work?? *)
            des_ifs; des_lookupAL_updateAddAL.
            apply GVs.lessdef_refl.
          - esplits; eauto.
            unfold InvState.Unary.sem_idT in *. ss. (* WHY JOST ss or simpl does not work?? *)
            des_ifs; des_lookupAL_updateAddAL.
            apply GVs.lessdef_refl.
        }
      * apply LESSDEF in H. clear LESSDEF.
        exploit H; eauto.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

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
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt st1_src st1_tgt invst1 invmem1
               (Invariant.update_tgt
                  (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd_tgt)) inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>> /\
    <<POSTCOND: Postcond.postcond_cmd_check
                  cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt
                  (Invariant.update_tgt
                     (Invariant.update_lessdef (postcond_cmd_add_lessdef cmd_tgt)) inv0)>>
.
Proof.
Admitted.

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
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt st1_src st1_tgt invst1 invmem1
               (remove_def_from_maydiff cmd_src cmd_tgt inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st1_src.(Mem) st1_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>> /\
    <<POSTCOND: Postcond.postcond_cmd_check cmd_src cmd_tgt def_src def_tgt uses_src uses_tgt
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
  (* guard. *)
  exploit postcond_cmd_add_lessdef_src_sound; try apply STATE0; eauto; []; ii; des.
  exploit postcond_cmd_add_lessdef_tgt_sound; try apply STATE1; eauto; []; ii; des.
  exploit postcond_cmd_add_remove_def_from_maydiff_sound; try apply STATE2;
    eauto; []; ii; des.
  exploit reduce_maydiff_sound; try apply STATE3; eauto; []; ii; des.
  esplits; eauto.
  do 3 (eapply InvMem.Rel.PreOrder_le_obligation_2; eauto).
Qed.
