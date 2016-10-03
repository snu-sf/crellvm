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
  destruct cmd_src; ss; try by inv NONCALL_SRC.
  - esplits; eauto; try by eapply InvMem.Rel.PreOrder_le_obligation_1.
  -
    inv STATE.
    inv SRC.
    esplits; eauto; try by eapply InvMem.Rel.PreOrder_le_obligation_1.
    instantiate (1 := invst0).
    unfold postcond_cmd_add_lessdef; ss.
    {
      econs; eauto.
      econs; eauto.
      clear TGT MAYDIFF. (* from STATE *)
      clear NOALIAS UNIQUE PRIVATE. (* from SRC *)
      ii. (* DO NOT USE econs; eauto HERE!! *)
(*
Don't use this without thinking, early binding will mess up late proof a lot,
even unable to read proof status because it shows changed type environment, like:
@{conf_src:={|
                     CurSystem := S;
                     CurTargetData := TD;
                     CurProducts := Ps;
                     Globals := gl;
                     FunTable := fs |};
           st0_src:={|
                    EC := {|
                          CurFunction := F;
                          CurBB := B;
                          CurCmds := insn_bop id0 bop0 sz0 v1 v2 :: cs;
                          Terminator := tmn;
                          Locals := lc;
                          Allocas := als |};
                    ECS := ECS0;
                    Mem := Mem0 |};
           st1_src:={|
                    EC := {|
                          CurFunction := F;
                          CurBB := B;
                          CurCmds := cs;
                          Terminator := tmn;
                          Locals := updateAddAL GenericValue lc id0 gvs3;
                          Allocas := als |};
                    ECS := ECS0;
                    Mem := Mem0 |}; evt:=events.E0;
           x:=(Expr.bop bop5 sz5 (ValueT.lift Tag.physical value1)
                 (ValueT.lift Tag.physical value2), IdT.lift Tag.physical id5)}
 *)
      destruct x; ss.
      (* unfold postcond_cmd_add_lessdef in H; ss. *)
      rename t into xxxxxxxxxxxxxxxx.
      rename t0 into yyyyyyyyyyyyyy.
      eapply ExprPairSetFacts.add_iff in H.
      (* Following gives 24 goals, inv STEP_SRC; try by (inv CMDS_SRC); []. *)
      (* Following gives 1 goal, inv STEP_SRC; try by (inv CMDS_SRC). *)
      (* Why??? *)
      (* Maybe problem with "by"? *)
      (* Ah, parsing problem... *)
      (* Following gives 1 goal as expected. inv STEP_SRC; try (by (inv CMDS_SRC)); []. *)
      des; clarify.
      +
        rename val1 into xxxxxxxxxxxxx.
        inv STEP_SRC; try (by (inv CMDS_SRC)); [].
        rename gvs3 into yyyyyyyyyyyyy.
        esplits; eauto.
        s. (* don't want to simpl other things for now *)
        instantiate (1:=yyyyyyyyyyyyy).
        ss.
        des_ifs; clarify.
        * unfold InvState.Unary.sem_idT. ss.
          rewrite lookupAL_updateAddAL_eq. ss.
        *
          idtac.
          ss.
          des_ifs; clarify.
          exploit opsem_props.OpsemProps.BOP_inversion; eauto; []; ii; des.
          rewrite InvState.Unary.sem_valueT_physical in Heq. ss.
          rewrite InvState.Unary.sem_valueT_physical in Heq0. ss.
          (* clear MEM POSTCOND LESSDEF. *)
          clear MEM LESSDEF.
          Ltac des_lookupAL_updateAddAL :=
            match goal with
            | [ H: lookupAL ?t (updateAddAL ?t _ ?idA _) ?idB = _ |- _ ] =>
              destruct (eq_atom_dec idB idA);
              [ss; clarify; rewrite lookupAL_updateAddAL_eq in H |
               ss; clarify; rewrite <- lookupAL_updateAddAL_neq in H]; ss; clarify
            end.


          unfold postcond_cmd_check in POSTCOND.
          Fail ss; des_ifs; []. (* ss. Ruins here!! Creating more matches than needed *)
          des_ifs; [].
          clear POSTCOND.
          des_bool.
          unfold Cmd.get_ids in *. ss.
          clear Heq3.

          {
            destruct value1, value2; ss; clarify.
            - repeat des_lookupAL_updateAddAL; try apply GVs.lessdef_refl.
              admit. (* Heq1 *)
              admit. (* Heq1 *)
              admit. (* Heq1 *)
            - repeat des_lookupAL_updateAddAL; try apply GVs.lessdef_refl.
              admit. (* Heq1 *)
            - repeat des_lookupAL_updateAddAL; try apply GVs.lessdef_refl.
              admit. (* Heq1 *)
            - repeat des_lookupAL_updateAddAL; try apply GVs.lessdef_refl.
          }
          (* - works without {}, but indentation gets fucked up *)
      +
        eapply ExprPairSetFacts.add_iff in H.
        des; clarify.
        * admit.
        * apply LESSDEF in H. clear LESSDEF.
          exploit H; eauto.
    }
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
