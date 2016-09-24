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
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.
Require Import SoundSnapshot.
Require Import SoundForget.
Require Import SoundReduceMaydiff.
Require Import SoundImplies.

Set Implicit Arguments.


Lemma add_terminator_cond_br_uncond
      inv bid_src bid_tgt l:
  Postcond.add_terminator_cond
    inv
    (insn_br_uncond bid_src l)
    (insn_br_uncond bid_tgt l)
    l =
  inv.
Proof. destruct inv, src, tgt. ss. Qed.

Lemma add_terminator_cond_switch
      inv bid_src bid_tgt ty val_src val_tgt l0 cls l:
  Postcond.add_terminator_cond
    inv
    (insn_switch bid_src ty val_src l0 cls)
    (insn_switch bid_tgt ty val_tgt l0 cls)
    l =
  inv.
Proof. destruct inv, src, tgt. ss. Qed.

Lemma add_terminator_cond_br
      conf_src conf_tgt
      st_src st_tgt
      invst invmem inv
      decision l1 l2
      id_src val_src gval_src
      id_tgt val_tgt gval_tgt
      (STATE: InvState.Rel.sem
                conf_src conf_tgt st_src st_tgt
                invst invmem inv)
      (VAL_SRC: getOperandValue
                  conf_src.(CurTargetData)
                  val_src
                  st_src.(EC).(Locals)
                  conf_src.(Globals) = Some gval_src)
      (VAL_TGT: getOperandValue
                  conf_tgt.(CurTargetData)
                  val_tgt
                  st_tgt.(EC).(Locals)
                  conf_tgt.(Globals) = Some gval_tgt)
      (DECIDE_SRC: decide_nonzero conf_src.(CurTargetData) gval_src decision)
      (DECIDE_TGT: decide_nonzero conf_tgt.(CurTargetData) gval_tgt decision):
  InvState.Rel.sem
    conf_src conf_tgt
    st_src st_tgt
    invst invmem
    (Postcond.add_terminator_cond
       inv
       (insn_br id_src val_src l1 l2)
       (insn_br id_tgt val_tgt l1 l2) (ite decision l1 l2)).
Proof.
Admitted.

Lemma get_lessdef_spec
      ep assigns
      (IN: ExprPairSet.In ep (Postcond.Phinode.get_lessdef assigns)):
  exists phix phiv phity,
    <<IN: In (Postcond.Phinode.assign_intro phix phity phiv) assigns>> /\
    __guard__
      (<<PAIR1: ep = (Expr.value (ValueT.id (Tag.physical, phix)),
                      Expr.value (ValueT.lift Tag.previous phiv))>> \/
       <<PAIR2: ep = (Expr.value (ValueT.lift Tag.previous phiv),
                      Expr.value (ValueT.id (Tag.physical, phix)))>>).
Proof.
  cut
    (exists phix phiv phity,
        <<IN: In (Postcond.Phinode.assign_intro phix phity phiv) (rev assigns)>> /\
        __guard__
          (<<PAIR1: ep = (Expr.value (ValueT.id (Tag.physical, phix)),
                          Expr.value (ValueT.lift Tag.previous phiv))>> \/
           <<PAIR2: ep = (Expr.value (ValueT.lift Tag.previous phiv),
                          Expr.value (ValueT.id (Tag.physical, phix)))>>)).
  { i. des. esplits; eauto. apply in_rev. eauto. }
  unfold Postcond.Phinode.get_lessdef in IN.
  rewrite <- fold_left_rev_right, <- map_rev in IN.
  induction (rev assigns); ss.
  { apply ExprPairSetFacts.empty_iff in IN. done. }
  destruct a. ss.
  repeat rewrite -> ExprPairSetFacts.add_iff in IN. des.
  - esplits; eauto. left. eauto.
  - esplits; eauto. right. eauto.
  - exploit IHl0; eauto. i. des. esplits; eauto.
Qed.

Lemma phinode_assign_sound
      conf phinodes b assigns
      locals locals'
      x ty v
      (ASSIGNS: forallb_map (Postcond.Phinode.resolve (fst b)) phinodes = Some assigns)
      (LOCALS': getIncomingValuesForBlockFromPHINodes
                  conf.(CurTargetData) phinodes b conf.(Globals) locals = Some locals')
      (UNIQUE_PHI: unique id_dec (List.map Postcond.Phinode.get_def assigns) = true)
      (ASSIGN_IN: In (Postcond.Phinode.assign_intro x ty v) assigns)
  : exists gv,
    <<VAL_V: getOperandValue conf.(CurTargetData) v locals conf.(Globals) = Some gv>> /\
    <<VAL_X: getOperandValue conf.(CurTargetData) (value_id x) locals' conf.(Globals) = Some gv>>.
Proof.
  revert_until b. induction phinodes; i; ss.
  { inv ASSIGNS. ss. }
  simtac. des.
  - inv ASSIGN_IN.
    assert (EQV: v = v0).
    { match goal with
      | [H1: getValueViaBlockFromValuels _ _ = Some v0,
         H2: lookupAL _ _ _ = Some v |- _] => clear -H1 H2
      end.
      unfold getValueViaBlockFromValuels in *.
      induction l0; ss; simtac.
      eapply IHl0; eauto.
    }
    subst. esplits; eauto.
    match goal with
    | [H:_ |- (if ?c then _ else _) = _ ] => destruct c; try done
    end.
  - exploit IHphinodes; eauto. i. des.
    esplits; eauto.
    fold id. destruct (x == id5); ss. subst.
    destruct (in_dec id_dec id5 (List.map Postcond.Phinode.get_def l2)); ss. contradict n.
    replace id5 with (Postcond.Phinode.get_def (Postcond.Phinode.assign_intro id5 ty v)); eauto.
    apply In_map; eauto.
Qed.

Lemma phinodes_add_lessdef_sound
      conf st0 st1
      l_to phinodes cmds terminator
      invst invmem inv0
      assigns
      (STEP: switchToNewBasicBlock conf.(CurTargetData)
                                   (l_to, stmts_intro phinodes cmds terminator)
                                   st0.(EC).(CurBB)
                                   conf.(Globals)
                                   st0.(EC).(Locals) = Some st1.(EC).(Locals))
      (ASSIGNS: forallb_map (Postcond.Phinode.resolve st0.(EC).(CurBB).(fst)) phinodes = Some assigns)
      (UNIQUE_PHI: unique id_dec (List.map Postcond.Phinode.get_def assigns) = true)
      (STATE: InvState.Unary.sem conf st1 invst invmem inv0)
      (PREV: forall x, InvState.Unary.sem_idT st0 invst (Tag.previous, x) =
                          lookupAL _ st0.(EC).(Locals) x)
  : InvState.Unary.sem
      conf st1 invst invmem
      (Hints.Invariant.update_lessdef (Postcond.postcond_phinodes_add_lessdef assigns) inv0).
Proof.
  econs; try by inv STATE.
  s. ii. apply ExprPairSet.union_1 in H.  des.
  { eapply STATE; eauto. }
  exploit get_lessdef_spec; eauto. i. des.
  esplits; [|reflexivity].
  unfold switchToNewBasicBlock in *.
  solve_match_bool. inv STEP. ss.
  destruct (CurBB (EC st0)). ss. des_ifs.
  exploit phinode_assign_sound; eauto; ss. i. des. ss.
  exploit opsem_props.OpsemProps.updateValuesForNewBlock_spec4; eauto.
  match goal with
  | [H: updateValuesForNewBlock _ _ = _ |- _] => rewrite H; i
  end.
  unguardH x0. des; subst; ss.
  - assert (GV_VAL1: gv = val1).
    { unfold InvState.Unary.sem_idT in VAL1. ss. congruence. }
    subst.
    unfold getOperandValue in VAL_V.
    destruct phiv; eauto.
    rewrite <- PREV in VAL_V. ss.
  - assert (GV_VAL1: gv = val1).
    { destruct phiv; ss.
      - rewrite <- PREV in VAL_V.
        unfold InvState.Unary.sem_idT in *. ss. congruence.
      - congruence.
    }
    subst. eauto.
Qed.

Lemma phinodes_progress_getPhiNodeID_safe
      TD phinodes b gl locals locals' id assigns
      (GETINC: getIncomingValuesForBlockFromPHINodes TD phinodes b
                                                     gl locals = Some locals')
      (IN: In id (List.map getPhiNodeID phinodes))
      (RESOLVE : forallb_map (Postcond.Phinode.resolve (fst b)) phinodes = Some assigns)
  :
    <<IN: In id (List.map Postcond.Phinode.get_def assigns)>>.
Proof.
  revert_until gl. induction phinodes; ss. i. simtac.
  des; auto. exploit IHphinodes; eauto.
Qed.

Lemma locals_equiv_after_phinode
      conf l_to phinodes cmds tmn b assigns
      locals locals'
      (SWITCH: switchToNewBasicBlock conf.(CurTargetData)
                                     (l_to, stmts_intro phinodes cmds tmn)
                                     b conf.(Globals) locals = Some locals')
      (RESOLVE: forallb_map (Postcond.Phinode.resolve b.(fst)) phinodes = Some assigns)
  :
    <<EQUIV: locals_equiv_except (AtomSetImpl_from_list (List.map Postcond.Phinode.get_def assigns))
                                 locals locals'>>.
Proof.
  ii. unfold switchToNewBasicBlock in SWITCH. simtac.
  apply opsem_props.OpsemProps.updateValuesForNewBlock_spec5; ss.
  destruct (in_dec id_dec id0 (List.map getPhiNodeID phinodes)).
  - exploit phinodes_progress_getPhiNodeID_safe; eauto. i. des.
    contradict NOT_MEM. unfold not.
    admit.
    (* apply eq_true_false_abs, AtomSetImpl_from_list_spec, In_map. eauto. *)
  - hexploit opsem_props.OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8; eauto. i.
    exploit notin_lookupAL_None; eauto.
Admitted.

Lemma IdTSet_from_list_spec':
  forall ids id0, IdTSet.mem id0 (IdTSet_from_list ids) = false <-> ~ In id0 ids.
Proof.
  split; i.
  - ii. apply IdTSet_from_list_spec in H0. congruence.
  - apply not_true_iff_false. ii.
    apply IdTSet_from_list_spec in H0. eauto.
Qed.

Lemma postcond_phinodes_sound
      m_src conf_src st0_src phinodes_src cmds_src terminator_src locals_src
      m_tgt conf_tgt st0_tgt phinodes_tgt cmds_tgt terminator_tgt locals_tgt
      invst0 invmem inv0 inv1
      l_from l_to
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (CMD_SRC: st0_src.(EC).(CurCmds) = [])
      (CMD_TGT: st0_tgt.(EC).(CurCmds) = [])
      (L_SRC: st0_src.(EC).(CurBB).(fst) = l_from)
      (L_TGT: st0_tgt.(EC).(CurBB).(fst) = l_from)
      (STMT_SRC: lookupAL stmts st0_src.(EC).(CurFunction).(get_blocks) l_to =
                 Some (stmts_intro phinodes_src cmds_src terminator_src))
      (STMT_TGT: lookupAL stmts st0_tgt.(EC).(CurFunction).(get_blocks) l_to =
                 Some (stmts_intro phinodes_tgt cmds_tgt terminator_tgt))
      (POSTCOND: Postcond.postcond_phinodes l_from phinodes_src phinodes_tgt inv0 = Some inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem)
      (STEP_SRC: switchToNewBasicBlock
                   conf_src.(CurTargetData)
                   (l_to, stmts_intro phinodes_src cmds_src terminator_src)
                   st0_src.(EC).(CurBB)
                   conf_src.(Globals)
                   st0_src.(EC).(Locals)
                 = Some locals_src)
      (STEP_TGT: switchToNewBasicBlock
                   conf_tgt.(CurTargetData)
                   (l_to, stmts_intro phinodes_tgt cmds_tgt terminator_tgt)
                   st0_tgt.(EC).(CurBB)
                   conf_tgt.(Globals)
                   st0_tgt.(EC).(Locals)
                 = Some locals_tgt):
  exists invst1,
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt
               (mkState
                  (mkEC
                     st0_src.(EC).(CurFunction)
                     (l_to, stmts_intro phinodes_src cmds_src terminator_src)
                     cmds_src
                     terminator_src
                     locals_src
                     st0_src.(EC).(Allocas))
                  st0_src.(ECS)
                  st0_src.(Mem))
               (mkState
                  (mkEC
                     st0_tgt.(EC).(CurFunction)
                     (l_to, stmts_intro phinodes_tgt cmds_tgt terminator_tgt)
                     cmds_tgt
                     terminator_tgt
                     locals_tgt
                     st0_tgt.(EC).(Allocas))
                  st0_tgt.(ECS)
                  st0_tgt.(Mem))
               invst1 invmem inv1>>.
Proof.
  unfold Postcond.postcond_phinodes in *.
  unfold Postcond.postcond_phinodes_assigns in *.
  simtac.
  exploit snapshot_sound; eauto. i. des.
  exploit forget_sound; eauto.
(*   exploit forget_sound; eauto. *)
  { instantiate (1 := mkState (mkEC _ _ _ _ _ _) _ _). econs; s; eauto.
    eapply locals_equiv_after_phinode; eauto.
  }
  { instantiate (1 := mkState (mkEC _ _ _ _ _ _) _ _). econs; s; eauto.
    eapply locals_equiv_after_phinode; eauto.
    rewrite L_TGT. eauto.
  }
  { instantiate (1 := AtomSetImpl_from_list ((filter_map Postcond.Phinode.get_use l0))).
    ii.
    inv STATE0.
    inv SRC.
    exploit UNIQUE; eauto.
    { apply AtomSetFacts.mem_iff; eauto. }
    i.
    admit.
    (* apply IdTSet_from_list_spec in MEM_X. *)
    (* apply IdTSet_from_list_spec' in UNIQUE_NO_USE. *)
    
    (* contradict  *)
    
    (* Set Printing All. idtac. *)
    
    (* eapply eq_true_false_abs in UNIQUE_NO_USE. *)
    (* bool *)
    (* apply IdTSet_from_list_spec in UNIQUE_NO_USE. *)
    (* IdTSetFacts.mem_ *)
    

    (* unfold unique_preserved_except. *)
  }
  { admit. }
  i. des. inversion x0.
  exploit phinodes_add_lessdef_sound; try exact SRC; eauto; i.
  exploit phinodes_add_lessdef_sound; try exact TGT; eauto; i.
  { rewrite L_TGT. eauto. }
  exploit reduce_maydiff_sound; swap 1 2.
  { instantiate (1 := Hints.Invariant.mk _ _ _). econs; eauto. }
  { eauto. }
  { eauto. }
  { i. match goal with [H:exists _, _ |- _] => exact H end.
Admitted.
