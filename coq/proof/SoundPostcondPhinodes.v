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
Require Import Postcond.
Require Import Hints.
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.
Require Import SoundSnapshot.
Require Import SoundForgetStack.
Require Import SoundReduceMaydiff.
Require Import SoundImplies.
Require Import TODOProof.
Require Import OpsemAux.
Require Import MemAux.

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

Lemma add_terminator_cond_switch_unary
      conf val st gmax public
      ty gval cases l_dflt l_dest id
      invst invmem inv
      (VAL : getOperandValue (CurTargetData conf) val
                             (Locals (EC st)) (Globals conf) = Some gval)
      (DECIDE : get_switch_branch (CurTargetData conf)
                                  ty gval cases l_dflt = Some l_dest)
      (STATE : InvState.Unary.sem conf st invst invmem gmax public inv)
  : InvState.Unary.sem conf st invst invmem gmax public
                       (Invariant.update_lessdef
                          (add_terminator_cond_lessdef
                             (insn_switch id ty val l_dflt cases) l_dest) inv).
Proof.
  inv STATE.
  econs; eauto. ss. ii.
  des_ifs; try by eapply LESSDEF; eauto.
  destruct p as [const_case l_case]. ss.
  rename Heq into FILTER_CASES.

  assert (CASE_AUX: In (const_case, l_case)
                       (List.filter (fun cl : const * l => l_dec l_dest (snd cl)) cases)).
  { rewrite FILTER_CASES. unfold In. eauto. }

  assert (CASE_IN: In (const_case, l_case) cases).
  { apply filter_In in CASE_AUX. des. eauto. }

  assert (CASE_UNIQUE: forall cl, In cl cases -> l_dec l_dest (snd cl) ->
                             cl = (const_case, l_case)).
  { i.
    cut (In cl [(const_case, l_case)]).
    { intro IN. inv IN; eauto. contradiction. }
    rewrite <- FILTER_CASES.
    apply filter_In. split; eauto.
  }
  (* gv_chunks_match_typ *)

  unfold get_switch_branch in DECIDE. des_ifs.
  unfold get_switch_branch_aux in *. des_ifs.
  exploit find_some; eauto. i. des. des_ifs. ss.
  exploit CASE_UNIQUE; eauto.
  { ss. destruct (l_dec l0 l0); ss. }
  i. clarify.
  specialize (Fcore_Zaux.Zeq_bool_spec z0 z).
  intro ZEQ. inv ZEQ; try congruence.
  destruct x as [e1 e2].

  do 2 rewrite ExprPairSetFacts.add_iff in *. des.
  - ss. clarify. ss.
    solve_leibniz. clarify. ss.
    rewrite InvState.Unary.sem_valueT_physical in VAL1. clarify.

    unfold intConst2Z in *. des_ifs.

    esplits; eauto.
    + unfold const2GV. ss.
    + ss.
      unfold GV2int in *. des_ifs.
      unfold val2GV.
      econs; try by apply list_forall2_nil.
      split; ss.
      { rewrite <- H1.
        rewrite <- e.
        replace (n0+1-1)%nat with n0; try omega.
        rewrite Integers.Int.repr_signed. eauto.
      }
      { esplits; eauto.
        - rewrite <- e.
          replace (n0+1-1)%nat with n0; try omega.
          ss.
        - chunk_simpl.
      }
  - ss. clarify. ss.
    solve_leibniz. clarify. ss.
    rewrite InvState.Unary.sem_valueT_physical. clarify.

    unfold intConst2Z in *. des_ifs.

    esplits; eauto.
    unfold const2GV in *. ss. clarify.
    unfold GV2int in *. des_ifs.
    econs; try by apply list_forall2_nil.
    ss. split.
    { rewrite <- H1.
      rewrite <- e.
      replace (n0+1-1)%nat with n0; try omega.
      rewrite Integers.Int.repr_signed. eauto.
    }
    { esplits; eauto.
      - rewrite <- e. replace (n0+1-1)%nat with n0; try omega. ss.
      - chunk_simpl.
    }
  - apply LESSDEF; eauto.
Qed.

Lemma add_terminator_cond_switch
      conf_src conf_tgt
      st_src st_tgt
      invst invmem inv
      ty cases l_dflt l_dest
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
      (DECIDE_SRC: get_switch_branch conf_src.(CurTargetData) ty gval_src cases l_dflt = Some l_dest)
      (DECIDE_TGT: get_switch_branch conf_tgt.(CurTargetData) ty gval_tgt cases l_dflt = Some l_dest)
  : InvState.Rel.sem
      conf_src conf_tgt
      st_src st_tgt
      invst invmem
      (Postcond.add_terminator_cond
         inv
         (insn_switch id_src ty val_src l_dflt cases)
         (insn_switch id_tgt ty val_tgt l_dflt cases) l_dest).
Proof.
  inv STATE.
  econs; eauto; ss.
  - eapply add_terminator_cond_switch_unary; eauto.
  - eapply add_terminator_cond_switch_unary; eauto.
Qed.

Lemma int_sizezero_cases_aux
      (i : Integers.Int.int 0)
  : (Integers.Int.eq 0 i (Integers.Int.zero 0) = true) \/
    (Integers.Int.eq 0 i (Integers.Int.one 0) = true).
Proof.
  destruct i. destruct intval.
  - left. ss.
  - unfold Integers.Int.modulus, two_power_nat in intrange. ss.
    destruct p.
    + specialize (Pos2Z.inj_xI p). i.
      specialize (Zgt_pos_0 p). i. omega.
    + specialize (Pos2Z.inj_xO p). i.
      specialize (Zgt_pos_0 p). i. omega.
    + right. ss.
  - specialize (Zlt_neg_0 p). i. omega.
Qed.

Lemma int_sizezero_cases
      (i : Integers.Int.int 0)
  : (i = (Integers.Int.zero 0)) \/
    (i = (Integers.Int.one 0)).
Proof.
  specialize (int_sizezero_cases_aux i). i. des.
  - left.
    exploit Integers.Int.eq_spec. i.
    rewrite H in *. eauto.
  - right.
    exploit Integers.Int.eq_spec. i.
    rewrite H in *. eauto.
Qed.

Lemma add_terminator_cond_br_unary
      conf val st gval decision
      invst invmem inv gmax public
      id l1 l2
      (VAL : getOperandValue (CurTargetData conf) val 
                             (Locals (EC st)) (Globals conf) = Some gval)
      (DECIDE : decide_nonzero (CurTargetData conf) gval decision)
      (STATE : InvState.Unary.sem conf st invst invmem gmax public inv)
  : InvState.Unary.sem conf st invst invmem gmax public
                       (Invariant.update_lessdef
                          (add_terminator_cond_lessdef (insn_br id val l1 l2)
                                                       (ite decision l1 l2))
                          inv).
Proof.
  inv STATE.
  econs; eauto.
  ii. unfold add_terminator_cond_lessdef in *. ss.
  destruct (l_dec l1 l2).
  { eapply LESSDEF; eauto. }
  inv DECIDE.

  destruct x as [e1 e2]. ss.

  do 2 rewrite ExprPairSetFacts.add_iff in *.
  des.
  - clarify. ss.
    solve_leibniz. clarify. ss.
    rewrite InvState.Unary.sem_valueT_physical in VAL1.
    unfold ite in *.
    unfold GV2int in INT.
    unfold Size.to_nat, Size.One in *.
    des_ifs; ss.
    + rename n0 into wz.
      esplits; ss. ss.
      destruct wz; try omega.
      specialize (int_sizezero_cases i0). i.
      unfold val2GV. ss. econs; ss; cycle 1.
      { apply list_forall2_nil. }
      econs; eauto.
      { (* value *)
        des; subst; unfold Integers.Int.repr; ss. }
      { split; ss. }
    +  esplits; ss. ss.
       rename n1 into wz.
       destruct wz; try omega.
       specialize (int_sizezero_cases i0). i.
       unfold val2GV. ss. econs; ss; cycle 1.
       { apply list_forall2_nil. }
       econs; eauto.
       { (* value *)
         des; subst; unfold Integers.Int.repr; ss. }
       { split; ss. }
  - clarify. ss.
    solve_leibniz. clarify. ss.
    rewrite InvState.Unary.sem_valueT_physical.
    unfold ite in *.
    unfold GV2int in INT.
    unfold Size.to_nat, Size.One in *.
    des_ifs; ss.
    + esplits; ss; eauto.
      rename n0 into wz.
      destruct wz; try omega.
      specialize (int_sizezero_cases i0). i.
      unfold const2GV in *. des_ifs. ss. clarify. ss.
      
      unfold val2GV.
      
      econs; ss; cycle 1.
      { apply list_forall2_nil. }
      econs; eauto.
      { (* value *)
        des; subst; unfold Integers.Int.repr; ss. }
      { ss. }
    + esplits; ss; eauto.
      rename n0 into wz.
      destruct wz; try omega.
      specialize (int_sizezero_cases i0). i.
      unfold const2GV in *. des_ifs. ss. clarify. ss.
      
      unfold val2GV.
      
      econs; ss; cycle 1.
      { apply list_forall2_nil. }
      econs; eauto.
      { (* value *)
        des; subst; unfold Integers.Int.repr; ss. }
      { ss. }
  - exploit LESSDEF; eauto.
Qed.

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
  inv STATE.
  econs; eauto; ss.
  - eapply add_terminator_cond_br_unary; eauto.
  - eapply add_terminator_cond_br_unary; eauto.
Qed.

Lemma get_lessdef_spec
      ep assigns
      (IN: ExprPairSet.In ep (Postcond.Phinode.get_lessdef assigns)):
  exists phix phiv phity,
    <<IN: In (Postcond.Phinode.assign_intro phix phity phiv) assigns>> /\
    __guard__
      (<<DEFINEDNESS: ep = (Expr.value (ValueT.const (const_undef phity)),
                            Expr.value (ValueT.id (Tag.physical, phix)))>> \/
       <<PAIR1: ep = (Expr.value (ValueT.id (Tag.physical, phix)),
                      Expr.value (ValueT.lift Tag.previous phiv))>> \/
       <<PAIR2: ep = (Expr.value (ValueT.lift Tag.previous phiv),
                      Expr.value (ValueT.id (Tag.physical, phix)))>>).
Proof.
  cut
    (exists phix phiv phity,
        <<IN: In (Postcond.Phinode.assign_intro phix phity phiv) (rev assigns)>> /\
        __guard__
          (<<DEFINEDNESS: ep = (Expr.value (ValueT.const (const_undef phity)),
                            Expr.value (ValueT.id (Tag.physical, phix)))>> \/
           <<PAIR1: ep = (Expr.value (ValueT.id (Tag.physical, phix)),
                          Expr.value (ValueT.lift Tag.previous phiv))>> \/
           <<PAIR2: ep = (Expr.value (ValueT.lift Tag.previous phiv),
                          Expr.value (ValueT.id (Tag.physical, phix)))>>)).
  { i. des. esplits; eauto. apply in_rev. eauto. }
  unfold Postcond.Phinode.get_lessdef in IN.
  rewrite <- fold_left_rev_right in IN.
  rewrite <- fold_left_rev_right in IN.
  rewrite <- map_rev in IN.
  rewrite ExprPairSetFacts.union_iff in IN. des.
  { (* assigns *)
    induction (rev assigns); ss.
    { apply ExprPairSetFacts.empty_iff in IN. done. }
    destruct a. ss.
    repeat rewrite -> ExprPairSetFacts.add_iff in IN. des.
    - solve_leibniz.
      esplits; eauto. right. left. eauto.
    - solve_leibniz.
      esplits; eauto. right. right. eauto.
    - exploit IHl0; eauto. i. des. esplits; eauto.
  }
  { (* definedness *)
    induction (rev assigns); ss.
    { apply ExprPairSetFacts.empty_iff in IN. done. }
    destruct a. ss.
    repeat rewrite -> ExprPairSetFacts.add_iff in IN. des.
    - solve_leibniz. esplits; eauto. left. eauto.
    - exploit IHl0; eauto. i. des. esplits; eauto.
  }
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

Lemma gv_chunks_match_typb_aux_implies_chunk_eq
      gv mcs
      (CHUNK: gv_chunks_match_typb_aux gv mcs)
  :
    <<CHUNK_EQ: List.map snd gv = mcs>>
.
Proof.
  exploit gv_chunks_match_typb_aux__gv_chunks_match_typ; eauto. i; des.
  exploit vm_matches_typ__eq__snd; eauto. i. clarify.
  rewrite util.snd_split__map_snd. ss.
Qed.

Lemma incomingPHINodes_lookup_chunk
      TD phinodes blk gl ls idgs
      (PHI: getIncomingValuesForBlockFromPHINodes TD phinodes blk gl ls = Some idgs)
      phix phity phiv assigns
      (ASSIGNS: In (Phinode.assign_intro phix phity phiv) assigns)
      gv
      (LOOKUP: lookupAL GenericValue idgs phix = Some gv)
      (RESOLVE: forallb_map (Phinode.resolve blk.(fst)) phinodes = Some assigns)
      (UNIQUE_PHI: unique id_dec (List.map Phinode.get_def assigns) = true)
      mcs
      (FLATTEN: flatten_typ TD phity = Some mcs)
  :
    <<CHUNK: gv_chunks_match_typb_aux gv mcs>>
    (* <<CHUNK: List.map snd gv = mcs>> *)
.
Proof.
  red.
  ginduction phinodes; ii; ss; clarify.
  des_ifs.
  ss.
  des_ifs_safe.
  destruct (phix == id5); ss.
  - clarify. des_ifs_safe.
    unfold gv_chunks_match_typb in *. des_ifs_safe.
    des.
    { clarify. }
    { repeat (des_bool; des; des_sumbool; clarify).
      exfalso. clear - UNIQUE_PHI ASSIGNS.
      apply UNIQUE_PHI. clear UNIQUE_PHI.
      ginduction l0; ii; ss.
      des; clarify; ss.
      - left; ss.
      - right. eapply IHl0; eauto.
    }
  - des_ifs_safe.
    repeat (des_bool; des; des_sumbool; clarify).
    { eapply IHphinodes; eauto. }
Qed.

Lemma phinodes_add_lessdef_sound
      conf st0 st1 gmax public
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
      (STATE: InvState.Unary.sem conf st1 invst invmem gmax public inv0)
      (PREV: forall x, InvState.Unary.sem_idT st0 invst (Tag.previous, x) =
                          lookupAL _ st0.(EC).(Locals) x)
  : InvState.Unary.sem
      conf st1 invst invmem gmax public
      (Hints.Invariant.update_lessdef (Postcond.postcond_phinodes_add_lessdef assigns) inv0).
Proof.
  econs; try by inv STATE.
  s. ii. apply ExprPairSet.union_1 in H.  des.
  { eapply STATE; eauto. }
  exploit get_lessdef_spec; eauto. i. des.
  unfold switchToNewBasicBlock in *.
  solve_match_bool. inv STEP. ss.
  destruct (CurBB (EC st0)). ss. des_ifs.
  exploit phinode_assign_sound; eauto; ss. i. des. ss.
  exploit opsem_props.OpsemProps.updateValuesForNewBlock_spec4; eauto.
  match goal with
  | [H: updateValuesForNewBlock _ _ = _ |- _] => rewrite H; i
  end.
  unguardH x0. des; subst; ss.
  - esplits.
    + unfold InvState.Unary.sem_idT. ss. eauto.
    + exploit const2GV_undef; eauto. i. des.
      exploit incomingPHINodes_lookup_chunk; eauto. intro CHUNK; des.
      apply all_undef_lessdef_aux; eauto.
      { rewrite x3.
        apply gv_chunks_match_typb_aux_implies_chunk_eq in CHUNK.
        rewrite <- CHUNK. ss. }
      { clear - CHUNK.
        ginduction gv; ii; ss.
        des_ifs.
        unfold is_true in *. repeat (des_bool; des; ss; clarify).
        econs; eauto.
      }
  - esplits; [|reflexivity].
    assert (GV_VAL1: gv = val1).
    { unfold InvState.Unary.sem_idT in VAL1. ss. congruence. }
    subst.
    unfold getOperandValue in VAL_V.
    destruct phiv; eauto.
    rewrite <- PREV in VAL_V. ss.
  - esplits; [|reflexivity].
    assert (GV_VAL1: gv = val1).
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
    apply eq_true_false_abs, AtomSetImpl_from_list_spec. eauto.
  - hexploit opsem_props.OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8; eauto. i.
    exploit notin_lookupAL_None; eauto.
Qed.

Lemma IdTSet_from_list_spec':
  forall ids id0, IdTSet.mem id0 (IdTSetFacts.from_list ids) = false <-> ~ In id0 ids.
Proof.
  split; i.
  - ii. apply IdTSet_from_list_spec in H0. congruence.
  - apply not_true_iff_false. ii.
    apply IdTSet_from_list_spec in H0. eauto.
Qed.

Lemma lookupAL_reverse_aux
      X lbl l v
      (IN_REV: lookupAL X (List.map (fun x => (snd x, fst x)) l) lbl = Some v)
  : In (v, lbl) l.
Proof.
  revert IN_REV.
  induction l; ss.
  des_ifs.
  - i. clarify. left. destruct a; eauto.
  - i. right. eauto.
Qed.

Lemma resolve_eq_getValueViaLabelFromValuels
      l_from phinodes passigns
      p ty vls v
      (RESOLVE : forallb_map (Phinode.resolve l_from) phinodes = Some passigns)
      (UNIQUE_ID : unique id_dec (List.map Phinode.get_def passigns) = true)
      (IN_PHIS: In (insn_phi p ty vls) phinodes)
      (GET_VALUE: getValueViaLabelFromValuels vls l_from = Some v)
  : In (Phinode.assign_intro p ty v) passigns.
Proof.
  revert dependent passigns.
  revert IN_PHIS.
  induction phinodes; ss; i.
  des_ifs. des.
  - subst. ss. des_ifs.
    assert (XX: v = v0).
    { clear -GET_VALUE Heq1.
      induction vls; ss.
      des_ifs. exploit IHvls; eauto.
    }
    subst. eauto.
  - exploit IHphinodes; eauto.
    + ss. des_bool. des. eauto.
    + i. ss. right. eauto.
Qed.

Lemma wf_const_valid_ptr
      conf st0 invmem phinodes gmax public
  (MEM : InvMem.Unary.sem conf gmax public (Mem st0) invmem)
  (WF_SUBSET : Forall
                (fun phi : phinode =>
                 exists b : block, phinodeInBlockB phi b /\ blockInFdefB b (CurFunction (EC st0))) phinodes)
  reg val' t1 vls1 const5
  nextbb
  (WF_INSN: wf_insn (CurSystem conf)
                    conf
                    (CurFunction (EC st0)) nextbb (insn_phinode (insn_phi reg t1 vls1)))
  (INCOMING_IN : In (insn_phi reg t1 vls1) phinodes)
  (INCOMING_VALUES : getValueViaLabelFromValuels vls1 (getBlockLabel (CurBB (EC st0))) = Some (value_const const5))
  (INCOMING_GET : const2GV (CurTargetData conf) (Globals conf) const5 = Some val')
  :
    <<VALID_PTR: memory_props.MemProps.valid_ptrs (gmax + 1)%positive val'>>
.
Proof.
  move WF_SUBSET at bottom.
  rewrite List.Forall_forall in WF_SUBSET.
  specialize (WF_SUBSET (insn_phi reg t1 vls1) INCOMING_IN). des.

  inv WF_INSN. clear H7 H8.
  exploit H6.
  {
    instantiate (1:= value_const const5).
    exploit infrastructure_props.getValueViaLabelFromValuels__InValueList; eauto.
    intros IN_CONST.
    clear - IN_CONST.
    {
      induction vls1; ss.
      des_ifs.
      des; clarify.
      - left; ss.
      - right; ss. eapply IHvls1; eauto.
    }
  (* split_combine *)
  (* in_combine_l *)
  }
  intro WF_VALUE. ss. des.

  inv WF_VALUE. destruct conf; ss. des_ifs.
  symmetry in INCOMING_GET.

  inv MEM.
  clear WF PRIVATE_PARENT MEM_PARENT UNIQUE_PARENT_MEM
        UNIQUE_PARENT_GLOBALS UNIQUE_PRIVATE_PARENT NEXTBLOCK.
  rename GLOBALS into WF_GLOBALS.
  eapply wf_globals_eq in WF_GLOBALS.

  exploit MemAux.wf_globals_const2GV; eauto.
  eapply wf_globals_eq; eauto.
Qed.

Lemma wf_const_diffblock
      conf st0 invmem phinodes gmax public
  (MEM : InvMem.Unary.sem conf gmax public (Mem st0) invmem)
  (WF_SUBSET : Forall
                (fun phi : phinode =>
                 exists b : block, phinodeInBlockB phi b /\ blockInFdefB b (CurFunction (EC st0))) phinodes)
  val reg val' t1 vls1 const5
  nextbb
  (WF_INSN: wf_insn (CurSystem conf)
                    conf
                    (CurFunction (EC st0)) nextbb (insn_phinode (insn_phi reg t1 vls1)))
  (GLOBALS : forall b : Values.block, In b (GV2blocks val) -> (gmax < b)%positive)
  (INCOMING_IN : In (insn_phi reg t1 vls1) phinodes)
  (INCOMING_VALUES : getValueViaLabelFromValuels vls1 (getBlockLabel (CurBB (EC st0))) = Some (value_const const5))
  (INCOMING_GET : const2GV (CurTargetData conf) (Globals conf) const5 = Some val')
  :
    <<DIFFBLOCK: InvState.Unary.sem_diffblock conf val val'>>
.
Proof.
  ii.
  exploit wf_const_valid_ptr; eauto; []; ii; des.
  eapply valid_ptr_globals_diffblock; eauto.
Qed.

Lemma wf_phinodes_wf_insn
      reg t1 vls1 phinodes5
      (INCOMING_IN: In (insn_phi reg t1 vls1) phinodes5)
      CurFunction0 CurSystem0 stmts md
      (WF: wf_phinodes CurSystem0 md CurFunction0
                       stmts phinodes5)
  :
    <<WF: wf_insn CurSystem0 md CurFunction0 stmts (insn_phinode (insn_phi reg t1 vls1))>>
.
Proof.
  ginduction phinodes5; ii; ss.
  inv WF.
  des.
  - clarify.
  - eapply IHphinodes5; eauto.
Qed.

Lemma wf_ec_lookup_wf_ec
      st0
      l_to
      conf
      phinodes5 cmds_src terminator_src
      (LOOKUP: lookupAL stmts (get_blocks (CurFunction (EC st0))) l_to =
               Some (stmts_intro phinodes5 cmds_src terminator_src))
      (WF_FDEF: wf_fdef (CurSystem conf) (OpsemAux.module_of_conf conf) (CurFunction (EC st0)))
      (WF_EC: OpsemAux.wf_EC (EC st0))
      locals_src
  :
    <<WF: OpsemAux.wf_EC
            {|
              CurFunction := CurFunction (EC st0);
              CurBB := (l_to, stmts_intro phinodes5 cmds_src terminator_src);
              CurCmds := cmds_src;
              Terminator := terminator_src;
              Locals := locals_src;
              Allocas := Allocas (EC st0) |}>>
.
Proof.
  inv WF_EC.
  econs; ss; eauto.
  - unfold get_blocks in *. des_ifs.
    destruct st0; ss. destruct EC0; ss. clarify.
    clear - LOOKUP.
    (* TODO: pull out lemma? Use Set Printing All and then pull out, otherwise type checking fails *)
    ginduction blocks5; ii; ss.
    apply orb_true_iff.
    des_ifs.
    + left. unfold blockEqB. unfold sumbool2bool. des_ifs.
    + right. eapply IHblocks5; eauto.
  - autounfold. ss.
    apply sublist_refl.
  - unfold terminatorEqB. unfold sumbool2bool. des_ifs.
Qed.

Hint Unfold OpsemAux.get_cmds_from_block. (* TODO: move to definition point *)
Hint Unfold OpsemAux.module_of_conf. (* TODO: move to definition point *)

(* st0 is the state before entering "phinodes". *)
(* Therefore, phinodes in st0.(EC).(CurBB) <> "phinodes". *)
(* st0.(EC).(CurBB) is the block before "phinodes". *)
(* "nextbb" represents block of the "phinodes". *)
(* It is introduced for "WF_PHIS" only. *)
Lemma phinodes_unique_preserved_except
      conf st0 inv0 invmem invst
      l_to phinodes cmds terminator locals l0
      gmax public
      (STATE : InvState.Unary.sem conf st0 invst invmem gmax public inv0)
      (MEM : InvMem.Unary.sem conf gmax public st0.(Mem) invmem)
      (RESOLVE : forallb_map (Phinode.resolve (fst (CurBB (EC st0)))) phinodes = Some l0)
      (UNIQUE_ID : unique id_dec (List.map Phinode.get_def l0) = true)
      (STEP : switchToNewBasicBlock (CurTargetData conf) (l_to, stmts_intro phinodes cmds terminator)
                                    (CurBB (EC st0)) (Globals conf) (Locals (EC st0)) = Some locals)
      nextbb
      (WF_PHIS: wf_phinodes (CurSystem conf) conf (CurFunction (EC st0)) nextbb phinodes)
      (WF_SUBSET: List.Forall (fun phi =>
                          exists b,
                            insnInBlockB (insn_phinode phi) b
                            /\ blockInFdefB b (CurFunction (EC st0))) phinodes)
  : unique_preserved_except conf inv0 invmem.(InvMem.Unary.unique_parent)
                                               (mkState (mkEC
                                                           st0.(EC).(CurFunction)
                                                                      (l_to, stmts_intro phinodes cmds terminator)
                                                                      cmds
                                                                      terminator
                                                                      locals
                                                                      st0.(EC).(Allocas))
                                                        st0.(ECS) st0.(Mem))
                                               gmax
                                               (AtomSetImpl.union (AtomSetImpl_from_list (List.map Phinode.get_def l0))
                                                                  (AtomSetImpl_from_list (filter_map Phinode.get_use l0))).
Proof.
  econs; ss.
  - i.
    rewrite <- AtomSetFacts.not_mem_iff in *.
    hexploit notin_union_1; eauto. intro NOT_IN_DEF.
    hexploit notin_union_2; eauto. intro NOT_IN_USE.
    rewrite AtomSetImpl_from_list_spec2 in *.

    inv STATE.
    rewrite <- AtomSetFacts.mem_iff in *.
    exploit UNIQUE; eauto. intro UNIQUE_U.

    unfold switchToNewBasicBlock in STEP. des_ifs.
    inv UNIQUE_U.
    econs; eauto; ss.
    + rewrite opsem_props.OpsemProps.updateValuesForNewBlock_spec7'; eauto.
      eapply opsem_props.OpsemProps.getIncomingValuesForBlockFromPHINodes_spec8; eauto.
      ss. ii.
      exploit phinodes_progress_getPhiNodeID_safe; eauto.
    + i.
      destruct (AtomSetImpl.mem reg (dom l1)) eqn:REG_MEM.
      { rewrite <- AtomSetFacts.mem_iff in REG_MEM.
        hexploit indom_lookupAL_Some; eauto. i. des.
        exploit opsem_props.OpsemProps.getIncomingValuesForBlockFromPHINodes_spec9'; eauto.
        intros INCOMING. destruct INCOMING as [t1 [vls1 [v [INCOMING_IN [INCOMING_VALUES INCOMING_GET]]]]].
        (* better way to name it?? *)

        exploit resolve_eq_getValueViaLabelFromValuels; eauto. intro IN_PASSIGNS.
        rewrite opsem_props.OpsemProps.updateValuesForNewBlock_spec6' in *; eauto. clarify.
        destruct v as [y|].
        - ss. eapply LOCALS; [| eauto].
          ii. subst.
          apply NOT_IN_USE. clarify.
          eapply filter_map_spec; eauto.
        - eapply wf_const_diffblock; eauto.
          eapply wf_phinodes_wf_insn; eauto.
      }
      { rewrite <- AtomSetFacts.not_mem_iff in REG_MEM.
        rewrite opsem_props.OpsemProps.updateValuesForNewBlock_spec7' in VAL'; eauto.
      }
  - inv STATE.
    i. unfold switchToNewBasicBlock in *.
    des_ifs.
    destruct (AtomSetImpl.mem x (dom l1)) eqn:REG_MEM.
    { rewrite <- AtomSetFacts.mem_iff in REG_MEM.
      hexploit indom_lookupAL_Some; eauto. i. des.
      exploit opsem_props.OpsemProps.getIncomingValuesForBlockFromPHINodes_spec9'; eauto. i. des.
      ss.

      
      exploit phinode_assign_sound; eauto.
      { eapply resolve_eq_getValueViaLabelFromValuels; eauto. }
      i. des.
      apply opsem_props.OpsemProps.updateValuesForNewBlock_spec4 with (lc:=st0.(EC).(Locals)) in VAL_X.
      clarify.
      destruct v as [y|]; ss.
      - eapply UNIQUE_PARENT_LOCAL; eauto.
      - hexploit wf_const_valid_ptr; eauto.
        { eapply wf_phinodes_wf_insn; eauto.
        }
        intro VALID_PTR; des.
        inv MEM.
        eapply valid_ptr_globals_diffblock_with_blocks; eauto.
    }
    { rewrite <- AtomSetFacts.not_mem_iff in REG_MEM.
      rewrite opsem_props.OpsemProps.updateValuesForNewBlock_spec7' in PTR; eauto.
    }
  - inv MEM. eauto.
  - inv MEM. eauto.
Unshelve.
ss.
Qed.

Lemma switchToNewBasicBlock_wf
      conf mem locals locals'
      l_from l_to stmts
      (WF_LOCAL : memory_props.MemProps.wf_lc mem locals)
      (STEP: switchToNewBasicBlock (CurTargetData conf) (l_to, stmts)
                                   l_from (Globals conf) locals = Some locals')
      gmax public invmem
      (* st0 invst0 inv0 *)
      (* (STATE: InvState.Unary.sem conf st0 invst0 invmem0 gmax public inv0) *)
      (MEM : InvMem.Unary.sem conf gmax public mem invmem)
  : memory_props.MemProps.wf_lc mem locals'.
Proof.
  unfold switchToNewBasicBlock in *. des_ifs.
  intros x gvx Hx.
  destruct (AtomSetImpl.mem x (dom l0)) eqn:REG_MEM.
  { rewrite <- AtomSetFacts.mem_iff in REG_MEM.
    hexploit indom_lookupAL_Some; eauto. i. des.
    exploit opsem_props.OpsemProps.getIncomingValuesForBlockFromPHINodes_spec9'; eauto. i. des.
    (* assert(H2:= H). *)
    apply opsem_props.OpsemProps.updateValuesForNewBlock_spec4 with (lc:=locals) in H. clarify.
    {
      destruct v; ss.
      - eapply WF_LOCAL; eauto.
      - inv MEM.
        exploit MemAux.wf_globals_const2GV; eauto; []; ii; des.
        unfold memory_props.MemProps.wf_Mem in WF. des.
        clear - WF0 x4.
        eapply memory_props.MemProps.valid_ptrs__trans; eauto.
        eapply Pos.lt_succ_r.
        replace (gmax + 1)%positive with (Pos.succ gmax); cycle 1.
        { destruct gmax; ss. }
        rewrite <- Pos.succ_lt_mono; eauto.
    }
  }
  { rewrite <- AtomSetFacts.not_mem_iff in REG_MEM.
    rewrite opsem_props.OpsemProps.updateValuesForNewBlock_spec7' in Hx; eauto.
  }
Qed.

Lemma lookup_implies_wf_subset
      st0 l_to phinodes cmds terminator
      (STMT : lookupAL stmts (get_blocks (CurFunction (EC st0))) l_to =
                  Some (stmts_intro phinodes cmds terminator))
  :
    <<WF_SUBSET: List.Forall
      (fun phi : phinode =>
         exists b : block, insnInBlockB (insn_phinode phi) b /\ blockInFdefB b (CurFunction (EC st0)))
      phinodes>>
.
Proof.
  destruct st0; ss. destruct EC0; ss. destruct CurFunction0; ss.
  clear - phinodes STMT.
  red.
  rewrite List.Forall_forall.
  i.
  induction blocks5; ii; ss.
  destruct a; ss.
  rename s into __s__.
  des_ifs.
  - esplits; eauto; cycle 1.
    + unfold is_true.
      rewrite orb_true_iff.
      left. instantiate (1:= (l0, stmts_intro phinodes cmds terminator)).
      rewrite infrastructure_props.blockEqB_refl. ss.
    + ss. clear - H.
      apply infrastructure_props.In_InPhiNodesB; ss.
  - exploit IHblocks5; eauto; []; ii; des.
    esplits; eauto.
    unfold is_true.
    rewrite orb_true_iff.
    right.
    ss.
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
  clarify.
  des_ifs_safe ss. clarify.
  des_bool. des.
  (* simtac. *) (* TODO: simtac LOSES INFORMATION on PHIS_SRC/PHIS_TGT *)
  (* TODO: REMOVE ALL SIMTAC *)
  exploit snapshot_sound; eauto. i. des.

  exploit forget_stack_sound; [eauto|eauto|eauto|eauto|eauto|eauto|eauto|..].
  { instantiate (1 := mkState (mkEC _ _ _ _ _ _) _ _). econs; s; eauto.
    eapply locals_equiv_after_phinode; eauto.
  }
  { instantiate (1 := mkState (mkEC _ _ _ _ _ _) _ _). econs; s; eauto.
    eapply locals_equiv_after_phinode; eauto.
    rewrite L_TGT. eauto.
  }
  { inv STATE_SNAPSHOT. inv MEM.
    instantiate (6:= (_, stmts_intro phinodes_src _ _)).
    eapply phinodes_unique_preserved_except; eauto.
    { instantiate (1:= (l_to, (stmts_intro phinodes_src cmds_src terminator_src))).
      inv STATE. inv SRC.
      clear - STMT_SRC WF_EC WF_FDEF.
      rpapply typings_props.wf_fdef__wf_phinodes; eauto. Undo 1.
      destruct st0_src; ss. destruct EC0; ss. destruct CurBB0; ss. destruct s; ss.
      eapply typings_props.wf_fdef__wf_phinodes; eauto.
      rpapply infrastructure_props.lookupBlock_blocks_inv; try eassumption. Undo 1.
      destruct CurFunction0.
      rpapply infrastructure_props.lookupBlock_blocks_inv; eauto.
    }
    { eapply lookup_implies_wf_subset; eauto. }
  }
  { inv STATE_SNAPSHOT. inv MEM.
    instantiate (6:= (_, stmts_intro phinodes_tgt _ _)).
    eapply phinodes_unique_preserved_except; eauto.
    { rewrite L_TGT. ss. }
    { instantiate (1:= (l_to, (stmts_intro phinodes_tgt cmds_tgt terminator_tgt))).
      inv STATE. inv TGT.
      clear - STMT_TGT WF_EC WF_FDEF.
      rpapply typings_props.wf_fdef__wf_phinodes; eauto. Undo 1.
      destruct st0_tgt; ss. destruct EC0; ss. destruct CurBB0; ss. destruct s; ss.
      eapply typings_props.wf_fdef__wf_phinodes; eauto.
      rpapply infrastructure_props.lookupBlock_blocks_inv; try eassumption. Undo 1.
      destruct CurFunction0.
      rpapply infrastructure_props.lookupBlock_blocks_inv; eauto.
    }
    { eapply lookup_implies_wf_subset; eauto. }
  }
  { eapply switchToNewBasicBlock_wf; try exact STEP_SRC; eauto. apply STATE. apply MEM. }
  { eapply switchToNewBasicBlock_wf; try exact STEP_TGT; eauto. apply STATE. apply MEM. }
  { ss. }
  { ss. }
  { apply STATE. }
  { apply STATE. }
  { apply STATE. }
  { apply STATE. }
  { apply STATE. }
  { eapply wf_ec_lookup_wf_ec; eauto; try apply STATE. }
  { eapply wf_ec_lookup_wf_ec; eauto; try apply STATE. }
  intros STATE_FORGET. des.
  inv STATE_FORGET.
  exploit phinodes_add_lessdef_sound; try exact SRC; eauto; i.
  exploit phinodes_add_lessdef_sound; try exact TGT; eauto; i.
  { rewrite L_TGT. eauto. }
  exploit reduce_maydiff_sound; swap 1 2.
  { instantiate (1 := Hints.Invariant.mk _ _ _). econs; eauto. }
  { eauto. }
  { eauto. }
  intro STATE_MAYDIFF. exact STATE_MAYDIFF.
Qed.
