Require Import vgtac.
Require Import vellvm.
Require Import memory_sim.
Require Import genericvalues_inject.
Require Import dopsem.

Require Import decs.
Require Import validator.
Require Import validator_aux.
Require Import validator_props.
Require Import set_facts2.
Require Import state_props.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import logical_step.

Require Import hint_sem_props_implies.
Require Import hint_sem_props_resolve.
Require Import hint_sem_props_proceed_step_defs.
Require Import hint_sem_props_proceed_phi.
Require Import hint_sem_props_proceed_hfilter.

Require Import hint_sem_props_resolve_defs.

Require Import FSetFacts.

Import Opsem.
Import syntax_ext.
Import hints.

Lemma pop_one_nil_nonzero hpn pst hnn nna
  (Hnonzero: false = noop_idx_zero_exists hpn)
  (Hpop: pop_one nil hpn pst hnn nna) :
  pst = pop_terminator.
Proof.
  inv Hpop; auto.
  unfold pop_one_X in Hpop0.
  rewrite <- Hnonzero in Hpop0.
  by inv Hpop0.
Qed.

Definition get_phinodes_from_previous_block (ec: @Opsem.ExecutionContext DGVs) td gl :=
  match ec with
    | mkEC F _ _ (insn_br _ cond l1 l2) lc _ =>
      match (getOperandValue td cond lc gl) with
        | Some cv => 
          match (if isGVZero td cv then lookupBlockViaLabelFromFdef F l2
            else lookupBlockViaLabelFromFdef F l1) with
            | Some (stmts_intro phis _ _) => Some phis
            | _ => None
          end
        | _ => None
      end
    | mkEC F _ _ (insn_br_uncond _ l) lc _ =>
      match (lookupBlockViaLabelFromFdef F l) with
        | Some (stmts_intro phis _ _) => Some phis
        | _ => None
      end
    | _ => None
  end.

Lemma invariant_proceed_preserves_hint_sem_fdef_branch :
  forall hint nhint1 nhint2 ptns1 ptns2 pi1 li1 pi2 li2
    alpha gmax fn_al1 fn_al2
    m1 cfg1 ec1 pecs1 pmem1 pns1
    m2 cfg2 ec2 pecs2 pmem2 pns2
    (Hmatch: matched_module_cfg m1 m2 cfg1 cfg2)
    (Hsim: hint_sem_insn hint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha gmax cfg1 (ec1::pecs1) pmem1 pns1 cfg2 (ec2::pecs2) pmem2 pns2)

    CurFunction1 CurBB1 CurCmds1 Terminator1 Locals1 Allocas1
    CurFunction2 CurBB2 CurCmds2 Terminator2 Locals2 Allocas2

    tr1 nec nst1 nmem1 nns1
    tr2 nec' nst2 nmem2 nns2
    phis1 phis2

    (Hec1: ec1 = mkEC CurFunction1 CurBB1 CurCmds1 Terminator1 Locals1 Allocas1)
    (Hec2: ec2 = mkEC CurFunction2 CurBB2 CurCmds2 Terminator2 Locals2 Allocas2)
    (Hphis1: get_phinodes_from_previous_block ec1 (CurTargetData cfg1) (Globals cfg1)
      = Some phis1)
    (Hphis2: get_phinodes_from_previous_block ec2 (CurTargetData cfg2) (Globals cfg2)
      = Some phis2)
    (Hcb: fst CurBB1 = fst CurBB2)

    (* Hypothesis which are invariants, can be drawn from outside. *)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgna1: globals_no_alias (Globals cfg1))
    (Hgna2: globals_no_alias (Globals cfg2))
    (Hterm: terminator_args_eq_check Terminator1 Terminator2 hint)

    (Hpop1: pop_state_terminator (ec1::pecs1) pns1)
    (Hpop2: pop_state_terminator (ec2::pecs2) pns2)
    (Hstep1: logical_semantic_step cfg1 fn_al1
      (mkState ec1 pecs1 pmem1) (mkState nec nst1 nmem1)
      pns1 nns1 merror tr1)
    (Hstep2: logical_semantic_step cfg2 fn_al2
      (mkState ec2 pecs2 pmem2) (mkState nec' nst2 nmem2)
      pns2 nns2 merror tr2)
    bid
    (Hbid1: is_branch cfg1 (mkState ec1 pecs1 pmem1) bid)
    (Hbid2: is_branch cfg2 (mkState ec2 pecs2 pmem2) bid)

    (Hnhint1: invariant_implies (infrules_resolve m1 m2 hint) nhint1)
    (Hprc: invariant_proceed_phis nhint1 phis1 phis2 (fst CurBB1) = ret nhint2),

    logical_semantic_step cfg1 fn_al1
    (mkState ec1 pecs1 pmem1) (mkState nec nst1 nmem1) pns1 nns1 merror tr1 /\
    hint_sem_insn nhint2 pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
    alpha gmax cfg1 nst1 nmem1 nns1 cfg2 nst2 nmem2 nns2.
Proof.
  intros.
  split; [done|].
  inv Hsim; simpl in *.
  unfold pop_one_X in Hpop1.
  remember (noop_idx_zero_exists n1) as nn1; destruct nn1; [by inv Hpop1|].
  destruct CurCmds1; inv Hpop1.
  unfold pop_one_X in Hpop2.
  remember (noop_idx_zero_exists n2) as nn2; destruct nn2; [by inv Hpop2|].
  destruct CurCmds2; inv Hpop2.
  inv Hstep1; inv Hstep2.
  inv Hec; inv Hpn; inv Hpn0; simpl in *.
  inv Hec0. admit. (*
  exploit (pop_one_nil_nonzero hpn); eauto.
  exploit (pop_one_nil_nonzero hpn0); eauto.
  intros Hpst0 Hpst; subst.
  clear Hpop Hpop0 Heqnn1 Heqnn2 hpn hpn0.
  inv Hnoop; [by inv Hnnn|].
  inv Hnoop0; [by inv Hnnn0|].
  destruct cfg1, cfg2; simpl in *.
  destruct Hbid1 as [_ Hbid1].
  destruct Hbid2 as [_ Hbid2].
  inv Hnnn; simpl in *.
  { destruct Hret as [_ Hret].
    by destruct Terminator1.
  }
  inv Hnnn0; simpl in *.
  { destruct Hret as [_ Hret].
    by destruct Terminator2.
  }
  destruct Hbrc as [_ Hbrc].
  destruct Hbrc0 as [_ Hbrc0].
  destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
  destruct Terminator2; inv Hbrc0;
    destruct Terminator1; inv Hbrc; inv Hterm;
    inv Hstep; inv Hstep0;
    infrule_tac.

  - inv H21; inv H25.
    exploit eq_check_value_prop; eauto; simpl.
    { by inv Hvmem. }
    { by rewrite <- getOperandValue_equals_getOperandValueExt_new; eauto. }
    { by rewrite <- getOperandValue_equals_getOperandValueExt_new; eauto. }
    intro Hinj.

    inv H20; inv H24.
    generalize (simulation__isGVZero alpha c c0 CurTargetData1 Hinj);
      clear Hinj; intro Hinj.
    eapply invariant_proceed_preserves_hint_sem_insn_phi.
    + instantiate (1:=(if isGVZero CurTargetData1 c then l2 else l1,
      stmts_intro ps' cs' tmn')); simpl; reflexivity.
    + instantiate (1:=(if isGVZero CurTargetData1 c0 then l2 else l1,
      stmts_intro ps'0 cs'0 tmn'0)); simpl.
      rewrite Hinj; done.
    + instantiate (1:=CurBB1); reflexivity.
    + instantiate (1:=CurBB2); done.
    + simpl; symmetry; apply H23.
    + simpl; symmetry; apply H27.
    + instantiate (1:=phis1).
      destruct (isGVZero CurTargetData1 c);
        simpl; destruct s; inv Hphis1; rewrite <-H22 in Heqy0; inv Heqy0; done.
    + instantiate (1:=phis2).
      destruct (isGVZero CurTargetData1 c0);
        simpl; destruct s0; inv Hphis2; rewrite <-H26 in Heqy2; inv Heqy2; done.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + instantiate (1:=mkEC CurFunction1 (if isGVZero CurTargetData1 c then l2 else l1,
      stmts_intro ps' cs' tmn') cs' tmn' Locals1 Allocas1).
      simpl; done.
    + instantiate (1:=mkEC CurFunction2 (if isGVZero CurTargetData1 c0 then l2 else l1,
      stmts_intro ps'0 cs'0 tmn'0) cs'0 tmn'0 Locals2 Allocas2).
      simpl; done.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + symmetry; apply Hprc.
    + eapply invariant_implies_preserves_hint_sem_fdef; eauto.
      eapply infrules_resolve_preserves_hint_sem_fdef; eauto;
        [by apply infrules_correct|].
      constructor; simpl; auto; simpl.
      by exists olc1; exists olc2; split; eauto.

  - eapply invariant_proceed_preserves_hint_sem_insn_phi.
    + instantiate (1:=(l0, stmts_intro ps' cs' tmn')).
      simpl; reflexivity.
    + instantiate (1:=(l0, stmts_intro ps'0 cs'0 tmn'0)).
      simpl; reflexivity.
    + instantiate (1:=CurBB1); reflexivity.
    + instantiate (1:=CurBB2); done.
    + simpl; symmetry; apply H19.
    + simpl; symmetry; apply H21.
    + instantiate (1:=phis1).
      simpl; destruct s0; inv Hphis1; inv H18; done.
    + instantiate (1:=phis2).
      simpl; destruct s; inv Hphis2; inv H20; done.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + instantiate (1:=mkEC CurFunction1 (l0, stmts_intro ps' cs' tmn') cs' tmn'
      Locals1 Allocas1).
      simpl; done.
    + instantiate (1:=mkEC CurFunction2 (l0, stmts_intro ps'0 cs'0 tmn'0) cs'0 tmn'0
      Locals2 Allocas2).
      simpl; done.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + symmetry; apply Hprc.
    + eapply invariant_implies_preserves_hint_sem_fdef; eauto.
      eapply infrules_resolve_preserves_hint_sem_fdef; eauto;
        [by apply infrules_correct|].
      constructor; simpl; auto; simpl.
      by exists olc1; exists olc2; split; eauto.
      *)
Qed.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
