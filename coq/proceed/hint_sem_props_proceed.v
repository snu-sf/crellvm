Require Import sflib.
Require Import vellvm.
Require Import memory_sim.
Require Import genericvalues_inject.
Require Import dopsem.

Require Import decs.
Require Import validator_aux.
Require Import validator_props.
Require Import set_facts2.
Require Import state_props.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import logical_step.

Require Import hint_sem_props_proceed_step_defs.

Require Import hint_sem_props_proceed_hcheck.
Require Import hint_sem_props_proceed_oldnew.
Require Import hint_sem_props_proceed_maydiff.
Require Import hint_sem_props_proceed_hfilter.
Require Import hint_sem_props_proceed_addcmd.
Require Import hint_sem_props_proceed_addneq.

Require Import FSetFacts.

Import Opsem.
Import syntax_ext.
Import hints.

Lemma logical_semantic_step_implies_same_ECStack_tail :
  forall cfg fn_al pec ecs pm pec' nst nm pns nns na tr ocmd
    (Hpop: pop_state_ocmd (pec::ecs) pns ocmd)
    (Hstep: logical_semantic_step cfg fn_al
      {| Opsem.EC := pec; Opsem.ECS := ecs; Opsem.Mem := pm |}
      {| Opsem.EC := pec'; Opsem.ECS := nst; Opsem.Mem := nm |} pns nns na tr)
    (Hncall: ocmd = merror \/ ~ is_general_call_state {| Opsem.EC := pec; Opsem.ECS := ecs; Opsem.Mem := pm |}),
    exists nec, nst = nec::ecs.
Proof.
  intros; inv Hstep; simpl in Hec; admit. (* inv Hec.
  destruct pst.
  - by eexists; destruct Hstep0 as [Hres _]; inv Hres.
  - unfold pop_state_ocmd in Hpop.
    inv Hpop0; [|done].
    rewrite Hpop1 in Hpop. subst.
    destruct rcmd; [|done].
    destruct Hncall as [|Hncall]; [done|].
    inv Hnoop; [|done].
    inv Hnnn; [done|idtac|idtac|].
    + assert (CurCmds ec <> nil).
      { intro Hcontr; rewrite Hcontr in Hpop1.
        unfold pop_one_X in Hpop1.
        by destruct (noop_idx_zero_exists hpn).
      }
      inv Hstep0; try done; try (eexists; reflexivity).
      by simpl in Hncall.
    + unfold is_call in Hcall.
      unfold is_general_call_state in Hncall.
      by destruct cfg, ec; destruct CurCmds0 as [|[]].
    + unfold is_excall in Hexcall.
      unfold is_general_call_state in Hncall.
      by destruct cfg, ec; destruct CurCmds0 as [|[]].
  - inv Hnoop; [by inv Hnnn|].
    inv Hpop0; [by destruct rcmd|].
    unfold pop_state_ocmd in Hpop.
    by rewrite Hpop2 in Hpop. *)
Qed.

Lemma logical_semantic_step_implies_same_noop_stack_tail :
  forall cfg fn_al ec pst pm ec' nst nm phns tns nns na tr ocmd
    (Hpop: pop_state_ocmd pst (phns::tns) ocmd)
    (Hstep: logical_semantic_step cfg fn_al
      {| Opsem.EC := ec; Opsem.ECS := pst; Opsem.Mem := pm |}
      {| Opsem.EC := ec'; Opsem.ECS := nst; Opsem.Mem := nm |} (phns::tns) nns na tr)
    (Hncall: ocmd = merror \/ ~ is_general_call_state {| Opsem.EC := ec; Opsem.ECS := pst; Opsem.Mem := pm |}),
    exists nhns, nns = nhns::tns.
Proof.
  intros. inv Hstep. destruct pst; inv Hec. inv Hpn.
  destruct pst0.
  - inv Hnoop; [|done].
    inv Hnnn; simpl; try by eexists; reflexivity.
    unfold is_call in Hcall.
    unfold is_general_call_state in Hncall.
    by destruct cfg.
  - unfold pop_state_ocmd in Hpop.
    inv Hpop0; [|done].
    destruct rcmd; [|done].
    rewrite Hpop1 in Hpop. subst.
    destruct Hncall as [|Hncall]; [done|].
    inv Hnoop; [|done].
    inv Hnnn; simpl; try by eexists; reflexivity.
    unfold is_call in Hcall.
    unfold is_general_call_state in Hncall.
    destruct cfg; try done.
    by destruct ec; destruct CurCmds0 as [|[]].
  - inv Hpop0; [by destruct rcmd|].
    unfold pop_state_ocmd in Hpop.
    by rewrite Hpop1 in Hpop.
Qed.

Lemma hint_sem_insn_implies_same_call_state:
  forall m1 m2 hint nhint ocmd1 ocmd2
    (Hprc: invariant_proceed m1 m2 hint ocmd1 ocmd2 = ret nhint)
    (Hncall2: forall rid, ~ is_general_call ocmd2 rid),
    (forall rid, ~ is_general_call ocmd1 rid).
Proof.
  intros.
  unfold invariant_proceed in Hprc.
  remember (heap_eq_check (hint_maydiff hint)
    (invariant_original (hint_invariant hint))
    (invariant_optimized (hint_invariant hint))
    (iso_original (hint_invariant hint))
    (iso_optimized (hint_invariant hint)) ocmd1 ocmd2) as hcheck.
  destruct hcheck; [|done]; clear Hprc.
  destruct ocmd1 as [[]|]; try done.
  destruct ocmd2 as [[]|]; try done.
  by elim (Hncall2 id0).
Qed.

Lemma hint_sem_insn_implies_same_step:
  forall fn_al1 fn_al2 cfg1 pst1 pecs nst1 necs pmem1 nmem1 pns1 nns1 nna1 ocmd1 tr1
    cfg2 pst2 pecs' pmem2 pns2 tr nst2 necs' nmem2 nns2 nna2 ocmd2

    (Hncall1: forall rid, ~ is_general_call ocmd1 rid)
    (Hncall2: forall rid, ~ is_general_call ocmd2 rid)
    (Hpop1: pop_state_ocmd (pst1::pecs) pns1 ocmd1)
    (Hpop2: pop_state_ocmd (pst2::pecs') pns2 ocmd2)
    (Hstep1: logical_semantic_step cfg1 fn_al1 (mkState pst1 pecs pmem1) (mkState nst1 necs nmem1)
      pns1 nns1 nna1 tr1)
    (Hstep2: logical_semantic_step cfg2 fn_al2 (mkState pst2 pecs' pmem2) (mkState nst2 necs' nmem2)
      pns2 nns2 nna2 tr),
    logical_semantic_step cfg1 fn_al1 (mkState pst1 pecs pmem1) (mkState nst1 necs nmem1)
    pns1 nns1 nna1 tr.
Proof.
  intros. admit. (*
  assert (Htrnil: tr = E0). admit.
  { inv Hstep2. simpl in Hec; inv Hec; clear H.
    destruct pst;
      [by destruct Hstep| |
        by inv Hpop; [destruct rcmd|
          unfold pop_state_ocmd in Hpop2; rewrite Hpop0 in Hpop2]].
    inv Hstep; try done.
    inv Hpop; [|done]; destruct rcmd; [|done]; clear Hist.
    move Hpop2 at bottom.
    unfold pop_state_ocmd in Hpop2; simpl in Hpop0, Hpop2.
    unfold pop_one_X in Hpop0, Hpop2.
    destruct (noop_idx_zero_exists hpn); [done|].
    subst ocmd2; simpl in Hncall2.
    by elim (Hncall2 rid).
  }
  subst tr.

  assert (tr1 = E0).
  { inv Hstep1.
    simpl in Hec; inv Hec; clear H.
    destruct pst.
    + by destruct Hstep.
    + inv Hpop; [|done]; destruct rcmd; [|done]; clear Hist.
      unfold pop_state_ocmd in Hpop1.
      rewrite Hpop0 in Hpop1; subst ocmd1.
      unfold pop_one_X in Hpop0.
      destruct (noop_idx_zero_exists hpn); [done|].
      remember (CurCmds ec) as cec; destruct cec; [done|]; inv Hpop0.
      inv Hstep; try done.
      simpl in Heqcec; inv Heqcec.
      simpl in Hncall1.
      by elim (Hncall1 rid).
    + inv Hpop; [by destruct rcmd|]; clear Hist.
      unfold pop_state_ocmd in Hpop1.
      by rewrite Hpop0 in Hpop1.
  }
  by subst tr1. *)
Qed.

Lemma invariant_proceed_preserves_hint_sem_insn_normal :
  forall m1 m2 hint nhint pecs1 pecs2 ptns1 ptns2 pi1 li1 pi2 li2 tr1
    alpha gmax fn_al1 fn_al2 cfg1 pec pst1 pmem1 pns1 nec nst1 nmem1 nns1 nna1
    cfg2 pec' pst2 pmem2 pns2 tr nec' nst2 nmem2 nns2 nna2 ocmd1 ocmd2

    (* Hypotheses which are invariants, can be drawn from outside. *)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgna1: globals_no_alias (Globals cfg1))
    (Hgna2: globals_no_alias (Globals cfg2))
    (Hgids1: is_global_ids (collect_global_ids (get_products_from_module m1))
      (Globals cfg1))
    (Hgids2: is_global_ids (collect_global_ids (get_products_from_module m2))
      (Globals cfg2))
    (* End of external hypotheses. *)

    (Hsim: hint_sem_insn hint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha gmax cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2)
    (Hpop1: pop_state_ocmd pst1 pns1 ocmd1)
    (Hpop2: pop_state_ocmd pst2 pns2 ocmd2)
    (Hprc: invariant_proceed m1 m2 hint ocmd1 ocmd2 = ret nhint)
    (Hestep1: logical_semantic_step cfg1 fn_al1 (mkState pec pst1 pmem1) (mkState nec nst1 nmem1)
      pns1 nns1 nna1 tr1)
    (Hstep2: logical_semantic_step cfg2 fn_al2 (mkState pec' pst2 pmem2) (mkState nec' nst2 nmem2)
      pns2 nns2 nna2 tr)
    (Hncall2: forall rid, ~ is_general_call ocmd2 rid),

    logical_semantic_step cfg1 fn_al1 (mkState pec pst1 pmem1) (mkState nec nst1 nmem1)
    pns1 nns1 nna1 tr /\
    (forall rid, ~ is_general_call ocmd1 rid) /\
    exists alpha', exists li1', exists li2',
      (inject_incr' alpha alpha' li1 pi1 li2 pi2 /\
        hint_sem_insn nhint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1' li2'
        alpha' gmax cfg1 nst1 nmem1 nns1 cfg2 nst2 nmem2 nns2).
Proof.
  intros.

  generalize (hint_sem_insn_implies_same_call_state _ _ _ _ _ _ Hprc Hncall2);
    intro Hncall1. admit.
  (*
  exploit hint_sem_insn_implies_same_step.
  { apply Hncall1. }
  { apply Hncall2. }
  { apply Hpop1. }
  { apply Hpop2. }
  { apply Hestep1. }
  { apply Hstep2. }
  intros Hstep1.

  assert (Hncall1': ocmd1 = merror \/
    (is_general_call_state {| ECS := pst1; Mem := pmem1 |} -> False)).
  { destruct ocmd1 as [cmd1|]; [right|left]; [|done].
    destruct pst1; [done|]. inv Hstep1. inv Hec.
    destruct ec. simpl in *.
    destruct CurCmds0; try done.
    destruct c; try done.
    unfold pop_one_X in *.
    inv Hpop; unfold pop_one_X in *; simpl in *;
      [|by destruct (noop_idx_zero_exists hpn)].
    destruct (noop_idx_zero_exists hpn); subst; [done|].
    inv Hpop0. inv Hpop1.
    by elim (Hncall1 id5).
  }

  assert (Hncall2': ocmd2 = merror \/
    (is_general_call_state {| ECS := pst2; Mem := pmem2 |} -> False)).
  { destruct ocmd2 as [cmd2|]; [right|left]; [|done].
    destruct pst2; [done|]. inv Hstep2. inv Hec.
    destruct ec. simpl in *.
    destruct CurCmds0; try done.
    destruct c; try done.
    unfold pop_one_X in *.
    inv Hpop; unfold pop_one_X in *; simpl in *;
      [|by destruct (noop_idx_zero_exists hpn)].
    destruct (noop_idx_zero_exists hpn); subst; [done|].
    inv Hpop0. inv Hpop2.
    by elim (Hncall2 id5).
  }

  inversion Hsim; subst.
  exploit logical_semantic_step_implies_same_ECStack_tail.
  { apply Hpop1. }
  { apply Hstep1. }
  { auto. }

  intros [nec1 Hnst1]; subst.
  exploit logical_semantic_step_implies_same_ECStack_tail.
  { apply Hpop2. }
  { apply Hstep2. }
  { auto. }

  intros [nec2 Hnst2]; subst.
  exploit logical_semantic_step_implies_same_noop_stack_tail.
  { apply Hpop1. }
  { apply Hstep1. }
  { auto. }

  intros [nhns1 Hnns1]; subst.
  exploit logical_semantic_step_implies_same_noop_stack_tail.
  { apply Hpop2. }
  { apply Hstep2. }
  { auto. }

  intros [nhns2 Hnns2]; subst.

  repeat split; try done.

  (* Proving hint_sem_insn preservation using step lemmas. *)
  destruct hint as [md [eqs1 eqs2 iso1 iso2] ir], nhint as [nmd [neqs1 neqs2] nir].
  hexploit hint_sem_insn_implies_hint_sem_each; eauto; intro Heach1.
  unfold invariant_proceed in Hprc; simpl in Hprc.

  (* Gathering information from invariant_proceed. *)
  move Hprc at bottom.
  remember (heap_eq_check md eqs1 eqs2 iso1 iso2 ocmd1 ocmd2) as hcheck;
    destruct hcheck; [|done]; simpl in Hprc; symmetry in Heqhcheck.  
  remember (self_use_check ocmd1) as su1; destruct su1; [|done]; simpl in Hprc.
  remember (self_use_check ocmd2) as su2; destruct su2; [|done]; simpl in Hprc.
  symmetry in Heqsu1, Heqsu2.
  inv Hprc.

  (* A. heap_eq_check *)
  exploit heap_eq_check_preserves_hint_sem_each.
  { apply Hstep1. }
  { apply Hstep2. }
  { apply Hpop1. }
  { apply Hpop2. }
  { apply Hncall1. }
  { apply Hncall2. }
  intro Hhcheck.
  exploit Hhcheck; eauto;
    intros [alpha' [li1' [li2' [Hincr [Hiboth [Hli1 [Hli2 Heach2]]]]]]].
  exists alpha'; exists li1'; exists li2'.
  split; [done|].
  clear Hhcheck Heach1.

  (* B. remove_old / new_to_old *)
  exploit oldnew_preserves_hint_sem_each.
  { apply Hstep1. }
  { apply Hstep2. }
  { apply Hpop1. }
  { apply Hpop2. }
  { apply Hncall1. }
  { apply Hncall2. }
  intro Holdnew.
  exploit Holdnew; eauto; intros Heach3; clear Holdnew Heach2.

  (* C. maydiff_update *)
  exploit maydiff_update_preserves_hint_sem_each.
  { apply Hstep1. }
  { apply Hstep2. }
  { apply Hpop1. }
  { apply Hpop2. }
  { apply Hncall1. }
  { apply Hncall2. }
  intro Hmaydiff.
  exploit Hmaydiff; eauto; intro Heach4; clear Hmaydiff Heach3.

  (* F. add_neq *)
  exploit add_neq_preserves_hint_sem_each.
  { apply Hstep1. }
  { apply Hstep2. }
  { apply Hpop1. }
  { apply Hpop2. }
  { apply Hncall1. }
  { apply Hncall2. }
  intro Haddneq.
  exploit Haddneq; eauto; intro Heach5; clear Haddneq Heach4.

  (* D. filter_eq *)
  exploit filter_eq_heap_preserves_hint_sem_each.
  { apply Hstep1. }
  { apply Hstep2. }
  { apply Hpop1. }
  { apply Hpop2. }
  { apply Hncall1. }
  { apply Hncall2. }
  intro Hhfilter.
  exploit Hhfilter; eauto; intro Heach6; clear Hhfilter Heach5.

  (* E. add_cmd *)
  exploit add_cmd_preserves_hint_sem_each.
  { apply Hstep1. }
  { apply Hstep2. }
  { apply Hpop1. }
  { apply Hpop2. }
  { apply Hncall1. }
  { apply Hncall2. }
  intro Haddcmd.
  exploit Haddcmd; eauto.
  { inv Hvmem; apply Hwf. }
  intro HeachF; clear Haddcmd Heach6.

  (* Done! *)
  eapply hint_sem_each_implies_hint_sem_insn; eauto. *)
Qed.
