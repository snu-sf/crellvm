Require Import vgtac.
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

Require Import FSetFacts.

Import Opsem.
Import syntax_ext.
Import hints.

Section HintSemEach.

  Variable
    (cfg1 cfg2: Config) (fn_al1 fn_al2: AssocList noop_t)
    (ec1 ec1' ec2 ec2': @ExecutionContext DGVs)
    (ecs1 ecs1' ecs2 ecs2': @ECStack DGVs)
    (mem1 mem1' mem2 mem2': mem) (ns1 ns1' ns2 ns2': noop_stack_t)
    (na1' na2': new_alloca_t) (tr: trace) (li1 pi1 li2 pi2: list mblock)
    (ocmd1 ocmd2: option cmd).

  Hypothesis
    (Hstep1: logical_semantic_step cfg1 fn_al1
      (mkState (ec1::ecs1) mem1) (mkState (ec1'::ecs1') mem1')
      ns1 ns1' na1' tr)
    (Hstep2: logical_semantic_step cfg2 fn_al2
      (mkState (ec2::ecs2) mem2) (mkState (ec2'::ecs2') mem2')
      ns2 ns2' na2' tr)
    (Hpop1: pop_state_ocmd (ec1::ecs1) ns1 ocmd1)
    (Hpop2: pop_state_ocmd (ec2::ecs2) ns2 ocmd2)
    (Hncall1: forall rid, ~ is_general_call ocmd1 rid)
    (Hncall2: forall rid, ~ is_general_call ocmd2 rid)
    (Heqtd: CurTargetData cfg1 = CurTargetData cfg2).
  
  Definition r1 := Locals ec1.
  Definition r2 := Locals ec2.
  Definition r1' := Locals ec1'.
  Definition r2' := Locals ec2'.
  Definition als1 := Allocas ec1.
  Definition als2 := Allocas ec2.
  Definition als1' := Allocas ec1'.
  Definition als2' := Allocas ec2'.

  Lemma add_cmd_preserves_hint_sem_each_aux:
    forall cfg fn_al ec ec' ecs ecs' mem mem' alpha gmax ns ns' na' tr inv ocmd olc
      (Holdvm1: (forall b, b >= Mem.nextblock mem -> alpha b = merror) \/
        (forall b1 b2 delta2, alpha b1 = ret (b2, delta2) -> b2 < Mem.nextblock mem))
      (Holdvm2: forall b, b <= gmax -> alpha b = ret (b, 0))
      (Hstep: logical_semantic_step cfg fn_al
        {| ECS := ec :: ecs; Mem := mem |}
        {| ECS := ec' :: ecs'; Mem := mem' |} ns ns' na' tr)
      (Hpop: pop_state_ocmd (ec::ecs) ns ocmd)
      (Hncall: forall rid, ~ is_general_call ocmd rid)
      (Hsu: self_use_check ocmd = true)
      (Hinv : eqs_sem cfg olc (Locals ec') mem' gmax inv),
      eqs_sem cfg olc (Locals ec') mem' gmax
      (vars_aux.add_ntag_option_cmd_to_eqs inv ocmd).

  Proof.
    intros; simpl in Hinv.
    destruct ocmd as [cmd|]; try done.
    hexploit pop_state_ocmd_some_implies_logical_step_real_step; eauto.
    intro Hrstep.
    destruct ec; s in Hpop; destruct ns; [done|].
    destruct CurCmds0.
    { unfold pop_one_X in Hpop; destruct (noop_idx_zero_exists n) in Hpop; done.
    }
    assert (Hceq: c = cmd).
    { unfold pop_one_X in Hpop; destruct (noop_idx_zero_exists n) in Hpop;
      inversion Hpop; done.
    }
    subst.
    remember (pop_one_X (cmd::CurCmds0) n) as poX.
    destruct poX; try done.
    destruct Hinv as [Hinvreg [Hinvheap Hinvneq]].
    inversion Hrstep; subst; try done;
    try by r; splits; eauto;
      s; apply hint_sem_aux.eqs_eq_reg_sem_set_add; [done|];
      econs; try econs; s;
      eauto using lookupAL_updateAddAL_eq,
        BOP_implies_BOPEXT_new, self_use_check_preserves_BOP,
        FBOP_implies_FBOPEXT_new, self_use_check_preserves_FBOP,
        TRUNC_implies_TRUNCEXT_new, self_use_check_preserves_TRUNC,
        EXT_implies_EXTEXT_new, self_use_check_preserves_EXT,
        CAST_implies_CASTEXT_new, self_use_check_preserves_CAST,
        ICMP_implies_ICMPEXT_new, self_use_check_preserves_ICMP,
        FCMP_implies_FCMPEXT_new, self_use_check_preserves_FCMP,
        getOperandValue_implies_getOperandValueExt_new,
        values2GVs_implies_values2GVsExt_new,
        self_use_check_preserves_extractValue_getOperandValue,
        self_use_check_preserves_insertValue_getOperandValue_1,
        self_use_check_preserves_insertValue_getOperandValue_2,
        self_use_check_preserves_gep_getOperandValue_1,
        self_use_check_preserves_gep_getOperandValue_2.

    (* alloca *)
    - r; splits; eauto.
      s; apply hint_sem_aux.eqs_eq_reg_sem_set_add; [done|].
      exploit memory_props.MemProps.nextblock_malloc; eauto; intro Hfact1.
      exploit memory_props.MemProps.malloc_result; eauto; intro Hfact2.
      eapply eq_reg_sem_old_alloca; eauto.
      + s; rewrite lookupAL_updateAddAL_eq; eauto.
      + s; assert (Hmb: $ blk2GV TD mb # typ_pointer t $ = blk2GV TD mb) by done.
        rewrite Hmb; clear Hmb.
        s; reflexivity.
      + rewrite Hfact2, <-Hfact1; omega.
      + destruct (Z_lt_dec gmax mb); [done|].
        elimtype False.
        assert (mb <= gmax) by omega; assert (gmax >= mb) by omega; clear n1.
        rewrite Hfact2 in H, H0.
        move Holdvm1 at bottom. move Holdvm2 at bottom.
        exploit Holdvm2. instantiate (1:=gmax); omega. intro Hcontr2.
        destruct Holdvm1 as [Holdvm1|Holdvm1].
        * exploit Holdvm1; eauto; intro Hcontr1.
          rewrite Hcontr1 in Hcontr2; done.
        * exploit Holdvm1; eauto.

    (* load *)
    - r; splits; eauto.
      s; apply hint_sem_aux.eqs_eq_heap_sem_set_add; [done|].
      unfold eq_heap_sem; s.
      rewrite <- getOperandValue_equals_getOperandValueExt_new.
      erewrite <- self_use_check_preserves_load_getOperandValue; eauto.
      rewrite H13; erewrite lookupAL_updateAddAL_eq.
      intros mp0 Heqmp.
      inversion H14; inversion Heqmp; subst; subst.
      by rewrite H15.

    (* store *)
    - r; splits; eauto.
      s; apply hint_sem_aux.eqs_eq_heap_sem_set_add; [done|].
      unfold eq_heap_sem; s.
      rewrite <- getOperandValue_equals_getOperandValueExt_new.
      rewrite <- getOperandValue_equals_getOperandValueExt_new.
      rewrite H13, H14.
      intros mp0 Heqmp.
      inversion H15; inversion H16; inversion Heqmp; subst; subst.
      exploit mload_after_mstore_get_same_value; eauto.
      intros [gv2 [Hload Heqgvs]].
      rewrite Hload; done.

    (* select *)
    - r; splits; eauto.
      s; apply hint_sem_aux.eqs_eq_reg_sem_set_add; [done|].
      econs.
      + instantiate (1:= if (isGVZero TD c) then gvs2 else gvs1).
        destruct (isGVZero TD c); s; eapply lookupAL_updateAddAL_eq; eauto.
      + instantiate (1:= if (isGVZero TD c) then gvs2 else gvs1).
        remember (isGVZero TD c) as cz; destruct cz.
        * eapply rhs_ext_select_false_sem; eauto; s;
          try apply getOperandValue_implies_getOperandValueExt_new; try done.
          erewrite <- self_use_check_preserves_select_getOperandValue_1; eauto.
          erewrite <- self_use_check_preserves_select_getOperandValue_3; eauto.
        * eapply rhs_ext_select_true_sem; eauto; s;
          try apply getOperandValue_implies_getOperandValueExt_new; try done.
          erewrite <- self_use_check_preserves_select_getOperandValue_1; eauto.
          erewrite <- self_use_check_preserves_select_getOperandValue_2; eauto.
      + done.
  Qed.

  Lemma register_iso_preserves_isolated_sem_1:
    forall olc1 iso1
      (Hli1: li_incr_1 li1 mem1 ocmd1 ocmd2)
      (Hiso1: isolated_sem (CurTargetData cfg1) olc1 r1' li1 iso1),
      isolated_sem (CurTargetData cfg1) olc1 r1' li1
      (register_isolated_pointers_orig ocmd1 ocmd2 iso1).
  Proof.
    intros.
    unfold r1' in *.
    destruct ocmd1 as [cmd1|]; try done.
    destruct_lstep_tac.
    destruct cmd1; try done.
    destruct_step_tac.
    destruct ocmd2 as [cmd2|]; try done.

    move Hiso1 at bottom.
    unfold isolated_sem in *.
    unfold IdExtSetImpl.For_all in *; intros x Hx.
    apply IdExtSetFacts.add_iff in Hx.
    destruct Hx as [Hx|Hx]; [|by eapply Hiso1; eauto].

    subst x; right.
    inv Hstep.
    exists (blk2GV TD mb); split; simpl in *.
    - rewrite lookupAL_updateAddAL_eq; eauto.
    - hexploit memory_props.MemProps.malloc_result; eauto; intro; subst mb; done.
  Qed.

  Lemma register_iso_preserves_isolated_sem_2:
    forall olc2 iso2
      (Hli2: li_incr_2 li2 mem2 ocmd1 ocmd2)
      (Hiso2: isolated_sem (CurTargetData cfg2) olc2 r2' li2 iso2),
      isolated_sem (CurTargetData cfg2) olc2 r2' li2
      (register_isolated_pointers_opt ocmd1 ocmd2 iso2).
  Proof.
    intros.
    unfold r2' in *.
    destruct ocmd2 as [cmd2|]; [|by destruct ocmd1].
    destruct_lstep_tac.
    destruct ocmd1 as [cmd1|]; try done.
    destruct cmd2; try done.
    destruct_step_tac.

    move Hiso2 at bottom.
    unfold isolated_sem in *.
    unfold IdExtSetImpl.For_all in *; intros x Hx.
    apply IdExtSetFacts.add_iff in Hx.
    destruct Hx as [Hx|Hx]; [|by eapply Hiso2; eauto].

    subst x; right.
    inv Hstep.
    exists (blk2GV TD mb); split; simpl in *.
    - rewrite lookupAL_updateAddAL_eq; eauto.
    - hexploit memory_props.MemProps.malloc_result; eauto; intro; subst mb; done.
  Qed.

  Lemma add_cmd_preserves_hint_sem_each:
    forall md iso1 iso2 alpha alpha' inv1 inv2 gmax
      (Holdmwf: wf_sb_mi gmax alpha mem1 mem2)

      (Hsu1: self_use_check ocmd1 = true)
      (Hsu2: self_use_check ocmd2 = true)
      (Hli1: li_incr_1 li1 mem1 ocmd1 ocmd2)
      (Hli2: li_incr_2 li2 mem2 ocmd1 ocmd2)

      (Hsem: hint_sem_each md inv1 inv2 iso1 iso2
        alpha' gmax cfg1 cfg2 r1' r2' mem1' mem2'
        li1 pi1 li2 pi2 als1' als2' mem1' mem2'),

      (hint_sem_each md 
        (vars_aux.add_ntag_option_cmd_to_eqs inv1 ocmd1)
        (vars_aux.add_ntag_option_cmd_to_eqs inv2 ocmd2)
        (register_isolated_pointers_orig ocmd1 ocmd2 iso1)
        (register_isolated_pointers_opt ocmd1 ocmd2 iso2)
        alpha' gmax cfg1 cfg2 r1' r2' mem1' mem2'
        li1 pi1 li2 pi2 als1' als2' mem1' mem2').
  Proof.
    intros.
    destruct Hsem as [[olc1 [olc2 [Hmd [Hinv1 [Hinv2 [Hiso1 Hiso2]]]]]] Hiav].
    split; try done; clear Hiav.
    exists olc1; exists olc2; split; try done.
    inv Holdmwf; rr; splits; try done; simpl in *.
    - eapply add_cmd_preserves_hint_sem_each_aux; try apply Hstep1; eauto.
    - eapply add_cmd_preserves_hint_sem_each_aux; try (right; apply Hmap2); eauto.
    - eapply register_iso_preserves_isolated_sem_1; eauto.
    - eapply register_iso_preserves_isolated_sem_2; eauto.
  Qed.

End HintSemEach.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
