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
      (mkState ec1 ecs1 mem1) (mkState ec1' ecs1' mem1')
      ns1 ns1' na1' tr)
    (Hstep2: logical_semantic_step cfg2 fn_al2
      (mkState ec2 ecs2 mem2) (mkState ec2' ecs2' mem2')
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

  Ltac des_same_cmd_tac :=
    repeat match goal with
             | [H: true = is_same_cmd _ _ _ _ _ |- _] =>
               move H at bottom; unfold is_same_cmd in H
             | [H: true = _ && _ |- _] =>
               let Hsamel := fresh "Hsame" in
                 let Hsamer := fresh "Hsame" in
                   apply andb_true_eq in H; destruct H as [Hsamel Hsamer]
             | [H: _ @ _ |- _] =>
               let Heq := fresh in
               inversion H as [Heq]; rewrite Heq in *; clear H Heq
             | [H: _ @@ _ |- _] =>
               apply dos_in_list_gvs_inv in H; rewrite H in *
           end.

  Lemma maydiff_update_preserves_hint_sem_each:
    forall inv1 inv2 iso1 iso2 alpha' gmax md md'
      (Hmd': md' = maydiff_update_opt md inv1 inv2 ocmd1 ocmd2)
      (Hsu1: self_use_check ocmd1 = true)
      (Hsu2: self_use_check ocmd2 = true)

      (Hsem: (vars_aux.is_defined_same_id ocmd1 ocmd2 = false /\
        (hint_sem_each
          (maydiff_add_def_all_opt (maydiff_add_def_all_opt md ocmd1) ocmd2)
          inv1 inv2 iso1 iso2
          alpha' gmax cfg1 cfg2 r1' r2' mem1 mem2
          li1 pi1 li2 pi2 als1' als2' mem1' mem2')) \/
      (vars_aux.is_defined_same_id ocmd1 ocmd2 = true /\
        (hint_sem_each
          (maydiff_add_def_new_opt (maydiff_add_def_new_opt md ocmd1) ocmd2)
          inv1 inv2 iso1 iso2
          alpha' gmax cfg1 cfg2 r1' r2' mem1 mem2
          li1 pi1 li2 pi2 als1' als2' mem1' mem2')))
      (Halpha: forall aid,
        na1' = ret aid -> na2' = ret aid -> alpha_incr_both alpha' mem1 mem2),

      (hint_sem_each md' inv1 inv2 iso1 iso2
        alpha' gmax cfg1 cfg2 r1' r2' mem1 mem2
        li1 pi1 li2 pi2 als1' als2' mem1' mem2').
  Proof.
    intros; subst.
    destruct Hsem as [[Hndef Hsem]|[Hdef Hsem]].

    Case "1. is_defined_same_id = false".
    destruct Hsem as [Hmi Hiav]; split; [|done]; clear Hiav.
    destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
    destruct ocmd1 as [cmd1|]; destruct ocmd2 as [cmd2|];
      try by simpl; simpl in Hmd; exists olc1; exists olc2.
      
    remember (is_same_cmd md inv1 inv2 cmd1 cmd2) as bsame; destruct bsame.
    { exists olc1; exists olc2; split; [|done].
      simpl; simpl in Hmd.
      unfold maydiff_update_opt, maydiff_update.
      rewrite <- Heqbsame.
      destruct cmd1, cmd2; try done;
      try (des_same_cmd_tac;
        destruct (id_dec id5 id0); try done; subst;
        unfold vars_aux.is_defined_same_id in Hndef; simpl in Hndef;
        destruct (AtomSetImpl.eq_dec (singleton id0) (singleton id0)) as [|Hcontr];
        try done; elim Hcontr; done).
    }
    { exists olc1; exists olc2; split; [|done].
      unfold maydiff_update_opt, maydiff_update.
      rewrite <- Heqbsame.
      destruct (vars_aux.is_defined_same_id (ret cmd1) (ret cmd2)); done.
    }

    Case "2. is_defined_same_id = true".
    destruct ocmd1 as [cmd1|]; destruct ocmd2 as [cmd2|]; try done.

    Focus 2. (* not a mainstream proof: left-nop *)
    { unfold vars_aux.is_defined_same_id in Hdef; simpl in Hdef.
      simpl in *.
      destruct Hsem as [Hmi Hiav]; split; [|done]; clear Hiav.
      destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
      exists olc1; exists olc2; split; [|done].
      unfold maydiff_sem in *; intros x Hnmem.
      apply Hmd.
      unfold maydiff_add_def_new; unfold maydiff_add_def_all in Hnmem.
      destruct (vars_aux.def_cmd cmd1); try done.
      rewrite IdExtSetFacts.add_b.
      repeat rewrite IdExtSetFacts.add_b in Hnmem.
      apply orb_false_iff in Hnmem; destruct Hnmem as [_ Hnmem].
      apply orb_false_iff in Hnmem; destruct Hnmem as [Hieq Hnmem].
      apply orb_false_iff; split; done.
    }
    Unfocus.

    Focus 2. (* not a mainstream prof: right-nop *)
    { unfold vars_aux.is_defined_same_id in Hdef; simpl in Hdef.
      simpl in *.
      destruct Hsem as [Hmi Hiav]; split; [|done]; clear Hiav.
      destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
      exists olc1; exists olc2; split; [|done].
      unfold maydiff_sem in *; intros x Hnmem.
      apply Hmd.
      unfold maydiff_add_def_new; unfold maydiff_add_def_all in Hnmem.
      destruct (vars_aux.def_cmd cmd2); try done.
      rewrite IdExtSetFacts.add_b.
      repeat rewrite IdExtSetFacts.add_b in Hnmem.
      apply orb_false_iff in Hnmem; destruct Hnmem as [_ Hnmem].
      apply orb_false_iff in Hnmem; destruct Hnmem as [Hieq Hnmem].
      apply orb_false_iff; split; done.
    }
    Unfocus.

    simpl; simpl in Hsem.
    unfold maydiff_update.
    remember (is_same_cmd md inv1 inv2 cmd1 cmd2) as bsame.
    destruct bsame.

    Focus 2. (* not a mainstream proof: is_same_cmd = false *)
    { rewrite Hdef.
      destruct Hsem as [Hmi Hiav]; split; [|done]; clear Hiav.
      destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
      exists olc1; exists olc2; split; [|done].
      unfold vars_aux.is_defined_same_id in Hdef; simpl in Hdef.
      unfold maydiff_add_def_new in *.
      destruct (vars_aux.def_cmd cmd2); try done.
      destruct (vars_aux.def_cmd cmd1).

      - assert (Hieq: i0 = i1).
        { clear -Hdef; unfold vgtac.is_true in Hdef.
          destruct (AtomSetImpl.eq_dec (singleton i1) (singleton i0)) as [Heq|];
            try done.
          unfold AtomSetImpl.eq, AtomSetImpl.Equal in Heq.
          destruct (Heq i0) as [_ Hieq].
          exploit Hieq; rewrite AtomSetFacts.singleton_iff; done.
        }
        subst.
        clear -Hmd; unfold maydiff_sem in *.
        intros x Hnmem; apply Hmd.
        repeat rewrite IdExtSetFacts.add_b.
        rewrite IdExtSetFacts.add_b in Hnmem.
        apply orb_false_iff in Hnmem; destruct Hnmem as [Hieq Hnmem].
        apply orb_false_iff; split; try done.
        apply orb_false_iff; split; done.

      - elimtype False; clear -Hdef; unfold vgtac.is_true in Hdef.
        destruct (AtomSetImpl.eq_dec empty (singleton i0)) as [Heq|]; try done.
        unfold AtomSetImpl.eq, AtomSetImpl.Equal in Heq.
        destruct (Heq i0) as [_ Hcontr]. 
        exploit Hcontr.
        rewrite AtomSetFacts.singleton_iff; done.
        apply AtomSetFacts.empty_iff.
    }
    Unfocus.

    destruct Hsem as [Hmi Hiav]; split; [|done].
    inversion Hiav as [Hals [Hgl [Hva Hvm]]].
    destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
    exists olc1; exists olc2; split; [|done].

    unfold maydiff_add_def_new in Hmd.
    remember (vars_aux.def_cmd cmd1) as cmd1d; destruct cmd1d as [cid1|p1];
      remember (vars_aux.def_cmd cmd2) as cmd2d; destruct cmd2d as [cid2|p2];
        [|by destruct cmd1, cmd2|by destruct cmd1, cmd2|done].
    
    assert (cid1 = cid2) as Heqcid.
    { destruct cmd1, cmd2; try done;
      try by
        simpl in Heqcmd1d, Heqcmd2d;
          inversion Heqcmd1d; inversion Heqcmd2d; subst;
            unfold is_same_cmd in Heqbsame;
              symmetry in Heqbsame; repeat rewrite andb_true_iff in Heqbsame;
                des; destruct (id_dec id5 id0); done.
    }
    subst.

    unfold maydiff_sem in *; intros x Hxnmem.
    destruct (id_ext_dec x (vars_aux.add_ntag cid2));
      [|by apply Hmd; repeat (rewrite IdExtSetFacts.add_neq_b; try auto)]. admit. (*

    unfold r1', r2' in *.
    hexploit pop_state_ocmd_some_implies_logical_step_real_step; try eapply Hpop1.
    apply Hstep1. intro Hrstep1.
    hexploit pop_state_ocmd_some_implies_logical_step_real_step; try eapply Hpop2.
    apply Hstep2. intro Hrstep2.
    move Hpop1 at bottom; move Hpop2 at bottom.
    destruct ec1, ec2; simpl in Hpop1, Hpop2.
    destruct ns1, ns2; try done.
    destruct CurCmds0;
      [by unfold pop_one_X in Hpop1; destruct (noop_idx_zero_exists n) in Hpop1|].
    destruct CurCmds1;
      [by unfold pop_one_X in Hpop2; destruct (noop_idx_zero_exists n1) in Hpop2|].
    assert (Hceq1: c = cmd1).
    { unfold pop_one_X in Hpop1; destruct (noop_idx_zero_exists n) in Hpop1;
      inversion Hpop1; done.
    }
    assert (Hceq2: c0 = cmd2).
    { unfold pop_one_X in Hpop2; destruct (noop_idx_zero_exists n1) in Hpop2;
      inversion Hpop2; done.
    }
    subst.

    inversion Hvm.
    destruct cmd1, cmd2; try done;
    unfold vars_aux.def_cmd in Heqcmd1d; inversion Heqcmd1d; subst; clear Heqcmd1d;
    unfold vars_aux.def_cmd in Heqcmd2d; inversion Heqcmd2d; subst; clear Heqcmd2d;
    try by elim (Hncall1 id0).

    (* BOP *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (sz_dec sz5 sz0) as [Heqsz'|]; try done; rewrite Heqsz' in *.
      destruct (bop_dec bop5 bop0) as [Heqbop'|]; try done; rewrite Heqbop' in *.
      eapply BOP_eq_check_value_implies_injection
        with (lv1:=value1) (rv1:=value2) (lv2:=value0) (rv2:=value3); eauto.

    (* FBOP *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (floating_point_dec floating_point5 floating_point0)
        as [Heqfp'|]; try done; rewrite Heqfp' in *.
      destruct (fbop_dec fbop5 fbop0) as [Heqbop'|]; try done; rewrite Heqbop' in *.
      eapply FBOP_eq_check_value_implies_injection
        with (lv1:=value1) (rv1:=value2) (lv2:=value0) (rv2:=value3); eauto.

    (* EXTRACTVALUE *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (typ_dec typ5 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (list_const_dec l0 l1) as [Heqlc'|]; try done; rewrite Heqlc' in *.
      destruct (typ_dec typ' typ'0) as [Heqtyp''|]; try done; rewrite Heqtyp'' in *.
      eapply EXTRACTVALUE_eq_check_value_implies_injection
        with (v1:=value5) (v2:=value0); eauto.

    (* INSERTVALUE *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (typ_dec typ5 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (typ_dec typ' typ'0) as [Heqtyp''|]; try done; rewrite Heqtyp'' in *.
      destruct (list_const_dec l0 l1) as [Heqlc'|]; try done; rewrite Heqlc' in *.
      eapply INSERTVALUE_eq_check_value_implies_injection
        with (lv1:=value5) (rv1:=value') (lv2:=value0) (rv2:=value'0); eauto.

    (* MALLOC *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (typ_dec typ5 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (align_dec align5 align0) as [Heqaln'|]; try done; rewrite Heqaln' in *.

      clear H13; clear H34; inv Hstep1.
      inv Hpn; inv Hpop;
      simpl in Hec; inv Hec;
      simpl in Hpop0; rewrite Hpop0 in Hpop1; [|done].
      rewrite <- Hpop1 in Halpha.

      inv Hstep2.
      inv Hpn; inv Hpop;
      simpl in Hec; inv Hec;
      simpl in Hpop1; rewrite Hpop1 in Hpop2; [|done].
      rewrite <- Hpop2 in Halpha.

      exploit (Halpha id0); try done.
      intro Hres.

      exploit memory_props.MemProps.malloc_result; try eapply H19; eauto; intro Hmb1.
      exploit memory_props.MemProps.malloc_result; try eapply H40; eauto; intro Hmb2.
      unfold alpha_incr_both in Hres.
      rewrite <- Hmb1, <- Hmb2 in Hres.
      repeat rewrite memory_props.simpl_blk2GV.
      repeat econstructor; eauto.

    (* ALLOCA *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (typ_dec typ5 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (align_dec align5 align0) as [Heqaln'|]; try done; rewrite Heqaln' in *.

      clear H13; clear H34; inv Hstep1.
      inv Hpn; inv Hpop;
      simpl in Hec; inv Hec;
      simpl in Hpop0; rewrite Hpop0 in Hpop1; [|done].
      rewrite <- Hpop1 in Halpha.

      inv Hstep2.
      inv Hpn; inv Hpop;
      simpl in Hec; inv Hec;
      simpl in Hpop1; rewrite Hpop1 in Hpop2; [|done].
      rewrite <- Hpop2 in Halpha.

      exploit (Halpha id0); try done.
      intro Hres.

      exploit memory_props.MemProps.malloc_result; try eapply H19; eauto; intro Hmb1.
      exploit memory_props.MemProps.malloc_result; try eapply H40; eauto; intro Hmb2.
      unfold alpha_incr_both in Hres.
      rewrite <- Hmb1, <- Hmb2 in Hres.
      repeat rewrite memory_props.simpl_blk2GV.
      repeat econstructor; eauto.

    (* LOAD *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (typ_dec typ5 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (align_dec align5 align0) as [Heqaln'|]; try done; rewrite Heqaln' in *.
      eapply LOAD_eq_check_value_implies_injection
        with (v1:=value1) (v2:=value0); eauto.

    (* GEP *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (inbounds_dec inbounds5 inbounds0) as [Heqinb'|];
        try done; rewrite Heqinb' in *.
      destruct (typ_dec typ5 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (typ_dec typ' typ'0) as [Heqtyp''|]; try done; rewrite Heqtyp'' in *.
      eapply GEP_eq_check_value_implies_injection
        with (v1:=value_5) (v2:=value_0); eauto.

    (* TRUNC *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (truncop_dec truncop5 truncop0) as [Heqtrc'|];
        try done; rewrite Heqtrc' in *.
      destruct (typ_dec typ1 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (typ_dec typ2 typ3) as [Heqtyp''|]; try done; rewrite Heqtyp'' in *.
      eapply TRUNC_eq_check_value_implies_injection
        with (v1:=value1) (v2:=value0); eauto.

    (* EXT *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (extop_dec extop5 extop0) as [Heqext'|]; try done; rewrite Heqext' in *.
      destruct (typ_dec typ1 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (typ_dec typ2 typ3) as [Heqtyp''|]; try done; rewrite Heqtyp'' in *.
      eapply EXT_eq_check_value_implies_injection
        with (v1:=value5) (v2:=value0); eauto.

    (* CAST *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (castop_dec castop5 castop0) as [Heqext'|];
        try done; rewrite Heqext' in *.
      destruct (typ_dec typ1 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      destruct (typ_dec typ2 typ3) as [Heqtyp''|]; try done; rewrite Heqtyp'' in *.
      eapply CAST_eq_check_value_implies_injection
        with (v1:=value1) (v2:=value0); eauto.

    (* ICMP *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (cond_dec cond5 cond0) as [Heqcond'|]; try done; rewrite Heqcond' in *.
      destruct (typ_dec typ5 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      eapply ICMP_eq_check_value_implies_injection
        with (lv1:=value1) (rv1:=value2) (lv2:=value0) (rv2:=value3); eauto.

    (* FCMP *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (fcond_dec fcond5 fcond0) as [Heqcond'|]; try done; rewrite Heqcond' in *.
      destruct (floating_point_dec floating_point5 floating_point0) as [Heqfp'|];
        try done; rewrite Heqfp' in *.
      eapply FCMP_eq_check_value_implies_injection
        with (lv1:=value1) (rv1:=value2) (lv2:=value0) (rv2:=value3); eauto.

    (* SELECT *)
    - inversion Hrstep1; inversion Hrstep2; subst; simpl; simpl in Hmd.
      simpl in Heqtd; rewrite Heqtd in *; clear Heqtd.
      unfold variable_equivalent; s.
      repeat rewrite lookupAL_updateAddAL_eq.
      des_same_cmd_tac.

      destruct (typ_dec typ5 typ0) as [Heqtyp'|]; try done; rewrite Heqtyp' in *.
      eapply SELECT_eq_check_value_implies_injection
        with (cv1:=value0) (lv1:=value1) (rv1:=value2)
          (cv2:=value3) (lv2:=value4) (rv2:=value5); eauto. *)
  Qed.

End HintSemEach.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)

