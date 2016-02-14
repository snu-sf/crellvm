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

Lemma heap_eq_check_preserves_hint_sem_each:
  forall 
    (cfg1 cfg2: Config) (fn_al1 fn_al2: AssocList noop_t)
    (ec1 ec1' ec2 ec2': @ExecutionContext DGVs)
    (ecs1 ecs1' ecs2 ecs2': @ECStack DGVs)
    (mem1 mem1' mem2 mem2': mem) (ns1 ns1' ns2 ns2': noop_stack_t)
    (na1' na2': new_alloca_t) (tr: trace) (li1 pi1 li2 pi2: list mblock)
    (ocmd1 ocmd2: option cmd)
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
  
    (Heqtd: CurTargetData cfg1 = CurTargetData cfg2)
    
    iso1 iso2 alpha gmax md inv1 inv2
    
    (Hheq: heap_eq_check md inv1 inv2 iso1 iso2 ocmd1 ocmd2)
    (Hsem: hint_sem_each md inv1 inv2 iso1 iso2
      alpha gmax cfg1 cfg2 (Locals ec1) (Locals ec2) mem1 mem2
      li1 pi1 li2 pi2 (Allocas ec1) (Allocas ec2) mem1 mem2),
    
    exists alpha', exists li1', exists li2',
      (inject_incr' alpha alpha' li1 pi1 li2 pi2) /\
      (forall aid, na1' = ret aid -> na2' = ret aid ->
        alpha_incr_both alpha' mem1 mem2) /\
      (li_incr_1 li1' mem1 ocmd1 ocmd2) /\
      (li_incr_2 li2' mem2 ocmd1 ocmd2) /\
      (hint_sem_each md inv1 inv2 iso1 iso2
        alpha' gmax cfg1 cfg2 (Locals ec1) (Locals ec2) mem1 mem2
        li1' pi1 li2' pi2 (Allocas ec1') (Allocas ec2') mem1' mem2').

Proof.
  intros. admit. (*
  destruct Hsem as [Hmi [Hals [Hgl [Hva Hvm]]]].
  remember (is_alloca_or_malloc ocmd1) as is_aom1; destruct is_aom1.

  Case "1. left allocates".
  remember (is_alloca_or_malloc ocmd2) as is_aom2; destruct is_aom2.

  SCase "1.1. left and right both allocate".
  destruct ocmd1 as [cmd1|]; try done; destruct_lstep_tac.
  destruct ocmd2 as [cmd2|]; try done; destruct_lstep_tac.
  destruct cmd1, cmd2; try done.

  SSCase "1.1.1. malloc-malloc case".
  destruct_step_tac; inv Hstep; inv Hstep0.
  simpl in Heqtd; inv Heqtd.

  move Hheq at bottom.
  apply andb_true_iff in Hheq. destruct Hheq as [Hheq Halneq].
  apply andb_true_iff in Hheq. destruct Hheq as [Hheq Hveq].
  apply andb_true_iff in Hheq. destruct Hheq as [Hideq Htypeq].
  destruct (id_dec id5 id0); try done; subst.
  destruct (typ_dec typ5 typ0); try done; subst.
  destruct (align_dec align5 align0); try done; subst.

  assert (Heqtsz: tsz = tsz0) by (rewrite H4 in H21; inv H21; done); subst.
  assert (Heqgn: gv_inject alpha gn gn0).
  { destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
    eapply eq_check_value_prop; eauto.
    + by inv Hvm.
    + by simpl; inv H23; destruct value5.
    + by simpl; inv H26; destruct value0.
  }
  exploit malloc_preserves_valid_memories.
  { apply H24. }
  { apply H27. }
  { apply Heqgn. }
  { apply Hvm. }
  intros [alpha' [Hincr [Hinj Hvmem']]].
  exists alpha'; exists li1; exists li2; splits; try done.

  rr; split.
  { eapply alpha_incr_preserves_hint_sem_each_md_inv; eauto. }
  { rr; splits; try done.
    + eapply alpha_incr_preserves_allocas_equivalent; eauto.
    + eapply alpha_incr_preserves_globals_equivalent; eauto.
    + eapply malloc_preserves_valid_allocas_1; eauto.
  }
    
  SSCase "1.1.2. alloca-alloca case".
  destruct_step_tac; inv Hstep; inv Hstep0.
  simpl in Heqtd; inv Heqtd.

  move Hheq at bottom.
  apply andb_true_iff in Hheq. destruct Hheq as [Hheq Halneq].
  apply andb_true_iff in Hheq. destruct Hheq as [Hheq Hveq].
  apply andb_true_iff in Hheq. destruct Hheq as [Hideq Htypeq].
  destruct (id_dec id5 id0); try done; subst.
  destruct (typ_dec typ5 typ0); try done; subst.
  destruct (align_dec align5 align0); try done; subst.

  assert (Heqtsz: tsz = tsz0) by (rewrite H4 in H21; inv H21; done); subst.
  assert (Heqgn: gv_inject alpha gn gn0).
  { destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
    eapply eq_check_value_prop; eauto.
    + by inv Hvm.
    + by simpl; inv H23; destruct value5.
    + by simpl; inv H26; destruct value0.
  }
    
  exploit malloc_preserves_valid_memories.
  { apply H24. }
  { apply H27. }
  { apply Heqgn. }
  { apply Hvm. }
  intros [alpha' [Hincr [Hinj Hvmem']]].
  exists alpha'; exists li1; exists li2; splits; try done.

  { rr; split.
    - eapply alpha_incr_preserves_hint_sem_each_md_inv; eauto.
    - rr; splits; try done.
      + hexploit memory_props.MemProps.malloc_result; try eapply H24; intro Hmb1.
        hexploit memory_props.MemProps.malloc_result; try eapply H27; intro Hmb2.
        eapply allocas_equivalent_map; eauto; try by subst.
        intro Hcontr; inv Hvmem'; pose (Hli1none _ Hcontr) as Hcontr'.
        unfold alpha_incr_both in Hinj; rewrite Hcontr' in Hinj; done.
        intro Hcontr; inv Hvmem'; pose (Hli2none _ Hcontr) as Hcontr'.
        unfold alpha_incr_both in Hinj; elim (Hcontr' (Mem.nextblock mem1)); done.
        eapply alpha_incr_preserves_allocas_equivalent; eauto.
      + eapply alpha_incr_preserves_globals_equivalent; eauto.
      + eapply malloc_preserves_valid_allocas_2; eauto.
  }

  SCase "1.2. only left allocates".
  destruct ocmd1 as [cmd1|]; try done; destruct_lstep_tac.
  destruct ocmd2 as [cmd2|]; try done; destruct_lstep_tac;
    try (destruct cmd1, cmd2; done; fail).
  destruct cmd1; try done; destruct_step_tac; inv Hstep.
  destruct Hstep0 as [Hstep0 _]; inv Hstep0.

  exploit malloc_left_preserves_valid_memories.
  { apply H24. }
  { apply Hvm. }
  intros [alpha' [Hincr Hvmem']].
  exists alpha'; exists (mb::li1); exists li2; splits;
    [done|by intros; rewrite <- Heqpop0 in Hpop1; inv Hpop1; inv H0|
      hexploit memory_props.MemProps.malloc_result; eauto; intro; subst mb; left; done|
      done|].

  { rr; split.
    - eapply li1_incr_preserves_hint_sem_each_md_inv; eauto.
      eapply alpha_incr_preserves_hint_sem_each_md_inv; eauto.
    - rr; splits; try done.
      + eapply allocas_equivalent_ignore_left; eauto; [by left|].
        eapply li1_incr_preserves_allocas_equivalent; eauto.
        * intros Hcontr; hexploit memory_props.MemProps.malloc_result; eauto.
          intro Hmb1; subst; destruct Hva as [Hva _].
          rewrite Forall_forall in Hva.
          pose (Hva _ Hcontr); omega.
        * eapply alpha_incr_preserves_allocas_equivalent; eauto.
      + eapply alpha_incr_preserves_globals_equivalent; eauto.
      + eapply malloc_left_preserves_valid_allocas; eauto.
  }

  Case "2. left does not allocate".
  remember (is_alloca_or_malloc ocmd2) as is_aom2; destruct is_aom2.

  SCase "2.1. only right allocates".
  destruct ocmd2 as [cmd2|]; try done; destruct_lstep_tac.
  destruct ocmd1 as [cmd1|]; try done; destruct_lstep_tac;
    try (destruct cmd2, cmd1; done; fail).
  destruct cmd2; try done; destruct_step_tac; inv Hstep.
  destruct Hstep0 as [Hstep0 _]; inv Hstep0.

  exploit malloc_right_preserves_valid_memories.
  { apply H24. }
  { apply Hvm. }
  intros [alpha' [Hincr Hvmem']].
  exists alpha'; exists li1; exists (mb::li2); splits;
    [done|by intros; rewrite <- Heqpop0 in Hpop1; inv Hpop1; inv H0|done|
      hexploit memory_props.MemProps.malloc_result; eauto; intro; subst mb; left; done|].

  { rr; split.
    - eapply li2_incr_preserves_hint_sem_each_md_inv; eauto.
      eapply alpha_incr_preserves_hint_sem_each_md_inv; eauto.
    - rr; splits; try done.
      + eapply allocas_equivalent_ignore_right; eauto; [by left|].
        eapply li2_incr_preserves_allocas_equivalent; eauto.
        intros Hcontr; hexploit memory_props.MemProps.malloc_result; eauto.
        intro Hmb2; subst; destruct Hva as [_ [Hva _]].
        rewrite Forall_forall in Hva.
        pose (Hva _ Hcontr); omega.
        eapply alpha_incr_preserves_allocas_equivalent; eauto.
      + eapply alpha_incr_preserves_globals_equivalent; eauto.
      + eapply malloc_right_preserves_valid_allocas; eauto.
  }

  SCase "2.2. both do not allocate".
  exists alpha; exists li1; exists li2.
  splits; try done.

  SSCase "2.2.1. alpha_incr_both: in this case, hypothesis is false".
  destruct ocmd1 as [cmd1|]; destruct_lstep_tac.
  destruct cmd1; try done; destruct_step_tac;
    try (unfold pop_one_X in Hpop0; destruct (noop_idx_zero_exists hpn);
      inv Hpop0; done; fail).

  SSCase "2.2.2. li_incr_1".
  destruct ocmd1 as [cmd1|]; try done.
  destruct ocmd2 as [cmd2|]; destruct cmd1; done.

  SSCase "2.2.3. li_incr_2".
  destruct ocmd1 as [cmd1|]; try done.
  destruct ocmd2 as [cmd2|]; try done.
  destruct cmd2; done.

  SSCase "2.2.4. hint_sem_each".
  assert (Allocas ec1' = Allocas ec1) as Heqals1.
  { destruct ocmd1 as [cmd1|].
    + destruct cmd1; try done; destruct_lstep_tac; destruct_step_tac.
      by elim (Hncall1 id5).
    + by destruct_lstep_tac; destruct Hstep as [Heceq _]; inv Heceq.
  }

  assert (Allocas ec2' = Allocas ec2) as Heqals2.
  { destruct ocmd2 as [cmd2|].
    + destruct_lstep_tac.
      destruct cmd2; try done; destruct_step_tac.
      by elim (Hncall2 id5).
    + destruct_lstep_tac.
      destruct Hstep as [Hstep _]; inv Hstep; done.
  }

  rr; split; try done.
  rr; splits; try done.

  SSSCase "2.2.2.1. allocas_equivalent".
  by rewrite Heqals1; rewrite Heqals2.

  SSSCase "2.2.2.2. valid_allocas".
  rewrite Heqals1; rewrite Heqals2.
  remember (is_free_or_store ocmd1) as Heqis_fos1; destruct Heqis_fos1.

  { destruct ocmd1 as [cmd1|]; [|done]; destruct_lstep_tac.
    destruct cmd1; try done; destruct_step_tac; inv Hstep.
    + destruct ocmd2 as [cmd2|]; [|done]; destruct_lstep_tac.
      destruct cmd2; try done. destruct_step_tac. inv Hstep.
      hexploit memory_props.MemProps.nextblock_free; try eapply H21; eauto.
      hexploit memory_props.MemProps.nextblock_free; try eapply H23; eauto.
      intros Hn2 Hn1.
      by unfold valid_allocas; rewrite <- Hn1, <- Hn2.
    + destruct ocmd2 as [cmd2|]; destruct_lstep_tac.
      * destruct cmd2; try done. destruct_step_tac. inv Hstep.
        hexploit memory_props.MemProps.nextblock_mstore; try eapply H25; eauto.
        hexploit memory_props.MemProps.nextblock_mstore; try eapply H29; eauto.
        intros Hn2 Hn1.
        by unfold valid_allocas; rewrite <- Hn1, <- Hn2.
      * destruct Hstep as [Hstep _]; inv Hstep.
        hexploit memory_props.MemProps.nextblock_mstore; try eapply H25; eauto.
        intros Hn1.
        by unfold valid_allocas; rewrite <- Hn1.
  }
  { assert (mem1 = mem1') as Heqmem1.
    { destruct ocmd1 as [cmd1|]; try done; destruct_lstep_tac.
      * destruct cmd1; try done; destruct_step_tac; try (by inv Hstep).
        by elim (Hncall1 id5).
      * by destruct Hstep as [Heceq _]; inv Heceq.
    }
    rewrite <- Heqmem1 in *; clear Heqmem1.
    assert (mem2 = mem2') as Heqmem2.
    { destruct ocmd2 as [cmd2|]; destruct_lstep_tac.
      * destruct cmd2; destruct_step_tac; try (by inv Hstep);
        try (by destruct ocmd1 as [cmd1|]; try done; destruct cmd1).
        by elim (Hncall2 id5).
      * by destruct Hstep as [Hstep _]; inv Hstep.
    }
    rewrite <- Heqmem2 in *; clear Heqmem2.
    done.
  }

  SSSCase "2.2.2.3. valid_memories".
  remember (is_free_or_store ocmd1) as Heqis_fos1; destruct Heqis_fos1.

  - destruct ocmd1 as [cmd1|]; [|done]; destruct_lstep_tac.
    destruct cmd1; try done.
    + destruct ocmd2 as [cmd2|]; [|done]. destruct_lstep_tac.
      destruct cmd2; try done. destruct_step_tac.
      inv Hstep; inv Hstep0.
      move Hheq at bottom.
      apply andb_true_iff in Hheq; destruct Hheq as [_ Hheq].
      destruct Hmi as [olc1 [olc2 [Hmdsem Hinvsem]]].
      assert (Hpinj: gv_inject alpha mptrs mptrs0).
      { eapply eq_check_value_prop; eauto.
          by inv Hvm.
          by unfold getOperandValueExt; destruct value5.
          by unfold getOperandValueExt; destruct value0.
      }
      repeat match goal with | [H: _ @ _ |- _] => inv H end.
      eapply free_preserves_valid_memories; eauto.

    + destruct ocmd2 as [cmd2|]; destruct_lstep_tac.
      * destruct cmd2; try done. destruct_step_tac.
        inv Hstep; inv Hstep0.
        move Hheq at bottom.
        apply andb_true_iff in Hheq; destruct Hheq as [Hheq Heqaln].
        destruct (align_dec align5 align0); try done; subst.
        apply andb_true_iff in Hheq; destruct Hheq as [Hheq Hisoc].
        apply andb_true_iff in Hheq; destruct Hheq as [Hheq Heqp].
        apply andb_true_iff in Hheq; destruct Hheq as [Heqtyp Heqv].
        destruct (typ_dec typ5 typ0); try done; subst.
        destruct Hmi as [olc1 [olc2 [Hmdsem Hinvsem]]].

        assert (Hpinj: gv_inject alpha mps2 mps0).
        { eapply eq_check_value_prop; eauto.
          by inv Hvm.
          by unfold getOperandValueExt; destruct value2.
          by unfold getOperandValueExt; destruct value3.
        }
        assert (Hvinj: gv_inject alpha gvs1 gvs0).
        { eapply eq_check_value_prop.
          apply Hmdsem. apply Hinvsem. apply Heqv. apply Heqtd.
          by inv Hvm; apply Hwf.
          by apply Hgl.
          by unfold getOperandValueExt; destruct value1.
          by unfold getOperandValueExt; destruct value0.
        }
        repeat match goal with | [H: _ @ _ |- _] => inv H end.
        simpl in Heqtd; subst TD.
        eapply mstore_preserves_valid_memories.
        apply Hvm. apply Hvinj. apply Hpinj. apply H25. apply H29.

      * destruct_step_tac.
        inv Hstep.
        destruct Hstep0 as [Hstep0 _]; inv Hstep0.
        move Hheq at bottom; simpl in Hheq.
        destruct Hmi as [olc1 [olc2 [Hmdsem Hinvsem]]].

        repeat match goal with | [H: _ @ _ |- _] => inv H end.
        destruct Hinvsem as [Hinv1 [Hinv2 [Hiso1 Hiso2]]].
        eapply mstore_left_preserves_valid_memories; eauto.

  - assert (mem1 = mem1') as Heqmem1.
    { destruct ocmd1 as [cmd1|]; try done; destruct_lstep_tac.
      * destruct cmd1; try done; destruct_step_tac; try (by inv Hstep).
        by elim (Hncall1 id5).
      * by destruct Hstep as [Heceq _]; inv Heceq.
    }
    rewrite <- Heqmem1 in *; clear Heqmem1.
    assert (mem2 = mem2') as Heqmem2.
    { destruct ocmd2 as [cmd2|]; destruct_lstep_tac.
      * destruct cmd2; destruct_step_tac; try (by inv Hstep);
        try (by destruct ocmd1 as [cmd1|]; try done; destruct cmd1).
        by elim (Hncall2 id5).
      * by destruct Hstep as [Hstep _]; inv Hstep.
    }
    rewrite <- Heqmem2 in *; clear Heqmem2.
    done. *)
Qed.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
