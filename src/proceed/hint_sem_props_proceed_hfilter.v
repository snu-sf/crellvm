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

Lemma logical_step_implies_mem_nextblock_incr_or_not:
  forall cfg fn_al ec ec' ecs ecs' mem mem' ns ns' na' tr ocmd
    (Hncall: forall rid, ~ is_general_call ocmd rid)
    (Hpop: pop_state_ocmd (ec::ecs) ns ocmd)
    (Hstep: logical_semantic_step cfg fn_al
      {| EC := ec; ECS := ecs; Mem := mem |}
      {| EC := ec'; ECS := ecs'; Mem := mem' |} ns ns' na' tr),
      (na' = merror /\ Mem.nextblock mem = Mem.nextblock mem') \/
      (exists aid, na' = ret aid /\ Mem.nextblock mem + 1 = Mem.nextblock mem').
Proof.
  intros; inv Hstep.
  simpl in Hec; inv Hec; clear H. admit. (*
  destruct pst.

  { Case "1. nop".
  left; split.
  - inv Hpop0; [|done].
    destruct rcmd; done.
  - by destruct Hstep0 as [Hres _]; inv Hres.
  }

  Case "2. cmd".
  inv Hpop0; [|done].
  destruct rcmd; [|done]; clear Hist.
  unfold pop_state_ocmd in Hpop; rewrite Hpop1 in Hpop; subst.
  unfold pop_one_X in Hpop1.
  destruct (noop_idx_zero_exists hpn); [done|].
  destruct ec0; simpl in *; destruct CurCmds0; [done|]; inv Hpop1.
  destruct c; destruct_step_tac; try (left; split; [done|]; inv Hstep0; done).

  SCase "2.1. malloc".
  right; inv Hstep0; exists id5; split; [done|].
  eapply memory_props.MemProps.nextblock_malloc; eauto.

  SCase "2.2. free".
  left; inv Hstep0; split; [done|].
  eapply memory_props.MemProps.nextblock_free; eauto.

  SCase "2.3. alloca".
  right; inv Hstep0; exists id5; split; [done|].
  eapply memory_props.MemProps.nextblock_malloc; eauto.

  SCase "2.4. store".
  left; inv Hstep0; split; [done|].
  eapply memory_props.MemProps.nextblock_mstore; eauto.

  SCase "2.5. call".
  by elim (Hncall id5).

  Case "3. terminator".
  inv Hpop0; [by destruct rcmd|]; clear Hist.
  by unfold pop_state_ocmd in Hpop; rewrite Hpop1 in Hpop; subst.
  *)
Qed.

Lemma filter_eq_heap_preserves_hint_sem_each_aux:
  forall cfg1 fn_al ec1 ec1' ecs1 ecs1' mem1 mem1' gmax ns1 ns1' na1' tr ocmd1
    inv1 inv1' m olc1
    (Hgna1: globals_no_alias (Globals cfg1))
    (Hstep1: logical_semantic_step cfg1 fn_al
      {| EC := ec1; ECS := ecs1; Mem := mem1 |}
      {| EC := ec1'; ECS := ecs1'; Mem := mem1' |} ns1 ns1' na1' tr)
    (Hpop1: pop_state_ocmd (ec1 :: ecs1) ns1 ocmd1)
    (Hncall1: forall rid : id, is_general_call ocmd1 rid -> False)
    (Hinv1': inv1' = filter_eq_heap_by_only_read_memory_value m ocmd1 inv1)
    (Hlinv: eqs_sem cfg1 olc1 (Locals ec1') mem1 gmax inv1),
    eqs_sem cfg1 olc1 (Locals ec1') mem1' gmax inv1'.
Proof.
  intros. admit. (*
  destruct inv1 as [ireg1 iheap1 inreg1].
  unfold filter_eq_heap_by_only_read_memory_value in Hinv1'.
  destruct inv1' as [ireg1' iheap1' inreg1']; inv Hinv1'.
  unfold eqs_sem; splits; simpl.

  SCase "1.1. register equations: involved only with old_alloca".
  destruct Hlinv as [Hreg1 _]; simpl in Hreg1.
  unfold filter_heap_eqs_by_cmd.
  destruct ocmd1 as [cmd1|]; destruct_lstep_tac;
    [|by simpl; destruct Hstep as [Hstep _]; inv Hstep].

  remember (vars_aux.def_cmd cmd1) as dcmd1; destruct dcmd1.

  SSCase "1.1.1. when there's a newly defined id".
  simpl; remember (is_alloca_or_malloc (ret cmd1)) as balloc1; destruct balloc1.

  SSSCase "1.1.1.1. malloc or alloca".
  simpl; unfold eqs_eq_reg_sem in *; intros.
  exploit Hreg1; eauto; intro Hereg1; clear Hreg1.
  inv Hereg1.
  { econstructor; eauto. }
  { destruct cmd1; try done; destruct_step_tac; inv Hstep;
    exploit memory_props.MemProps.nextblock_malloc; eauto; intro Hmfact;
    eapply eq_reg_sem_old_alloca; eauto;
    rewrite <-Hmfact; omega.
  }

  SSSCase "1.1.1.2. otherwise, memory does not change".
  exploit def_cmd_inl_not_malloc_implies_memory_same; eauto.
  intro Hmeq; subst; done.

  SSCase "1.1.2. free or store".
  simpl; destruct cmd1; try done; destruct_step_tac; inv Hstep.

  SSSCase "1.1.2.1. free".
  exploit memory_props.MemProps.nextblock_free; eauto; intro Hmfact.
  simpl; unfold eqs_eq_reg_sem in *; intros.
  exploit Hreg1; eauto; intro Hereg1; clear Hreg1.
  inv Hereg1.
  { econstructor; eauto. }
  { eapply eq_reg_sem_old_alloca; eauto.
    rewrite <-Hmfact; done.
  }

  SSSCase "1.1.2.2. store".
  exploit memory_props.MemProps.nextblock_mstore; eauto; intro Hmfact.
  simpl; unfold eqs_eq_reg_sem in *; intros.
  exploit Hreg1; eauto; intro Hereg1; clear Hreg1.
  inv Hereg1.
  { econstructor; eauto. }
  { eapply eq_reg_sem_old_alloca; eauto.
    rewrite <-Hmfact; done.
  }
  
  SCase "1.2. heap equations: involved only with heap filter".
  destruct Hlinv as [_ [Hheap1 Hnreg1]]; simpl in Hheap1.
  destruct ocmd1 as [cmd1|]; destruct_lstep_tac;
    [|by destruct Hstep as [Hstep _]; inv Hstep].
  destruct cmd1; destruct_step_tac; move Hheap1 at bottom.

  SSCase "1.2.1. malloc".
  unfold eqs_eq_heap_sem in *; intros.
  exploit Hheap1; eauto; intro Hhelt1; clear Hheap1 H.
  unfold eq_heap_sem in *.
  remember (getOperandValueExt (CurTargetData cfg1) p olc1 Locals1 (Globals cfg1))
  as pov; destruct pov; [|done].
  remember (getOperandValueExt (CurTargetData cfg1) v olc1 Locals1 (Globals cfg1))
  as vov; destruct vov; [|done]; intros.
  exploit Hhelt1; eauto; intro Hload1; clear Hhelt1; inv Hmp.

  inv Hstep; simpl in *.
  remember (mload TD mem1 mp t a) as vload; destruct vload; [|done].
  exploit memory_props.MemProps.malloc_preserves_mload; eauto; intro Hres.
  rewrite Hres; done.

  { SSCase "1.2.2. free".
  inv Hstep.
  unfold eqs_eq_heap_sem in *; intros.
  unfold filter_pointer_in_eqs_eq_heap in H.
  rewrite EqHeapSetFacts.filter_b in H;
    [| by unfold compat_bool, Proper, "==>"; intros; subst].
  apply andb_true_iff in H; destruct H.
  exploit Hheap1; eauto; intros Hbrd.
  remember (vars_aux.add_ntag_value value5) as pv; destruct pv;
    inversion H21; subst mptrs; clear H21.

  (* freed by id "x". *)
  - destruct x as [x nx]; unfold vars_aux.add_ntag_value in Heqpv.
    destruct value5; [|done]; unfold vars_aux.add_ntag in Heqpv.
    inv Heqpv; simpl in H20.
    destruct p; try done.

    (* neq_reg with id. *)
    + unfold eq_heap_sem in *; simpl; simpl in Hbrd.
      remember (lookupALExt olc1 Locals1 x) as vx; destruct vx; [|done].
      destruct (getOperandValueExt TD v olc1 Locals1 gl); [|done]; intros.
      inv Hmp; exploit Hbrd; eauto; intro Hmload1; clear Hbrd.
      remember (mload TD mem1 mp t a) as mv; destruct mv; [|done].
      symmetry in Heqmv.
      exploit memory_props.MemProps.free_preserves_mload; eauto.
      { apply orb_true_iff in H0; inv H0; pose (Hnreg1 _ _ H1) as Hnoteq;
        unfold neq_reg_sem in Hnoteq; simpl in Hnoteq;
        rewrite H20, <- Heqvx in Hnoteq; destruct Hnoteq;
        unfold no_alias' in H2; destruct H2 as [Hna [Hundef1 Hundef2]];
        [done|eapply memory_props.MemProps.no_alias_sym; eauto].
      }
      intros Hres; rewrite Hres; done.

    (* neq_reg with const *)
    + destruct c; try done.
      unfold eq_heap_sem in *; simpl; simpl in Hbrd.
      remember (@const2GV DGVs TD gl (const_gid typ0 id1)) as icgv;
        destruct icgv; [|done].
      unfold const2GV, _const2GV in Heqicgv.
      remember (lookupAL GenericValue gl id1) as gvid1; destruct gvid1; [|done].
      inv Heqicgv.
      destruct (getOperandValueExt TD v olc1 Locals1 gl); [|done]; intros.
      exploit Hbrd; eauto; intro Hmload1; clear Hbrd.
      remember (mload TD mem1 mp t a) as mv; destruct mv; [|done].
      inv Hmp.
      exploit memory_props.MemProps.free_preserves_mload; eauto.
      { pose (Hnreg1 _ _ H0) as Hnoteq.
        unfold neq_reg_sem in Hnoteq; simpl in Hnoteq.
        rewrite H20, <- Heqgvid1 in Hnoteq; destruct Hnoteq.
        unfold no_alias' in H2; destruct H2 as [Hna [Hundef1 Hundef2]].
        rewrite not_undef_implies_cgv2gvs_same; eauto.
      }
      intros Hres; rewrite Hres; done.

  (* freed by const *)
  - destruct c; try done.
    destruct value5; [done|].
    simpl in H20. unfold const2GV in H20.
    destruct const5; try done; simpl in H20.
    remember (lookupAL GenericValue gl id1) as gvid1; destruct gvid1; [|done];
      inv H20.
    simpl in Heqpv; inv Heqpv.
    destruct p; try done.

    { unfold eq_heap_sem in *; simpl; simpl in Hbrd.
      remember (lookupALExt olc1 Locals1 x) as xv; destruct xv; [|done].
      destruct (getOperandValueExt TD v olc1 Locals1 gl); [|done]; intros.
      exploit Hbrd; eauto; intro Hmload1; clear Hbrd.
      remember (mload TD mem1 mp t a) as mv; destruct mv; [|done].
      inv Hmp.
      exploit memory_props.MemProps.free_preserves_mload; eauto.
      { pose (Hnreg1 _ _ H0) as Hnoteq.
        unfold neq_reg_sem in Hnoteq; simpl in Hnoteq.
        rewrite <- Heqxv, <- Heqgvid1 in Hnoteq; destruct Hnoteq.
        unfold no_alias' in H2; destruct H2 as [Hna [Hundef1 Hundef2]].
        eapply memory_props.MemProps.no_alias_sym; eauto.
        rewrite not_undef_implies_cgv2gvs_same; eauto.
      }
      intros Hres; rewrite Hres; done.
    }
    { destruct c; try done.
      unfold eq_heap_sem in *; simpl; simpl in Hbrd.
      remember (@const2GV DGVs TD gl (const_gid typ0 id0)) as icgv;
        destruct icgv; [|done].
      unfold const2GV, _const2GV in Heqicgv.
      remember (lookupAL GenericValue gl id0) as gvid0; destruct gvid0; [|done].
      inv Heqicgv.
      destruct (getOperandValueExt TD v olc1 Locals1 gl); [|done]; intros.
      exploit Hbrd; eauto; intro Hmload1; clear Hbrd.
      remember (mload TD mem1 mp t a) as mv; destruct mv; [|done].
      inv Hmp.
      exploit memory_props.MemProps.free_preserves_mload; eauto.
      { apply negb_true_iff in H0; destruct (id_dec id1 id0); [done|].
        exploit Hgna1; eauto; intros [Hna [Hundef1 Hundef2]].
        repeat rewrite not_undef_implies_cgv2gvs_same; eauto.
      }
      intros Hres; rewrite Hres; done.
    }
  }

  SSCase "1.2.3. alloca".
  unfold eqs_eq_heap_sem in *; intros.
  exploit Hheap1; eauto; intro Hhelt1; clear Hheap1 H.
  unfold eq_heap_sem in *.
  remember (getOperandValueExt (CurTargetData cfg1) p olc1 Locals1 (Globals cfg1))
  as pov; destruct pov; [|done].
  remember (getOperandValueExt (CurTargetData cfg1) v olc1 Locals1 (Globals cfg1))
  as vov; destruct vov; [|done]; intros.
  exploit Hhelt1; eauto; intro Hload1; clear Hhelt1; inv Hmp.

  inv Hstep; simpl in *.
  remember (mload TD mem1 mp t a) as vload; destruct vload; [|done].
  exploit memory_props.MemProps.malloc_preserves_mload; eauto; intro Hres.
  rewrite Hres; done.

  SSCase "1.2.4. store".
  inv Hstep.
  unfold eqs_eq_heap_sem in *; intros.
  unfold filter_pointer_in_eqs_eq_heap in H.
  rewrite EqHeapSetFacts.filter_b in H;
    [| by unfold compat_bool, Proper, "==>"; intros; subst].
  apply andb_true_iff in H; destruct H.
  exploit Hheap1; eauto; intros Hbrd.
  remember (vars_aux.add_ntag_value value2) as pv; destruct pv;
    inversion H24; subst gvs1; clear H24;
    inversion H25; subst mps2; clear H25.

  (* stored by id "x". *)
  { destruct x as [x nx]; unfold vars_aux.add_ntag_value in Heqpv.
    destruct value2; [|done]; unfold vars_aux.add_ntag in Heqpv.
    inv Heqpv; simpl in H23.
    destruct p; try done.

    (* neq_reg with id. *)
    + unfold eq_heap_sem in *; simpl; simpl in Hbrd.
      remember (lookupALExt olc1 Locals1 x) as vx; destruct vx; [|done].
      destruct (getOperandValueExt TD v olc1 Locals1 gl); [|done]; intros.
      inv Hmp; exploit Hbrd; eauto; intro Hmload1; clear Hbrd.
      remember (mload TD mem1 mp t a) as mv; destruct mv; [|done].
      symmetry in Heqmv.
      exploit memory_props.MemProps.mstore_preserves_mload; eauto.
      { apply orb_true_iff in H0; inv H0; pose (Hnreg1 _ _ H1) as Hnoteq;
        unfold neq_reg_sem in Hnoteq; simpl in Hnoteq;
        rewrite H23, <- Heqvx in Hnoteq; destruct Hnoteq;
        unfold no_alias' in H2; destruct H2 as [Hna [Hundef1 Hundef2]];
        [done|eapply memory_props.MemProps.no_alias_sym; eauto].
      }
      intros Hres; rewrite Hres; done.

    (* neq_reg with const *)
    + destruct c; try done.
      unfold eq_heap_sem in *; simpl; simpl in Hbrd.
      remember (@const2GV DGVs TD gl (const_gid typ0 id1)) as icgv;
        destruct icgv; [|done].
      unfold const2GV, _const2GV in Heqicgv.
      remember (lookupAL GenericValue gl id1) as gvid1; destruct gvid1; [|done].
      inv Heqicgv.
      destruct (getOperandValueExt TD v olc1 Locals1 gl); [|done]; intros.
      exploit Hbrd; eauto; intro Hmload1; clear Hbrd.
      remember (mload TD mem1 mp t a) as mv; destruct mv; [|done].
      inv Hmp.
      exploit memory_props.MemProps.mstore_preserves_mload; eauto.
      { pose (Hnreg1 _ _ H0) as Hnoteq.
        unfold neq_reg_sem in Hnoteq; simpl in Hnoteq.
        rewrite H23, <- Heqgvid1 in Hnoteq; destruct Hnoteq.
        unfold no_alias' in H2; destruct H2 as [Hna [Hundef1 Hundef2]].
        rewrite not_undef_implies_cgv2gvs_same; eauto.
      }
      intros Hres; rewrite Hres; done.
  }
  (* stored by const *)
  { destruct c; try done.
    destruct value2; [done|].
    simpl in H23. unfold const2GV in H23.
    destruct const5; try done; simpl in H23.
    remember (lookupAL GenericValue gl id1) as gvid1; destruct gvid1; [|done];
      inv H23.
    simpl in Heqpv; inv Heqpv.
    destruct p; try done.

    { unfold eq_heap_sem in *; simpl; simpl in Hbrd.
      remember (lookupALExt olc1 Locals1 x) as xv; destruct xv; [|done].
      destruct (getOperandValueExt TD v olc1 Locals1 gl); [|done]; intros.
      exploit Hbrd; eauto; intro Hmload1; clear Hbrd.
      remember (mload TD mem1 mp t a) as mv; destruct mv; [|done].
      inv Hmp.
      exploit memory_props.MemProps.mstore_preserves_mload; eauto.
      { pose (Hnreg1 _ _ H0) as Hnoteq.
        unfold neq_reg_sem in Hnoteq; simpl in Hnoteq.
        rewrite <- Heqxv, <- Heqgvid1 in Hnoteq; destruct Hnoteq.
        eapply memory_props.MemProps.no_alias_sym; eauto.
        unfold no_alias' in H2; destruct H2 as [Hna [Hundef1 Hundef2]].
        rewrite not_undef_implies_cgv2gvs_same; eauto.
      }
      intros Hres; rewrite Hres; done.
    }
    { destruct c; try done.
      unfold eq_heap_sem in *; simpl; simpl in Hbrd.
      remember (@const2GV DGVs TD gl (const_gid typ0 id0)) as icgv;
        destruct icgv; [|done].
      unfold const2GV, _const2GV in Heqicgv.
      remember (lookupAL GenericValue gl id0) as gvid0; destruct gvid0; [|done].
      inv Heqicgv.
      destruct (getOperandValueExt TD v olc1 Locals1 gl); [|done]; intros.
      exploit Hbrd; eauto; intro Hmload1; clear Hbrd.
      remember (mload TD mem1 mp t a) as mv; destruct mv; [|done].
      inv Hmp.
      exploit memory_props.MemProps.mstore_preserves_mload; eauto.
      { apply negb_true_iff in H0; destruct (id_dec id1 id0); [done|].
        exploit Hgna1; eauto; intros [Hna [Hundef1 Hundef2]].
        repeat rewrite not_undef_implies_cgv2gvs_same; eauto.
      }
      intros Hres; rewrite Hres; done.
    }
  }

  SSCase "1.2.5. call".
  by elim (Hncall1 id5).

  SCase "1.3. register non-equations: not changed".
  destruct Hlinv as [_ [_ Hnreg1]]; simpl in Hnreg1.
  assert (Hseq: eqs_neq_reg_sem cfg1 olc1 (Locals ec1')
    (eqs_neq_reg
      (filter_heap_eqs_by_cmd
        {|
          eqs_eq_reg := ireg1;
          eqs_eq_heap := iheap1;
          eqs_neq_reg := inreg1 |} ocmd1)) =
    eqs_neq_reg_sem cfg1 olc1 (Locals ec1') inreg1).
  { unfold filter_heap_eqs_by_cmd.
    by destruct ocmd1 as [cmd1|]; [destruct (vars_aux.def_cmd cmd1)|done].
  }
  rewrite Hseq; done. *)
Qed.

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
    (Heqtd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgna1: globals_no_alias (Globals cfg1))
    (Hgna2: globals_no_alias (Globals cfg2)).
  
  Definition r1 := Locals ec1.
  Definition r2 := Locals ec2.
  Definition r1' := Locals ec1'.
  Definition r2' := Locals ec2'.
  Definition als1 := Allocas ec1.
  Definition als2 := Allocas ec2.
  Definition als1' := Allocas ec1'.
  Definition als2' := Allocas ec2'.

  Lemma filter_eq_heap_preserves_hint_sem_each:
    forall md iso1 iso2 alpha' z inv1 inv2 inv1' inv2' m1 m2
      (Hinv1': inv1' = filter_eq_heap_by_only_read_memory_value m1 ocmd1 inv1)
      (Hinv2': inv2' = filter_eq_heap_by_only_read_memory_value m2 ocmd2 inv2)

      (Hsem: hint_sem_each md inv1 inv2 iso1 iso2
        alpha' z cfg1 cfg2 r1' r2' mem1 mem2
        li1 pi1 li2 pi2 als1' als2' mem1' mem2'),

      (hint_sem_each md inv1' inv2' iso1 iso2
        alpha' z cfg1 cfg2 r1' r2' mem1' mem2'
        li1 pi1 li2 pi2 als1' als2' mem1' mem2').
  Proof.
    intros; unfold r1, r1', r2, r2', als1, als1', als2, als2' in *.
    destruct Hsem as [Hmi Hiav]; split; [|done].
    destruct Hmi as [olc1 [olc2 [Hmd Hinv]]]; exists olc1; exists olc2; split; [done|].
    clear Hmd; destruct Hinv as [Hlinv [Hrinv [Hliso Hriso]]]; simpl in Hlinv, Hrinv.
    rr; splits; simpl; try done;
      eapply filter_eq_heap_preserves_hint_sem_each_aux; eauto.
  Qed.
End HintSemEach.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
