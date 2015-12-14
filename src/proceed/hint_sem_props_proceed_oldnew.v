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

Definition update_olc_by_ocmd olc lc ocmd : @GVsMap DGVs :=
  match ocmd with
    | ret cmd =>
      match (vars_aux.def_cmd cmd) with
        | inl x => 
          match (lookupAL _ lc x) with
            | ret xv => updateAddAL _ olc x xv
            | merror => deleteAL _ olc x
          end
        | inr _ => olc
      end
    | merror => olc
  end.

Lemma deleteAL_deleteAL A m k :
  eqAL A (deleteAL A (deleteAL A m k) k) (deleteAL A m k).
Proof.
  intro x.
  destruct (id_dec k x); [subst|].
  - by repeat rewrite lookupAL_deleteAL_eq.
  - by rewrite lookupAL_deleteAL_neq.
Qed.

Lemma updateAddAL_deleteAL A m k v :
  eqAL A (updateAddAL A (deleteAL A m k) k v) (updateAddAL A m k v).
Proof.
  intro x.
  destruct (id_dec x k); [subst|].
  - by repeat rewrite lookupAL_updateAddAL_eq.
  - repeat (rewrite <- lookupAL_updateAddAL_neq; [|done]).
    rewrite lookupAL_deleteAL_neq; [done|].
    by intro H; apply n; symmetry.
Qed.

Lemma oldnew_preserves_maydiff_sem_aux:
  forall i1 lc1 lc2 alpha' md olc1 olc2 igv1 igv2 cmd1 cmd2
    (Hmd : maydiff_sem lc1 lc2 alpha' olc1 olc2 md)
    (Heqcmd1id: inl i1 = vars_aux.def_cmd cmd1)
    (Heqcmd2id: inl i1 = vars_aux.def_cmd cmd2),
    maydiff_sem (updateAddAL GVs lc1 i1 igv1)
    (updateAddAL GVs lc2 i1 igv2) alpha'
    (update_olc_by_ocmd olc1 lc1 (ret cmd1))
    (update_olc_by_ocmd olc2 lc2 (ret cmd2))
    (maydiff_add_def_new_opt
      (maydiff_add_def_new_opt
        (new_to_old_md_by_newdefs
          (remove_old_md_by_newdefs md
            (AtomSetImpl.inter (vars_aux.def_cmd_opt (ret cmd1))
              (vars_aux.def_cmd_opt (ret cmd2))))
          (AtomSetImpl.inter (vars_aux.def_cmd_opt (ret cmd1))
            (vars_aux.def_cmd_opt (ret cmd2)))) 
        (ret cmd1)) (ret cmd2)).
Proof.
  intros.
  unfold maydiff_add_def_new_opt, maydiff_add_def_new, vars_aux.def_cmd_opt;
    rewrite <-Heqcmd1id, <-Heqcmd2id.

  assert (Hstep1: maydiff_sem lc1 lc2 alpha'
    (deleteAL _ olc1 i1) (deleteAL _ olc2 i1)
    (remove_old_md_by_newdefs md (AtomSetImpl.inter (singleton i1) (singleton i1)))).
  Case "Step 1: wrapping remove_old_md_by_newdefs".
  unfold maydiff_sem in *; intros x Hx.
  unfold remove_old_md_by_newdefs in Hx; unfold variable_equivalent in *.
  assert (Hseteq: IdExtSetImpl.eq
    (AtomSetImpl.fold
      (fun (x : atom) (acc : IdExtSetImpl.t) =>
        IdExtSetImpl.remove (vars_aux.add_otag x) acc)
      (AtomSetImpl.inter (singleton i1) (singleton i1)) md)
    (IdExtSetImpl.remove (vars_aux.add_otag i1) md)).
  { idtac.
    match goal with
      | [|- context[AtomSetImpl.fold ?f ?s ?i]] =>
        exploit (AtomSetFacts2.fold_singleton_simpl f s i)
    end.
    + rewrite AtomSetFacts2.inter_singleton_1.
      reflexivity.
    + intro H; destruct H as [e' [He' H]]; subst.
      by rewrite H.
  }
  rewrite Hseteq in Hx.
  destruct (id_ext_dec x (i1, ntag_old)).
  { by subst; simpl; repeat rewrite lookupAL_deleteAL_eq. }
  { destruct x as [x [|]]; simpl.
    + destruct (id_dec i1 x); [by subst; elim n|].
      repeat rewrite lookupAL_deleteAL_neq; eauto.
      rewrite IdExtSetFacts.remove_b in Hx.
      apply andb_false_iff in Hx; inv Hx.
      * by pose (Hmd (x, ntag_old) H).
      * apply negb_false_iff in H.
        unfold vars_aux.add_otag, IdExtSetFacts.eqb in H.
        destruct (IdExtSetFacts.eq_dec (i1, ntag_old) (x, ntag_old)); [|done].
        by inv e; elim n0.
    + rewrite IdExtSetFacts.remove_b in Hx.
      apply andb_false_iff in Hx; inv Hx.
      * by pose (Hmd (x, ntag_new) H).
      * apply negb_false_iff in H.
        unfold vars_aux.add_otag, IdExtSetFacts.eqb in H.
        by destruct (IdExtSetFacts.eq_dec (i1, ntag_old) (x, ntag_new)).
  }

  assert (Hstep2: maydiff_sem
    (deleteAL _ lc1 i1) (deleteAL _ lc2 i1) alpha'
    (update_olc_by_ocmd (deleteAL _ olc1 i1) lc1 (ret cmd1))
    (update_olc_by_ocmd (deleteAL _ olc2 i1) lc2 (ret cmd2))
    (new_to_old_md_by_newdefs
      (remove_old_md_by_newdefs md (AtomSetImpl.inter (singleton i1) (singleton i1)))
      (AtomSetImpl.inter (singleton i1) (singleton i1)))).
  { Case "Step 2: wrapping new_to_old_md_by_newdefs".
  remember (deleteAL GVs olc1 i1) as dolc1.
  remember (deleteAL GVs olc2 i1) as dolc2.
  remember (remove_old_md_by_newdefs md
    (AtomSetImpl.inter (singleton i1) (singleton i1))) as md'.
  unfold maydiff_sem in *; intros x Hx.
  unfold new_to_old_md_by_newdefs in Hx; unfold variable_equivalent in *.
  assert (Hseteq: IdExtSetImpl.eq
    (AtomSetImpl.fold
      (fun (x : atom) (_ : IdExtSetImpl.t) =>
        if IdExtSetImpl.mem (vars_aux.add_ntag x) md'
          then
            IdExtSetImpl.add (vars_aux.add_otag x)
            (IdExtSetImpl.remove (vars_aux.add_ntag x) md')
          else md') (AtomSetImpl.inter (singleton i1) (singleton i1)) md')
    (if IdExtSetImpl.mem (vars_aux.add_ntag i1) md'
      then
        IdExtSetImpl.add (vars_aux.add_otag i1)
        (IdExtSetImpl.remove (vars_aux.add_ntag i1) md')
      else md')).
  { idtac.
    match goal with
      | [|- context[AtomSetImpl.fold ?f ?s ?i]] =>
        exploit (AtomSetFacts2.fold_singleton_simpl f s i)
    end.
    + rewrite AtomSetFacts2.inter_singleton_1.
      reflexivity.
    + intro H; destruct H as [e' [He' H]]; subst.
      by rewrite H.
  }
  rewrite Hseteq in Hx; clear Hseteq.
  remember (IdExtSetImpl.mem (vars_aux.add_ntag i1) md') as ni1mem; destruct ni1mem.

  { destruct (id_ext_dec (i1, ntag_old) x);
    [subst x; elimtype False; clear -Hx;
      rewrite IdExtSetFacts.add_b in Hx;
      apply orb_false_iff in Hx; destruct Hx as [Hx _];
      unfold vars_aux.add_otag, IdExtSetFacts.eqb in Hx;
      destruct (IdExtSetFacts.eq_dec (i1, ntag_old) (i1, ntag_old)); done|].

    destruct (id_ext_dec (i1, ntag_new) x);
    [by subst x; simpl; repeat rewrite lookupAL_deleteAL_eq|].

    destruct x as [x [|]].
    + destruct (id_dec i1 x); [by subst x; elim n|].
      rewrite IdExtSetFacts.add_b in Hx.
      apply orb_false_iff in Hx; destruct Hx as [_ Hx].
      rewrite IdExtSetFacts2.F.remove_b in Hx.
      apply andb_false_iff in Hx; inversion Hx;
        [|apply negb_false_iff in H;
          unfold vars_aux.add_ntag, IdExtSetFacts2.F.eqb in H;
          destruct (IdExtSetFacts.eq_dec (i1, ntag_new) (x, ntag_old)); done].
      clear n n0; simpl; rewrite <- Heqcmd1id, <- Heqcmd2id.
      remember (lookupAL GVs lc1 i1) as vi1; destruct vi1.
      * rewrite <- lookupAL_updateAddAL_neq; eauto.
        remember (lookupAL GVs lc2 i1) as vi2; destruct vi2;
          [by rewrite <- lookupAL_updateAddAL_neq; eauto; pose (Hstep1 _ H)|
            by rewrite lookupAL_deleteAL_neq; eauto; pose (Hstep1 _ H)].
      * rewrite lookupAL_deleteAL_neq; eauto.
        remember (lookupAL GVs lc2 i1) as vi2; destruct vi2;
          [by rewrite <- lookupAL_updateAddAL_neq; eauto; pose (Hstep1 _ H)|
            by rewrite lookupAL_deleteAL_neq; eauto; pose (Hstep1 _ H)].

    + destruct (id_dec i1 x); [by subst x; elim n0|].
      rewrite IdExtSetFacts.add_b in Hx.
      apply orb_false_iff in Hx; destruct Hx as [_ Hx].
      rewrite IdExtSetFacts2.F.remove_b in Hx.
      apply andb_false_iff in Hx; inversion Hx;
        [|apply negb_false_iff in H;
          unfold vars_aux.add_ntag, IdExtSetFacts2.F.eqb in H;
          destruct (IdExtSetFacts.eq_dec (i1, ntag_new) (x, ntag_new)); done].
      clear n n0; simpl.
      repeat rewrite lookupAL_deleteAL_neq; eauto.
      by pose (Hstep1 _ H).
  }

  { symmetry in Heqni1mem; unfold vars_aux.add_ntag in Heqni1mem.
    remember (Hstep1 _ Heqni1mem) as Hfact; simpl in Hfact; clear HeqHfact.
    destruct (id_ext_dec (i1, ntag_old) x).
    + subst x; simpl; rewrite <- Heqcmd1id, <- Heqcmd2id.
      remember (lookupAL GVs lc1 i1) as vi1; destruct vi1.
      * rewrite lookupAL_updateAddAL_eq; eauto.
        remember (lookupAL GVs lc2 i1) as vi2; destruct vi2; [|done].
        rewrite lookupAL_updateAddAL_eq; eauto.
      * rewrite lookupAL_deleteAL_eq; eauto.
        remember (lookupAL GVs lc2 i1) as vi2; destruct vi2; [done|].
        rewrite lookupAL_deleteAL_eq; eauto.
    + clear Hfact.
      destruct (id_ext_dec (i1, ntag_new) x);
      [by subst x; simpl; repeat rewrite lookupAL_deleteAL_eq; eauto|].
      destruct x as [x [|]]; simpl.

      * destruct (id_dec i1 x); [by subst x; elim n|].
        rewrite <- Heqcmd1id, <- Heqcmd2id.
        assert (Hleq1: lookupAL GVs
          match lookupAL GVs lc1 i1 with
            | ret xv => updateAddAL GVs dolc1 i1 xv
            | merror => deleteAL GVs dolc1 i1
          end x = lookupALExt dolc1 lc1 (x, ntag_old)) by
        (simpl; destruct (lookupAL GVs lc1 i1);
          [by rewrite <- lookupAL_updateAddAL_neq; eauto|
            by rewrite lookupAL_deleteAL_neq; eauto]).
        assert (Hleq2: lookupAL GVs
          match lookupAL GVs lc2 i1 with
            | ret xv => updateAddAL GVs dolc2 i1 xv
            | merror => deleteAL GVs dolc2 i1
          end x = lookupALExt dolc2 lc2 (x, ntag_old)) by
        (simpl; destruct (lookupAL GVs lc2 i1);
          [by rewrite <- lookupAL_updateAddAL_neq; eauto|
            by rewrite lookupAL_deleteAL_neq; eauto]).
        pose (Hstep1 _ Hx) as Hres.
        by rewrite <- Hleq1, <- Hleq2 in Hres.

      * destruct (id_dec i1 x); [by subst x; elim n0|].
        repeat rewrite lookupAL_deleteAL_neq; eauto.
        by pose (Hstep1 _ Hx).
  } }

  clear Hstep1.

  assert (Haleq1: eqAL _
    (update_olc_by_ocmd (deleteAL _ olc1 i1) lc1 (ret cmd1))
    (update_olc_by_ocmd olc1 lc1 (ret cmd1))).
  { unfold update_olc_by_ocmd; rewrite <- Heqcmd1id.
    destruct (lookupAL _ lc1 i1).
    + by apply updateAddAL_deleteAL.
    + by apply deleteAL_deleteAL.
  }

  assert (Haleq2: eqAL _
    (update_olc_by_ocmd (deleteAL _ olc2 i1) lc2 (ret cmd2))
    (update_olc_by_ocmd olc2 lc2 (ret cmd2))).
  { unfold update_olc_by_ocmd; rewrite <- Heqcmd2id.
    destruct (lookupAL _ lc2 i1).
    + by apply updateAddAL_deleteAL.
    + by apply deleteAL_deleteAL.
  }

  assert (Hstep3: maydiff_sem
    (deleteAL _ lc1 i1) (deleteAL _ lc2 i1) alpha'
    (update_olc_by_ocmd olc1 lc1 (ret cmd1))
    (update_olc_by_ocmd olc2 lc2 (ret cmd2))
    (new_to_old_md_by_newdefs
      (remove_old_md_by_newdefs md (AtomSetImpl.inter (singleton i1) (singleton i1)))
      (AtomSetImpl.inter (singleton i1) (singleton i1)))).

  { Case "Step 3: polishing, using Haleq1 and Haleq2".
  unfold maydiff_sem in *; intros x Hx.
  remember (Hstep2 _ Hx) as Hbrd; clear HeqHbrd Hstep2.
  unfold variable_equivalent in *.
  destruct x as [x [|]].
  - unfold lookupALExt in *; by repeat rewrite <- Haleq1; rewrite <- Haleq2.
  - unfold lookupALExt in *; done.
  }

  clear Haleq1 Haleq2 Hstep2.

  assert (Hstep4: maydiff_sem
    (updateAddAL _ (deleteAL _ lc1 i1) i1 igv1)
    (updateAddAL _ (deleteAL _ lc2 i1) i1 igv2) alpha'
    (update_olc_by_ocmd olc1 lc1 (ret cmd1))
    (update_olc_by_ocmd olc2 lc2 (ret cmd2))
    (IdExtSetImpl.add (vars_aux.add_ntag i1)
      (IdExtSetImpl.add (vars_aux.add_ntag i1)
        (new_to_old_md_by_newdefs
          (remove_old_md_by_newdefs md
            (AtomSetImpl.inter (singleton i1) (singleton i1)))
          (AtomSetImpl.inter (singleton i1) (singleton i1)))))).
  { Case "Step 4: wrapping newtag adds".
  remember (new_to_old_md_by_newdefs
    (remove_old_md_by_newdefs md
      (AtomSetImpl.inter (singleton i1) (singleton i1)))
    (AtomSetImpl.inter (singleton i1) (singleton i1))) as md'.
  remember (deleteAL GVs lc1 i1) as ec'.
  remember (deleteAL GVs lc2 i1) as ec0'.
  unfold maydiff_sem in *; intros x Hx.
  destruct (id_ext_dec (i1, ntag_new) x).
  - subst x; elimtype False; clear -Hx.
    rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx.
    destruct Hx as [Hcontr _].
    unfold vars_aux.add_ntag, IdExtSetFacts.eqb in Hcontr.
    by destruct (IdExtSetFacts.eq_dec (i1, ntag_new) (i1, ntag_new)).
  - rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx; destruct Hx as [_ Hx].
    rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx; destruct Hx as [_ Hx].
    remember (Hstep3 _ Hx) as Hres; clear HeqHres Hstep3.
    unfold variable_equivalent in *.
    destruct x as [x [|]]; [done|].
    destruct (id_dec i1 x); [by subst x; elim n|].
    unfold lookupALExt in *.
    by repeat rewrite <- lookupAL_updateAddAL_neq; eauto.
  }

  clear Hstep3.

  assert (Haleq1: eqAL _
    (updateAddAL GVs (deleteAL GVs lc1 i1) i1 igv1)
    (updateAddAL GVs lc1 i1 igv1)).
  { by apply updateAddAL_deleteAL. }

  assert (Haleq2: eqAL _
    (updateAddAL GVs (deleteAL GVs lc2 i1) i1 igv2)
    (updateAddAL GVs lc2 i1 igv2)).
  { by apply updateAddAL_deleteAL. }

  (* Final step! *)
  unfold maydiff_sem in *; intros x Hx.
  remember (Hstep4 _ Hx) as Hres; clear HeqHres Hstep4.
  unfold variable_equivalent in *.
  destruct x as [x [|]]; [done|].
  unfold lookupALExt in *.
  by repeat rewrite <- Haleq1, <- Haleq2; eauto.
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
    (Heqtd: CurTargetData cfg1 = CurTargetData cfg2).
  
  Definition r1 := Locals ec1.
  Definition r2 := Locals ec2.
  Definition r1' := Locals ec1'.
  Definition r2' := Locals ec2'.
  Definition als1 := Allocas ec1.
  Definition als2 := Allocas ec2.
  Definition als1' := Allocas ec1'.
  Definition als2' := Allocas ec2'.

  Lemma oldnew_preserves_eqs_sem_cmd:
    forall cfg olc lc lc' mem0 gmax inv i0 igvs
    (Heqs1: eqs_sem cfg olc lc mem0 gmax inv)
    (Hec': lc' = updateAddAL GVs lc i0 igvs),
    eqs_sem cfg
    match lookupAL GVs lc i0 with
      | ret xv => updateAddAL GVs olc i0 xv
      | merror => deleteAL GVs olc i0
    end lc' mem0 gmax
    (new_to_old_by_newdefs (remove_old_by_newdefs inv (singleton i0)) (singleton i0)).
  Proof.
    intros.
    unfold new_to_old_by_newdefs; unfold remove_old_by_newdefs.
    repeat
      match goal with
        | [|- context[AtomSetImpl.fold ?f (AtomSetImpl.singleton ?e) ?i]] =>
          let x := fresh "x" in
            let H1 := fresh "H1" in
              let H2 := fresh "H2" in
                destruct (AtomSetFacts2.fold_singleton_simpl
                  f (AtomSetImpl.singleton e) i e (AtomSetImpl.eq_refl _))
                as [x [H1 H2]]; subst; rewrite H2; clear H2        
      end.
    destruct inv as [inv_r inv_h inv_ne].
    destruct Heqs1 as [Hinv1_r [Hinv1_h Hinv1_ne]]; simpl in *.
    rr; splits; simpl.

    - intros x' r' Hxrmem'.
      unfold new_to_old_local_in_eq_reg in Hxrmem'.
      exploit EqRegSetFacts2.in_fold_exists; eauto.
      intros [xr [Hxrmem Hxrn2o]]; inv Hxrn2o.
      unfold filter_local_in_eqs_eq_reg in Hxrmem.
      rewrite EqRegSetFacts.filter_b in Hxrmem;
        try (by unfold compat_bool, Proper, "==>"; intros; subst).
      apply andb_true_iff in Hxrmem; destruct Hxrmem as [Hxrmem Hxrfilt].
      destruct xr as [x r]; simpl in *.
      eapply oldnew_preserves_eq_reg_sem; eauto.

    - intros p' t' a' v' Hpvmem'.
      unfold new_to_old_local_in_eq_heap in Hpvmem'.
      exploit EqHeapSetFacts2.in_fold_exists; eauto.
      intros [pv [Hpvmem Hpvn2o]]; inv Hpvn2o.
      unfold filter_local_in_eqs_eq_heap in Hpvmem.
      rewrite EqHeapSetFacts.filter_b in Hpvmem;
        try (by unfold compat_bool, Proper, "==>"; intros; subst).
      apply andb_true_iff in Hpvmem; destruct Hpvmem as [Hpvmem Hpvfilt].
      destruct pv as [[[p t] a] v]; simpl in *.
      inv H0.
      eapply oldnew_preserves_eq_heap_sem; eauto.

    - intros i l Hilmem'.
      unfold new_to_old_local_in_neq_reg in Hilmem'.
      exploit NeqRegSetFacts2.in_fold_exists; eauto.
      intros [il [Hilmem Hiln2o]]; inv Hiln2o.
      unfold filter_local_in_eqs_neq_reg in Hilmem.
      rewrite NeqRegSetFacts.filter_b in Hilmem;
        try (by unfold compat_bool, Proper, "==>"; intros; subst).
      apply andb_true_iff in Hilmem; destruct Hilmem as [Hilmem Hilfilt].
      destruct il as [i lg]; simpl in *.
      eapply oldnew_preserves_neq_reg_sem; eauto.
  Qed.

  Lemma oldnew_preserves_eqs_sem:
    forall cfg fn_al ec ec' ecs ecs' mem mem' gmax ns ns' na' tr inv nd ocmd olc
      (Hstep1 : logical_semantic_step cfg fn_al
        {| EC := ec; ECS := ecs; Mem := mem |}
        {| EC := ec'; ECS := ecs'; Mem := mem' |} ns ns' na' tr)
      (Hpop1: pop_state_ocmd (ec :: ecs) ns ocmd)
      (Hncall: forall rid : id, is_general_call ocmd rid -> False)
      (Hnd: nd = vars_aux.def_cmd_opt ocmd)
      (Hsu1: self_use_check ocmd = true)
      (Heqs1: eqs_sem cfg olc (Locals ec) mem gmax inv),
      eqs_sem cfg (update_olc_by_ocmd olc (Locals ec) ocmd)
      (Locals ec') mem gmax
      (new_to_old_by_newdefs (remove_old_by_newdefs inv nd) nd).
  Proof.
    intros. admit. (*
    destruct ocmd as [cmd|]; destruct_lstep_tac. 

    - simpl in *; subst.
      remember (vars_aux.def_cmd cmd) as cmdid; destruct cmdid.
    
      + exploit def_cmd_inl_implies_locals_update; eauto; intros [igvs Hec'].
        eapply oldnew_preserves_eqs_sem_cmd; eauto.

      + unfold remove_old_by_newdefs;
        repeat rewrite AtomSetProperties.fold_1b; try done.
        unfold new_to_old_by_newdefs;
        repeat rewrite AtomSetProperties.fold_1b; try done.
        destruct cmd; try done; destruct_step_tac.

    - simpl in *; subst.
      unfold remove_old_by_newdefs;
      repeat rewrite AtomSetProperties.fold_1b; try done.
      unfold new_to_old_by_newdefs;
      repeat rewrite AtomSetProperties.fold_1b; try done.
      by destruct Hstep as [Heceq Heqtr]; inv Heceq; subst. *)
  Qed.

  Lemma oldnew_preserves_iso_sem_cmd:
    forall cfg olc lc lc' iso li i0 igvs
      (Hiso1 : isolated_sem (CurTargetData cfg) olc lc li iso)
      (Hec': lc' = updateAddAL GVs lc i0 igvs),
      isolated_sem (CurTargetData cfg)
      match lookupAL GVs lc i0 with
        | ret xv => updateAddAL GVs olc i0 xv
        | merror => deleteAL GVs olc i0
      end lc' li
      (new_to_old_by_newdefs_iso
        (remove_old_by_newdefs_iso iso (singleton i0)) 
        (singleton i0)).
  Proof.
    intros.
    unfold new_to_old_by_newdefs_iso; unfold remove_old_by_newdefs_iso.
    repeat
      match goal with
        | [|- context[AtomSetImpl.fold ?f (AtomSetImpl.singleton ?e) ?i]] =>
          let x := fresh "x" in
            let H1 := fresh "H1" in
              let H2 := fresh "H2" in
                destruct (AtomSetFacts2.fold_singleton_simpl
                  f (AtomSetImpl.singleton e) i e (AtomSetImpl.eq_refl _))
                as [x [H1 H2]]; subst; rewrite H2; clear H2        
      end.
    rr; rr in Hiso1; simpl.

    intros x Hx.
    destruct x as [x [|]].

    Case "1. x has an old tag".
    destruct (id_dec x i0).

    { SCase "1.1. x = i0".
    subst x.
    remember (IdExtSetImpl.mem (vars_aux.add_ntag i0)
      (IdExtSetImpl.remove (vars_aux.add_otag i0) iso)) as bii; destruct bii;
    [|by apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [_ Hcontr]].
    rewrite IdExtSetFacts.remove_b in Heqbii.
    symmetry in Heqbii; apply andb_true_iff in Heqbii.
    destruct Heqbii as [Hii _].
    apply IdExtSetFacts.mem_iff in Hii.
    exploit Hiso1; eauto; intro Hfact; clear Hiso1.
    simpl; simpl in Hfact; clear igvs.
    destruct Hfact as [He|[igvs [Hlookup Hptr]]].
    - rewrite He; simpl; left; eapply lookupAL_deleteAL_eq; eauto.
    - rewrite Hlookup; simpl; right; exists igvs; split; [|done].
      eapply lookupAL_updateAddAL_eq; eauto.
    }

    { SCase "1.2. x <> i0".
    remember (IdExtSetImpl.mem (vars_aux.add_ntag i0)
      (IdExtSetImpl.remove (vars_aux.add_otag i0) iso)) as bii; destruct bii.
    - apply IdExtSetFacts.add_iff in Hx.
      destruct Hx as [Hcontr|Hx]; [by inv Hcontr; elim n|].
      apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      exploit Hiso1; eauto; intro Hfact; clear Hiso1.
      simpl; simpl in Hfact; clear igvs.
      destruct Hfact as [He|[igvs [Hlookup Hptr]]].
      + left; destruct (lookupAL GVs lc i0).
        * rewrite <-lookupAL_updateAddAL_neq; eauto.
        * rewrite lookupAL_deleteAL_neq; eauto.
      + right; exists igvs; split; [|done].
        destruct (lookupAL GVs lc i0).
        * rewrite <-lookupAL_updateAddAL_neq; eauto.
        * rewrite lookupAL_deleteAL_neq; eauto.
    - apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      exploit Hiso1; eauto; intro Hfact; clear Hiso1.
      simpl; simpl in Hfact; clear igvs.
      destruct Hfact as [He|[igvs [Hlookup Hptr]]].
      + left; destruct (lookupAL GVs lc i0).
        * rewrite <-lookupAL_updateAddAL_neq; eauto.
        * rewrite lookupAL_deleteAL_neq; eauto.
      + right; exists igvs; split; [|done].
        destruct (lookupAL GVs lc i0).
        * rewrite <-lookupAL_updateAddAL_neq; eauto.
        * rewrite lookupAL_deleteAL_neq; eauto.
    }

    Case "2. x has a new tag".
    destruct (id_dec x i0).

    { SCase "2.1. x = i0; contradiction".
    subst x; elimtype False; clear -Hx.
    remember (IdExtSetImpl.mem (vars_aux.add_ntag i0)
      (IdExtSetImpl.remove (vars_aux.add_otag i0) iso)) as bii; destruct bii.
    - apply IdExtSetFacts.add_iff in Hx; destruct Hx as [Hx|Hx]; [done|].
      apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [_ Hx]; done.
    - apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      symmetry in Heqbii; rewrite IdExtSetFacts.remove_b in Heqbii.
      apply andb_false_iff in Heqbii; destruct Heqbii as [Heqbii|Heqbii].
      + apply IdExtSetFacts2.F.mem_iff in Hx.
        unfold vars_aux.add_ntag in Heqbii; rewrite Hx in Heqbii; done.
      + apply negb_false_iff in Heqbii.
        unfold vars_aux.add_ntag, vars_aux.add_otag in Heqbii.
        unfold IdExtSetFacts.eqb in Heqbii.
        unfold id in *.
        destruct (IdExtSetFacts.eq_dec (i0, ntag_old) (i0, ntag_new)); done.
    }

    SCase "2.2. x <> i0".
    remember (IdExtSetImpl.mem (vars_aux.add_ntag i0)
      (IdExtSetImpl.remove (vars_aux.add_otag i0) iso)) as bii; destruct bii.
    - apply IdExtSetFacts.add_iff in Hx.
      destruct Hx as [Hcontr|Hx]; [by inv Hcontr; elim n|].
      apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      exploit Hiso1; eauto; intro Hfact; clear Hiso1.
      simpl; simpl in Hfact.
      destruct Hfact as [He|[xgvs [Hlookup Hptr]]].
      + left; rewrite <-lookupAL_updateAddAL_neq; eauto.
      + right; exists xgvs; split; [|done].
        rewrite <-lookupAL_updateAddAL_neq; eauto.
    - apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      exploit Hiso1; eauto; intro Hfact; clear Hiso1.
      simpl; simpl in Hfact.
      destruct Hfact as [He|[xgvs [Hlookup Hptr]]].
      + left; rewrite <-lookupAL_updateAddAL_neq; eauto.
      + right; exists xgvs; split; [|done].
        rewrite <-lookupAL_updateAddAL_neq; eauto.
  Qed.

  Lemma oldnew_preserves_iso_sem:
    forall cfg fn_al ec ec' ecs ecs' mem mem' ns ns' na' tr nd ocmd olc li iso
      (Hstep1 : logical_semantic_step cfg fn_al
        {| EC := ec; ECS := ecs; Mem := mem |}
        {| EC := ec'; ECS := ecs'; Mem := mem' |} ns ns' na' tr)
      (Hpop1: pop_state_ocmd (ec :: ecs) ns ocmd)
      (Hncall: forall rid : id, is_general_call ocmd rid -> False)
      (Hnd: nd = vars_aux.def_cmd_opt ocmd)
      (Hsu1: self_use_check ocmd = true)
      (Hiso1: isolated_sem (CurTargetData cfg) olc (Locals ec) li iso),
      isolated_sem (CurTargetData cfg) (update_olc_by_ocmd olc (Locals ec) ocmd)
      (Locals ec') li (new_to_old_by_newdefs_iso (remove_old_by_newdefs_iso iso nd) nd).
  Proof.
    intros. admit. (*
    destruct ocmd as [cmd|]; destruct_lstep_tac.

    - simpl in *; subst.
      remember (vars_aux.def_cmd cmd) as cmdid; destruct cmdid.
    
      + exploit def_cmd_inl_implies_locals_update; eauto; intros [igvs Hec'].
        eapply oldnew_preserves_iso_sem_cmd; eauto.

      + unfold remove_old_by_newdefs_iso;
        repeat rewrite AtomSetProperties.fold_1b; try done.
        unfold new_to_old_by_newdefs_iso;
        repeat rewrite AtomSetProperties.fold_1b; try done.
        destruct cmd; try done; destruct_step_tac.

    - simpl in *; subst.
      unfold remove_old_by_newdefs_iso;
      repeat rewrite AtomSetProperties.fold_1b; try done.
      unfold new_to_old_by_newdefs_iso;
      repeat rewrite AtomSetProperties.fold_1b; try done.
      by destruct Hstep as [Heceq Heqtr]; inv Heceq; subst. *)
  Qed.

  Lemma oldnew_preserves_hint_sem_each:
    forall md inv1 inv2 iso1 iso2 iso1' iso2' alpha' gmax nd1 nd2 nd md' inv1' inv2'
      (Hsu1: self_use_check ocmd1 = true)
      (Hsu2: self_use_check ocmd2 = true)
      (Hnd1: nd1 = vars_aux.def_cmd_opt ocmd1)
      (Hnd2: nd2 = vars_aux.def_cmd_opt ocmd2)
      (Hnd: nd = AtomSetImpl.inter nd1 nd2)
      (Hmd': md' = new_to_old_md_by_newdefs (remove_old_md_by_newdefs md nd) nd)
      (Hinv1': inv1' = new_to_old_by_newdefs (remove_old_by_newdefs inv1 nd1) nd1)
      (Hinv2': inv2' = new_to_old_by_newdefs (remove_old_by_newdefs inv2 nd2) nd2)
      (Hiso1': iso1' = new_to_old_by_newdefs_iso
        (remove_old_by_newdefs_iso iso1 nd1) nd1)
      (Hiso2': iso2' = new_to_old_by_newdefs_iso
        (remove_old_by_newdefs_iso iso2 nd2) nd2)
      

      (Hsem: hint_sem_each md inv1 inv2 iso1 iso2
        alpha' gmax cfg1 cfg2 r1 r2 mem1 mem2
        li1 pi1 li2 pi2 als1' als2' mem1' mem2'),

      (vars_aux.is_defined_same_id ocmd1 ocmd2 = false /\
        (hint_sem_each
          (maydiff_add_def_all_opt (maydiff_add_def_all_opt md' ocmd1) ocmd2)
          inv1' inv2' iso1' iso2'
          alpha' gmax cfg1 cfg2 r1' r2' mem1 mem2
          li1 pi1 li2 pi2 als1' als2' mem1' mem2')) \/
      (vars_aux.is_defined_same_id ocmd1 ocmd2 = true /\
        (hint_sem_each
          (maydiff_add_def_new_opt (maydiff_add_def_new_opt md' ocmd1) ocmd2)
          inv1' inv2' iso1' iso2'
          alpha' gmax cfg1 cfg2 r1' r2' mem1 mem2
          li1 pi1 li2 pi2 als1' als2' mem1' mem2')).

  Proof.
    intros. admit. (*
    remember (vars_aux.is_defined_same_id ocmd1 ocmd2) as bsame; destruct bsame.

    Case "1. is_defined_same_id".
    right; split; [done|].

    destruct Hsem as [[olc1 [olc2 [Hmd Hinv]]] Hiav]; split; [|done]; clear Hiav.
    exists (update_olc_by_ocmd olc1 (Locals ec1) ocmd1).
    exists (update_olc_by_ocmd olc2 (Locals ec2) ocmd2).
    split.

    { SCase "1.1. maydiff_sem".
    clear Hinv; unfold r1, r2, r1', r2' in *.

    destruct ocmd1 as [cmd1|]; destruct_lstep_tac.
    - destruct ocmd2 as [cmd2|]; destruct_lstep_tac.
      + remember (vars_aux.def_cmd cmd1) as cmd1id.
        remember (vars_aux.def_cmd cmd2) as cmd2id.
        destruct cmd1id, cmd2id.
        * unfold vars_aux.is_defined_same_id in Heqbsame; simpl in Heqbsame.
          rewrite <- Heqcmd1id, <- Heqcmd2id in *.
          apply AtomSetFacts2.eq_dec_singleton_eq in Heqbsame; subst.
          exploit def_cmd_inl_implies_locals_update; try eapply Heqcmd1id; eauto;
            intros [igv1 Hec1']; rewrite Hec1' in *; clear Hec1'.
          exploit def_cmd_inl_implies_locals_update; try eapply Heqcmd2id; eauto;
            intros [igv2 Hec2']; rewrite Hec2' in *; clear Hec2'.
          eapply oldnew_preserves_maydiff_sem_aux; eauto.

        * unfold vars_aux.is_defined_same_id in Heqbsame; simpl in Heqbsame.
          rewrite <- Heqcmd1id, <- Heqcmd2id in Heqbsame.
          by rewrite <- AtomSetFacts2.eq_dec_singleton_false_1 in Heqbsame.
        * unfold vars_aux.is_defined_same_id in Heqbsame; simpl in Heqbsame.
          rewrite <- Heqcmd1id, <- Heqcmd2id in Heqbsame.
          by rewrite <- AtomSetFacts2.eq_dec_singleton_false_2 in Heqbsame.
        * simpl.
          rewrite <- Heqcmd1id, <- Heqcmd2id.
          hexploit AtomSetProperties.empty_inter_1; try by instantiate (1:=empty).
          instantiate (1:= empty).
          intro Hempty; unfold remove_old_md_by_newdefs, new_to_old_md_by_newdefs.
          repeat rewrite AtomSetProperties.fold_1b; try by apply Hempty.
          destruct cmd1, cmd2; try done;
          destruct_step_tac; inv Hstep; inv Hstep0; done.

      + simpl; destruct Hstep0 as [Heceq0 _]; inv Heceq0.
        hexploit AtomSetProperties.empty_inter_2; try by instantiate (1:=empty).
        instantiate (1:= (vars_aux.def_cmd_opt (ret cmd1))).
        intro Hempty; unfold remove_old_md_by_newdefs, new_to_old_md_by_newdefs.        
        repeat rewrite AtomSetProperties.fold_1b; try by apply Hempty.

        remember (vars_aux.def_cmd cmd1) as cmd1id; destruct cmd1id.
        * elimtype False.
          unfold vars_aux.is_defined_same_id in Heqbsame; simpl in Heqbsame.
          rewrite <- Heqcmd1id in Heqbsame; clear -Heqbsame.
          by rewrite <- AtomSetFacts2.eq_dec_singleton_false_1 in Heqbsame.

        * by destruct cmd1; try done; destruct_step_tac.

    - simpl; destruct Hstep as [Heceq _]; inv Heceq.
      hexploit AtomSetProperties.empty_inter_1; try by instantiate (1:=empty).
      instantiate (1:= (vars_aux.def_cmd_opt ocmd2)).
      intro Hempty; unfold remove_old_md_by_newdefs, new_to_old_md_by_newdefs.
      repeat rewrite AtomSetProperties.fold_1b; try by apply Hempty.

      destruct ocmd2 as [cmd2|]; destruct_lstep_tac.
      + remember (vars_aux.def_cmd cmd2) as cmd2id; destruct cmd2id.
        * elimtype False.
          unfold vars_aux.is_defined_same_id in Heqbsame; simpl in Heqbsame.
          rewrite <- Heqcmd2id in Heqbsame; clear -Heqbsame.
          by rewrite <- AtomSetFacts2.eq_dec_singleton_false_2 in Heqbsame.

        * by destruct cmd2; try done; destruct_step_tac.

      + by simpl; destruct Hstep as [Heceq _]; inv Heceq.
    }

    { SCase "1.2. invariant_sem".
    unfold r1, r2, r1', r2' in *; destruct Hinv as [Heqs1 [Heqs2 [Hiso1 Hiso2]]].
    rr; splits; simpl in *; subst.
    - eapply oldnew_preserves_eqs_sem; eauto.
    - eapply oldnew_preserves_eqs_sem; eauto.
    - eapply oldnew_preserves_iso_sem; eauto.
    - eapply oldnew_preserves_iso_sem; eauto.
    }

    Case "2. not is_defined_same_id".
    left; split; [done|].
    hexploit is_defined_same_id_false_implies_inter_empty; eauto; intro Hndempty.
    rewrite <- Hnd1, <- Hnd2, <- Hnd in Hndempty.
    unfold remove_old_md_by_newdefs in Hmd'; simpl in Hmd'.
    rewrite AtomSetProperties.fold_1b in Hmd';
      try by apply AtomSetProperties.empty_is_empty_2.
    unfold new_to_old_md_by_newdefs in Hmd'.
    rewrite AtomSetProperties.fold_1b in Hmd';
      try by apply AtomSetProperties.empty_is_empty_2.
    rewrite Hmd' in *; clear Hmd'.
    rewrite Hinv1', Hinv2' in *; clear Hinv1' Hinv2'.

    destruct Hsem as [[olc1 [olc2 [Hmd Hinv]]] Hiav]; split; [|done]; clear Hiav.
    exists (update_olc_by_ocmd olc1 (Locals ec1) ocmd1).
    exists (update_olc_by_ocmd olc2 (Locals ec2) ocmd2).
    split.

    { SCase "2.1. maydiff_sem".
    clear Hinv; unfold r1, r2, r1', r2' in *.

    assert (Hbridge:
      maydiff_sem (Locals ec1') (Locals ec2) alpha'
      (update_olc_by_ocmd olc1 (Locals ec1) ocmd1) olc2
      (maydiff_add_def_all_opt md ocmd1)).
    - destruct ocmd1 as [cmd1|]; destruct_lstep_tac.
      + simpl.
        remember (vars_aux.def_cmd cmd1) as cmd1id; destruct cmd1id.

        * unfold maydiff_add_def_all; rewrite <- Heqcmd1id.

          destruct cmd1; try done;
          try (by simpl in Heqcmd1id; inv Heqcmd1id;
            destruct ec, ec1'; simpl in *; unfold pop_one_X in Heqpop;
            destruct (noop_idx_zero_exists hpn); try done;
            destruct CurCmds0; try done;
            inv Heqpop; inv Hstep;
            try destruct (isGVZero TD c);
            eapply update_preserves_maydiff_sem_left; eauto).
          by elim (Hncall1 id5).

        * by destruct cmd1; try done;
          unfold maydiff_add_def_all; rewrite <- Heqcmd1id;
          destruct_step_tac.

      + by destruct Hstep as [Heceq _]; inv Heceq.

    - destruct ocmd2 as [cmd2|]; destruct_lstep_tac.
      + simpl.
        remember (vars_aux.def_cmd cmd2) as cmd2id; destruct cmd2id.

        * unfold maydiff_add_def_all; rewrite <- Heqcmd2id.

          destruct cmd2; try done;
          try (by simpl in Heqcmd2id; inv Heqcmd2id;
            destruct ec, ec2'; simpl in *; unfold pop_one_X in Heqpop;
            destruct (noop_idx_zero_exists hpn); try done;
            destruct CurCmds0; try done;
            inv Heqpop; inv Hstep;
            try destruct (isGVZero TD c);
            eapply update_preserves_maydiff_sem_right; eauto).
          by elim (Hncall2 id5).

        * by destruct cmd2; try done;
          unfold maydiff_add_def_all; rewrite <- Heqcmd2id;
          destruct_step_tac.

      + by destruct Hstep as [Heceq _]; inv Heceq.
    }

    SCase "2.2. invariant_sem".
    unfold r1, r2, r1', r2' in *; destruct Hinv as [Heqs1 [Heqs2 [Hiso1 Hiso2]]].
    rr; splits; simpl.
    - eapply oldnew_preserves_eqs_sem; eauto.
    - eapply oldnew_preserves_eqs_sem; eauto.
    - subst; eapply oldnew_preserves_iso_sem; eauto.
    - subst; eapply oldnew_preserves_iso_sem; eauto. *)
  Qed.

End HintSemEach.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)

