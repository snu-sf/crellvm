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
Require Import hint_sem_aux_void.
Require Import logical_step.

Require Import hint_sem_props_proceed_oldnew.
Require Import hint_sem_props_proceed_step_defs.
Require Import hint_sem_props_proceed_call.

Require Import FSetFacts.

Import Opsem.
Import syntax_ext.
Import hints.

Definition retval_update_void st : (@Opsem.ECStack DGVs) :=
  match st with
    | nil => st
    | ec::ecs => 
      match ec with
        | mkEC cf cb cc t lc als =>
          (mkEC
            cf
            cb
            (match cc with
               | nil => nil
               | c::cc => cc
             end)
            t
            lc als)
          ::ecs
      end
  end.

Definition is_void_call (ocmd:monad cmd) : bool :=
  match ocmd with
    | ret insn_call _ true _ _ _ _ _ => true
    | _ => false
  end.

Lemma call_maydiff_add_preserves_maydiff_sem_left':
  forall lc1 lc2 olc1 olc2 alpha' md ocmd1
    (Hcall1: is_void_call ocmd1)
    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md),
    maydiff_sem lc1 lc2
    alpha' (update_olc_by_ocmd olc1 lc1 ocmd1) olc2
    (maydiff_add_def_all_opt md ocmd1).
Proof.
  intros; destruct ocmd1 as [[]|]; inv Hcall1.
  destruct noret5; [|done].
  simpl. unfold maydiff_add_def_all. simpl.
  by apply update_preserves_maydiff_sem_left'.
Qed.

Lemma call_maydiff_add_preserves_maydiff_sem_right':
  forall lc1 lc2 olc1 olc2 alpha' md ocmd2
    (Hcall2: is_void_call ocmd2)
    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md),
    maydiff_sem lc1 lc2
    alpha' olc1 (update_olc_by_ocmd olc2 lc2 ocmd2)
    (maydiff_add_def_all_opt md ocmd2).
Proof.
  intros; destruct ocmd2 as [[]|]; inv Hcall2.
  destruct noret5; [|done].
  simpl. unfold maydiff_add_def_all. simpl.
  by apply update_preserves_maydiff_sem_right'.
Qed.

Lemma oldnew_preserves_maydiff_sem_aux':
  forall i1 lc1 lc2 alpha' md olc1 olc2 cmd1 cmd2
    (Hmd : maydiff_sem lc1 lc2 alpha' olc1 olc2 md)
    (Heqcmd1id: inl i1 = vars_aux.def_cmd cmd1)
    (Heqcmd2id: inl i1 = vars_aux.def_cmd cmd2),
    maydiff_sem lc1 lc2 alpha'
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
  Case "Step 2: wrapping new_to_old_md_by_newdefs".
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
  }
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
  Case "Step 3: polishing, using Haleq1 and Haleq2".
  unfold maydiff_sem in *; intros x Hx.
  remember (Hstep2 _ Hx) as Hbrd; clear HeqHbrd Hstep2.
  unfold variable_equivalent in *.
  destruct x as [x [|]].
  { unfold lookupALExt in *; by repeat rewrite <- Haleq1; rewrite <- Haleq2. }
  { unfold lookupALExt in *; done. }
  

  clear Haleq1 Haleq2 Hstep2.

  assert (Hstep4: maydiff_sem
    (updateAddAL_opt _ (deleteAL _ lc1 i1) i1 (lookupAL _ lc1 i1))
    (updateAddAL_opt _ (deleteAL _ lc2 i1) i1 (lookupAL _ lc2 i1)) alpha'
    (update_olc_by_ocmd olc1 lc1 (ret cmd1))
    (update_olc_by_ocmd olc2 lc2 (ret cmd2))
    (IdExtSetImpl.add (vars_aux.add_ntag i1)
      (IdExtSetImpl.add (vars_aux.add_ntag i1)
        (new_to_old_md_by_newdefs
          (remove_old_md_by_newdefs md
            (AtomSetImpl.inter (singleton i1) (singleton i1)))
          (AtomSetImpl.inter (singleton i1) (singleton i1)))))).
  Case "Step 4: wrapping newtag adds".
  remember (new_to_old_md_by_newdefs
    (remove_old_md_by_newdefs md
      (AtomSetImpl.inter (singleton i1) (singleton i1)))
    (AtomSetImpl.inter (singleton i1) (singleton i1))) as md'.
  remember (deleteAL GVs lc1 i1) as ec'.
  remember (deleteAL GVs lc2 i1) as ec0'.
  unfold maydiff_sem in *; intros x Hx.
  destruct (id_ext_dec (i1, ntag_new) x).
  { subst x; elimtype False; clear -Hx.
    rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx.
    destruct Hx as [Hcontr _].
    unfold vars_aux.add_ntag, IdExtSetFacts.eqb in Hcontr.
    by destruct (IdExtSetFacts.eq_dec (i1, ntag_new) (i1, ntag_new)).
  }
  { rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx; destruct Hx as [_ Hx].
    rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx; destruct Hx as [_ Hx].
    remember (Hstep3 _ Hx) as Hres; clear HeqHres Hstep3.
    unfold variable_equivalent in *.
    destruct x as [x [|]]; [done|].
    destruct (id_dec i1 x); [by subst x; elim n|].
    unfold lookupALExt in *.
    by repeat rewrite lookupAL_updateAddAL_opt_neq; eauto.
  }
  clear Hstep3.

  assert (Haleq1: eqAL _
    (updateAddAL_opt GVs (deleteAL GVs lc1 i1) i1 (lookupAL GVs lc1 i1))
    lc1).
  { by apply eqAL_updateAddAL_opt_deleteAL. }

  assert (Haleq2: eqAL _
    (updateAddAL_opt GVs (deleteAL GVs lc2 i1) i1 (lookupAL GVs lc2 i1))
    lc2).
  { by apply eqAL_updateAddAL_opt_deleteAL. }

  (* Final step! *)
  unfold maydiff_sem in *; intros x Hx.
  remember (Hstep4 _ Hx) as Hres; clear HeqHres Hstep4.
  unfold variable_equivalent in *.
  destruct x as [x [|]]; [done|].
  unfold lookupALExt in *.
  by rewrite <- Haleq1, <- Haleq2; eauto.
Qed.

Require Import vars_aux.

Lemma oldnew_preserves_eq_reg_sem':
  forall i0 y r cfg lc lc' olc mem gmax igvs
    (Hec': lc' = (updateAddAL_opt GVs lc i0 igvs))
    (Hnot: negb (IdExtSetImpl.mem (add_otag i0)
      (IdExtSetImpl.add y (vars_aux.used_locals_in_rhs r))) = true)
    (Hsem: eq_reg_sem cfg olc lc mem gmax y r),
    eq_reg_sem cfg (match lookupAL GVs lc i0 with
                      | ret xv => updateAddAL GVs olc i0 xv
                      | merror => deleteAL GVs olc i0
                    end)
    lc' mem gmax (new_to_old_local_in_id i0 y) (new_to_old_local_in_rhs i0 r).
Proof.
  intros.
  inv Hsem; simpl in *.

  Case "1. normal value".
  eapply eq_reg_sem_value; eauto; simpl in *.
  { destruct y as [y [|]]; simpl in *.
    + destruct (id_dec i0 y); try subst; simpl in *.
      * elimtype False; clear -Hnot.
        rewrite IdExtSetFacts.add_b in Hnot.
        apply negb_true_iff in Hnot.
        apply orb_false_iff in Hnot; destruct Hnot as [Hcontr _].
        unfold add_otag, IdExtSetFacts.eqb in Hcontr.
        by destruct (IdExtSetFacts.eq_dec (y, ntag_old) (y, ntag_old)).
      * destruct (lookupAL GVs lc i0);
        [rewrite <- lookupAL_updateAddAL_neq; eauto|
          rewrite lookupAL_deleteAL_neq; eauto].
    + destruct (id_dec i0 y); try subst; simpl in *.
      * by rewrite Hlookup; apply lookupAL_updateAddAL_eq.
      * rewrite lookupAL_updateAddAL_opt_neq; eauto.
  }

  { destruct r; try (inv Hrhs; fail); simpl in Hnot; mem_destruct_tac.

    (* BOP *)
    + inv Hrhs; econstructor.
      unfold BOPEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      remember (getOperandValueExt (CurTargetData cfg) w olc lc (Globals cfg))
      as wov; destruct wov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt' in Heqvov; eauto.
      symmetry in Heqwov; eapply oldnew_preserves_getOperandValueExt' in Heqwov; eauto.
      rewrite Heqvov, Heqwov.
      done.

    (* FBOP *)
    + inv Hrhs; econstructor; unfold FBOPEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      remember (getOperandValueExt (CurTargetData cfg) w olc lc (Globals cfg))
      as wov; destruct wov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt' in Heqvov; eauto.
      symmetry in Heqwov; eapply oldnew_preserves_getOperandValueExt' in Heqwov; eauto.
      by rewrite Heqvov, Heqwov.

    (* ExtractValue *)
    + inv Hrhs; apply rhs_ext_extractvalue_sem with (gvs:=gvs0); [|done].
      eapply oldnew_preserves_getOperandValueExt'; eauto.

    (* InsertValue *)
    + inv Hrhs; apply rhs_ext_insertvalue_sem with (gvs:=gvs0) (gvs':=gvs'0);
      [| |done]; eapply oldnew_preserves_getOperandValueExt'; eauto.

    (* GEP *)
    + inv Hrhs; eapply rhs_ext_gep_sem; eauto.
      * eapply oldnew_preserves_getOperandValueExt'; eauto.
      * clear Hlookup Heqgvs H11 H10 gvs gvs'. (* for simple induction *)
        generalize dependent vidxss.
        induction lsv as [|[sa va] lsv]; [done|].
        intros; simpl.
        unfold used_locals_in_lsv in H2; simpl in H2.
        mem_destruct_tac.
        inv H9.
        remember (getOperandValueExt (CurTargetData cfg) va olc
          lc (Globals cfg)) as vaov; destruct vaov; [|done].
        symmetry in Heqvaov; eapply oldnew_preserves_getOperandValueExt' in Heqvaov;
          eauto.
        rewrite Heqvaov.
        destruct (values2GVsExt (CurTargetData cfg) lsv olc lc (Globals cfg));
          try done.
        hexploit IHlsv; try done.
        by intros Hind; rewrite Hind.

    (* TRUNC *)
    + inv Hrhs; econstructor; unfold TRUNCEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt' in Heqvov; eauto.
      by rewrite Heqvov.

    (* EXT *)
    + inv Hrhs; econstructor; unfold EXTEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt' in Heqvov; eauto.
      by rewrite Heqvov.

    (* CAST *)
    + inv Hrhs; econstructor; unfold CASTEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt' in Heqvov; eauto.
      by rewrite Heqvov.

    (* ICMP *)
    + inv Hrhs; econstructor; unfold ICMPEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      remember (getOperandValueExt (CurTargetData cfg) w olc lc (Globals cfg))
      as wov; destruct wov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt' in Heqvov; eauto.
      symmetry in Heqwov; eapply oldnew_preserves_getOperandValueExt' in Heqwov; eauto.
      by rewrite Heqvov, Heqwov.

    (* FCMP *)
    + inv Hrhs; econstructor; unfold FCMPEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      remember (getOperandValueExt (CurTargetData cfg) w olc lc (Globals cfg))
      as wov; destruct wov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt' in Heqvov; eauto.
      symmetry in Heqwov; eapply oldnew_preserves_getOperandValueExt' in Heqwov; eauto.
      by rewrite Heqvov, Heqwov.

    (* SELECT *)
    + inv Hrhs; [eapply rhs_ext_select_true_sem|eapply rhs_ext_select_false_sem]; eauto;
      eapply oldnew_preserves_getOperandValueExt'; eauto.

    (* Value *)
    + inv Hrhs; eapply rhs_ext_value__sem.
      eapply oldnew_preserves_getOperandValueExt'; eauto.
  }

  Case "2. old_alloca_old".
  eapply eq_reg_sem_old_alloca; eauto.
  rewrite negb_true_iff in Hnot.
  rewrite IdExtSetFacts.add_b in Hnot; apply orb_false_iff in Hnot.
  destruct Hnot as [Hneq _].
  unfold add_otag, IdExtSetFacts.eqb in Hneq.
  match goal with [H: context [IdExtSetFacts.eq_dec ?a ?b] |- _] =>
    (destruct (IdExtSetFacts.eq_dec a b); [done|]) end.
  clear Hneq.

  destruct y as [y [|]].
  - simpl; destruct (id_dec i0 y); [by subst y; elim n|].
    simpl; simpl in Hlookup.
    destruct (lookupAL GVs lc i0);
      [by rewrite <- lookupAL_updateAddAL_neq; eauto|
        by rewrite lookupAL_deleteAL_neq; eauto].
  - simpl; destruct (id_dec i0 y); simpl; simpl in Hlookup.
    + by subst; rewrite Hlookup; rewrite lookupAL_updateAddAL_eq.
    + by rewrite lookupAL_updateAddAL_opt_neq; eauto.

Qed.

Lemma oldnew_preserves_eq_heap_sem':
  forall i p t a v cfg lc lc' olc mem igvs
    (Hec': lc' = (updateAddAL_opt GVs lc i igvs))
    (Hnot: negb (IdExtSetImpl.mem (vars_aux.add_otag i)
      (IdExtSetImpl.union (vars_aux.used_locals_in_value p)
        (vars_aux.used_locals_in_value v))) = true)
    (Hsem: eq_heap_sem cfg olc lc mem p t a v),
    eq_heap_sem cfg (match lookupAL GVs lc i with
                      | ret xv => updateAddAL GVs olc i xv
                      | merror => deleteAL GVs olc i
                    end)
    lc' mem (new_to_old_local_in_value i p) t a (new_to_old_local_in_value i v).
Proof.
  intros.
  unfold eq_heap_sem in Hsem.
  remember (getOperandValueExt (CurTargetData cfg) p olc lc (Globals cfg))
  as pove; destruct pove; [|done].
  remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
  as vove; destruct vove; [|done].

  unfold eq_heap_sem; mem_destruct_tac.
  symmetry in Heqpove; eapply oldnew_preserves_getOperandValueExt' in Heqpove; eauto.
  symmetry in Heqvove; eapply oldnew_preserves_getOperandValueExt' in Heqvove; eauto.
  by rewrite Heqpove, Heqvove.
Qed.

Lemma oldnew_preserves_neq_reg_sem':
  forall i ii lg cfg lc lc' olc igvs
    (Hec': lc' = (updateAddAL_opt GVs lc i igvs))
    (Hnot: negb (IdExtSetImpl.mem (vars_aux.add_otag i)
      (IdExtSetImpl.add ii (vars_aux.used_locals_in_localglobal lg))) = true)
    (Hsem: neq_reg_sem cfg olc lc ii lg),
    neq_reg_sem cfg (match lookupAL GVs lc i with
                      | ret xv => updateAddAL GVs olc i xv
                      | merror => deleteAL GVs olc i
                    end)
    lc' (new_to_old_local_in_id i ii) (new_to_old_local_in_localglobal i lg).
Proof.
  intros; mem_destruct_tac.
  unfold neq_reg_sem in *.
  remember (logical_step.lookupALExt olc lc ii) as vii; destruct vii; [|done].
  symmetry in Heqvii; eapply oldnew_preserves_lookup' in Heqvii; eauto;
    [|by simpl; rewrite IdExtSetFacts.singleton_b; apply H].
  rewrite Heqvii.

  destruct lg as [i|gi]; [|done]; simpl.
  remember (logical_step.lookupALExt olc lc i) as vi; destruct vi; [|done].
  symmetry in Heqvi; eapply oldnew_preserves_lookup' in Heqvi; eauto.
  by rewrite Heqvi.
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

  Lemma oldnew_preserves_eqs_sem_cmd':
    forall cfg olc lc lc' mem0 gmax inv i0 igvs
    (Heqs1: eqs_sem cfg olc lc mem0 gmax inv)
    (Hec': lc' = updateAddAL_opt GVs lc i0 igvs),
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
      eapply oldnew_preserves_eq_reg_sem'; eauto.
      

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
      eapply oldnew_preserves_eq_heap_sem'; eauto.

    - intros i l Hilmem'.
      unfold new_to_old_local_in_neq_reg in Hilmem'.
      exploit NeqRegSetFacts2.in_fold_exists; eauto.
      intros [il [Hilmem Hiln2o]]; inv Hiln2o.
      unfold filter_local_in_eqs_neq_reg in Hilmem.
      rewrite NeqRegSetFacts.filter_b in Hilmem;
        try (by unfold compat_bool, Proper, "==>"; intros; subst).
      apply andb_true_iff in Hilmem; destruct Hilmem as [Hilmem Hilfilt].
      destruct il as [i lg]; simpl in *.
      eapply oldnew_preserves_neq_reg_sem'; eauto.
  Qed.

  Lemma oldnew_preserves_eqs_sem':
    forall cfg fn_al ec ec' ecs ecs' mem mem' gmax ns ns' na' tr inv nd ocmd olc
      (Hstep1 : logical_semantic_step cfg fn_al
        {| ECS := ec :: ecs; Mem := mem |}
        {| ECS := ec' :: ecs'; Mem := mem' |} ns ns' na' tr)
      (Hpop1: pop_state_ocmd (ec :: ecs) ns ocmd)
      (Hncall: forall rid : id, is_general_call ocmd rid -> False)
      (Hnd: nd = vars_aux.def_cmd_opt ocmd)
      (Hsu1: self_use_check ocmd = true)
      (Heqs1: eqs_sem cfg olc (Locals ec) mem gmax inv),
      eqs_sem cfg (update_olc_by_ocmd olc (Locals ec) ocmd)
      (Locals ec') mem gmax
      (new_to_old_by_newdefs (remove_old_by_newdefs inv nd) nd).
  Proof.
    intros.
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
      by destruct Hstep as [Heceq Heqtr]; inv Heceq; subst.
  Qed.

  Lemma oldnew_preserves_iso_sem_cmd':
    forall cfg olc lc lc' iso li i0 igvs
      (Hiso1 : isolated_sem (CurTargetData cfg) olc lc li iso)
      (Hec': lc' = updateAddAL_opt GVs lc i0 igvs),
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

    SCase "1.1. x = i0".
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
    { rewrite He; simpl; left; eapply lookupAL_deleteAL_eq; eauto. }
    { rewrite Hlookup; simpl; right; exists igvs; split; [|done].
      eapply lookupAL_updateAddAL_eq; eauto.
    }

    SCase "1.2. x <> i0".
    remember (IdExtSetImpl.mem (vars_aux.add_ntag i0)
      (IdExtSetImpl.remove (vars_aux.add_otag i0) iso)) as bii; destruct bii.
    { apply IdExtSetFacts.add_iff in Hx.
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
    }
    { apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
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

    SCase "2.1. x = i0; contradiction".
    subst x; elimtype False; clear -Hx.
    remember (IdExtSetImpl.mem (vars_aux.add_ntag i0)
      (IdExtSetImpl.remove (vars_aux.add_otag i0) iso)) as bii; destruct bii.
    { apply IdExtSetFacts.add_iff in Hx; destruct Hx as [Hx|Hx]; [done|].
      apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [_ Hx]; done.
    }
    { apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
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
    { apply IdExtSetFacts.add_iff in Hx.
      destruct Hx as [Hcontr|Hx]; [by inv Hcontr; elim n|].
      apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      exploit Hiso1; eauto; intro Hfact; clear Hiso1.
      simpl; simpl in Hfact.
      destruct Hfact as [He|[xgvs [Hlookup Hptr]]].
      + left; rewrite lookupAL_updateAddAL_opt_neq; eauto.
      + right; exists xgvs; split; [|done].
        rewrite lookupAL_updateAddAL_opt_neq; eauto.
    }
    { apply IdExtSetFacts.remove_iff in Hx; destruct Hx as [Hx _].
      exploit Hiso1; eauto; intro Hfact; clear Hiso1.
      simpl; simpl in Hfact.
      destruct Hfact as [He|[xgvs [Hlookup Hptr]]].
      + left; rewrite lookupAL_updateAddAL_opt_neq; eauto.
      + right; exists xgvs; split; [|done].
        rewrite lookupAL_updateAddAL_opt_neq; eauto.
    }
  Qed.
End HintSemEach.

Lemma eqAL_lookupALExt olc lc1 lc2 v
  (H: eqAL _ lc1 lc2) :
  lookupALExt olc lc1 v = lookupALExt olc lc2 v.
Proof.
  destruct v. destruct n; [done|]. simpl.
  apply H.
Qed.

Lemma eqAL_getOperandValueExt lc1 lc2 td v olc gl
  (H: eqAL _ lc1 lc2) :
  getOperandValueExt td v olc lc1 gl = getOperandValueExt td v olc lc2 gl.
Proof.
  destruct v; [|done]. simpl.
  by apply eqAL_lookupALExt.
Qed.

Lemma eqAL_values2GVsExt lc1 lc2 td vs olc gl
  (H: eqAL _ lc1 lc2) :
  values2GVsExt td vs olc lc1 gl = values2GVsExt td vs olc lc2 gl.
Proof.
  induction vs; [done|].
  destruct a. simpl.
  erewrite eqAL_getOperandValueExt; eauto.
  destruct (getOperandValueExt td v olc lc2 gl); [|done].
  by rewrite IHvs.
Qed.

Lemma eqAL_rhs_ext_value_sem cfg olc lc1 lc2 r v
  (H: eqAL _ lc1 lc2)
  (Hsem: rhs_ext_value_sem cfg olc lc1 r v) :
  rhs_ext_value_sem cfg olc lc2 r v.
Proof.
  inv Hsem.
  - econs; eauto. unfold BOPEXT in *.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto. unfold FBOPEXT in *.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto;
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
    by erewrite <- eqAL_values2GVsExt; eauto.
  - econs; eauto. unfold TRUNCEXT in *.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto. unfold EXTEXT in *.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto. unfold CASTEXT in *.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto. unfold ICMPEXT in *.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto. unfold FCMPEXT in *.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - eapply rhs_ext_select_false_sem; eauto.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - econs; eauto.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
Qed.

Lemma eqAL_eqs_sem cfg olc lc1 lc2 mem gmax e
  (Hsem: eqs_sem cfg olc lc1 mem gmax e)
  (Hlc: eqAL _ lc1 lc2) :
  eqs_sem cfg olc lc2 mem gmax e.
Proof.
  destruct Hsem as [H1 [H2 H3]]. unfold eqs_sem. splits.
  - intros x r Hx. exploit H1; eauto. intro H. inv H.
    + econs; eauto.
      * erewrite <- eqAL_lookupALExt; eauto.
      * eapply eqAL_rhs_ext_value_sem; eauto.
    + eapply eq_reg_sem_old_alloca; eauto.
      erewrite <- eqAL_lookupALExt; eauto.
  - intros x t a v Hx. exploit H2; eauto. intro H.
    unfold eq_heap_sem in *.
    repeat (erewrite <- (eqAL_getOperandValueExt lc1 lc2); [|by eauto]); eauto.
  - intros x v Hx. exploit H3; eauto. intro H.
    unfold neq_reg_sem in *.
    erewrite <- eqAL_lookupALExt; eauto. destruct (lookupALExt olc lc1 x); [|done].
    destruct v; [|done].
    erewrite <- eqAL_lookupALExt; eauto.
Qed.

Lemma eqAL_isolated_sem td olc lc1 lc2 li iso
  (Hsem: isolated_sem td olc lc1 li iso)
  (Hlc: eqAL _ lc1 lc2) :
  isolated_sem td olc lc2 li iso.
Proof.
  intros x Hx. exploit Hsem; eauto. intros [H|H].
  - left. erewrite <- eqAL_lookupALExt; eauto.
  - destruct H as [gvp [Hgvp H]].
    right. exists gvp. split; auto.
    erewrite <- eqAL_lookupALExt; eauto.
Qed.

Lemma eqAL_updateAddAL_opt X m x :
  eqAL X (updateAddAL_opt _ m x (lookupAL _ m x)) m.
Proof.
  intro y. destruct (id_dec y x); [subst|].
  - by rewrite lookupAL_updateAddAL_opt_eq.
  - by rewrite lookupAL_updateAddAL_opt_neq.
Qed.

Lemma call_oldnew_preserves_hint_sem':
  forall ocmd1 ocmd2 nd1 nd2 nd md md' inv1 inv2 inv1' inv2'
    cfg1 cfg2 lc1 lc2 mem1 mem2 alpha' gmax olc1 olc2 iso1 iso2 iso1' iso2' li1 li2
    (Hcall1: is_void_call ocmd1)
    (Hcall2: is_void_call ocmd2)
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


    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md)
    (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2)),

    ((vars_aux.is_defined_same_id ocmd1 ocmd2 = false /\
      maydiff_sem lc1 lc2
      alpha' (update_olc_by_ocmd olc1 lc1 ocmd1) (update_olc_by_ocmd olc2 lc2 ocmd2)
      (maydiff_add_def_all_opt (maydiff_add_def_all_opt md' ocmd1) ocmd2)) \/
    (vars_aux.is_defined_same_id ocmd1 ocmd2 = true /\
      maydiff_sem lc1 lc2
      alpha' (update_olc_by_ocmd olc1 lc1 ocmd1) (update_olc_by_ocmd olc2 lc2 ocmd2)
      (maydiff_add_def_new_opt (maydiff_add_def_new_opt md' ocmd1) ocmd2)))
    /\
    invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2
    (update_olc_by_ocmd olc1 lc1 ocmd1) (update_olc_by_ocmd olc2 lc2 ocmd2) gmax
    li1 li2 (mkInvariant inv1' inv2' iso1' iso2').
Proof.
  intros; split.

  Case "1. maydiff_sem".
  remember (vars_aux.is_defined_same_id ocmd1 ocmd2) as bs; destruct bs.

  SCase "1.1. return with same id".
  right; subst md'.
  unfold vars_aux.is_defined_same_id in Heqbs; simpl.

  split; [done|].

  destruct ocmd1 as [cmd1|]; [|done].
  destruct ocmd2 as [cmd2|]; [|done].
  simpl in Hnd1, Hnd2.
  remember (vars_aux.def_cmd cmd1) as dcmd1; destruct dcmd1; [|by destruct cmd1].
  remember (vars_aux.def_cmd cmd2) as dcmd2; destruct dcmd2; [|by destruct cmd2].
  simpl in Heqbs; rewrite <-Heqdcmd1, <-Heqdcmd2 in Heqbs.
  exploit AtomSetFacts2.eq_dec_singleton_eq.
  { instantiate (1:=i1). instantiate (1:=i0).
    destruct (AtomSetImpl.eq_dec (singleton i0) (singleton i1)); done.
  }
  intro; subst.

  hexploit oldnew_preserves_maydiff_sem_aux'.
  { apply Hmd. }
  { apply Heqdcmd1. }
  { apply Heqdcmd2. }
  intro Hmdfact.

  destruct cmd1; try done; destruct cmd2; try done.
  simpl in *; subst; simpl in *.
  inv Heqdcmd1; inv Heqdcmd2; done.

  SCase "1.2. return with different id".
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

  eapply call_maydiff_add_preserves_maydiff_sem_right'; eauto.
  eapply call_maydiff_add_preserves_maydiff_sem_left'; eauto.

  SCase "2. invariant_sem".
  destruct Hinv as [Hinv1 [Hinv2 [Hiso1 Hiso2]]].
  rr; splits; simpl in *; try done.

  - destruct ocmd1 as [cmd1|]; [|done].
    destruct cmd1; try done; simpl in *.
    rewrite Hinv1'. subst.
    eapply eqAL_eqs_sem; [by eapply oldnew_preserves_eqs_sem_cmd'; eauto|].
    by apply eqAL_updateAddAL_opt.
  - destruct ocmd2 as [cmd2|]; [|done].
    destruct cmd2; try done; simpl in *.
    rewrite Hinv2'; subst.
    eapply eqAL_eqs_sem; [by eapply oldnew_preserves_eqs_sem_cmd'; eauto|].
    by apply eqAL_updateAddAL_opt.
  - destruct ocmd1 as [cmd1|]; [|done].
    destruct cmd1; try done; simpl in *. subst.
    eapply eqAL_isolated_sem; [by eapply oldnew_preserves_iso_sem_cmd'; eauto|].
    by apply eqAL_updateAddAL_opt.
  - destruct ocmd2 as [cmd2|]; [|done].
    destruct cmd2; try done; simpl in *. subst.
    eapply eqAL_isolated_sem; [by eapply oldnew_preserves_iso_sem_cmd'; eauto|].
    by apply eqAL_updateAddAL_opt.
Qed.

Ltac des_same_cmd_tac :=
  repeat match goal with
           | [H: true = is_same_cmd _ _ _ _ _ _ _ |- _] =>
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

Lemma call_update_md_preserves_maydiff_sem':
  forall ocmd1 ocmd2 md md' inv1 inv2
    cfg1 cfg2 lc1 lc2 mem1 mem2 alpha' gmax olc1 olc2 iso1 iso2 li1 li2
    (Hcall1: is_void_call ocmd1)
    (Hcall2: is_void_call ocmd2)
    (Hsu1: self_use_check ocmd1 = true)
    (Hsu2: self_use_check ocmd2 = true)

    (Hinv: invariant_sem cfg1 cfg2 lc1 lc2
      mem1 mem2 olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hmd': md' = maydiff_update_opt md inv1 inv2 ocmd1 ocmd2)

    (Hmd: (vars_aux.is_defined_same_id ocmd1 ocmd2 = false /\
      maydiff_sem lc1 lc2
      alpha' olc1 olc2
      (maydiff_add_def_all_opt (maydiff_add_def_all_opt md ocmd1) ocmd2)) \/
    (vars_aux.is_defined_same_id ocmd1 ocmd2 = true /\
      maydiff_sem lc1 lc2
      alpha' olc1 olc2
      (maydiff_add_def_new_opt (maydiff_add_def_new_opt md ocmd1) ocmd2))),

    maydiff_sem lc1 lc2
    alpha' olc1 olc2 md'.
Proof.
  intros.
  destruct ocmd1 as [cmd1|]; [|done]; destruct ocmd2 as [cmd2|]; [|done].
  destruct Hmd as [[Hndef Hmd]|[Hdef Hmd]].

  Case "1. return with different id".
  rewrite Hmd'.
  remember (is_same_cmd md inv1 inv2 cmd1 cmd2) as bsame; destruct bsame.
  { simpl; simpl in Hmd.
    unfold maydiff_update_opt, maydiff_update.
    rewrite <- Heqbsame.
    destruct cmd1, cmd2; try done.
    simpl in Heqbsame.
    des_same_cmd_tac.
    destruct (id_dec id5 id0); try done; subst.
    unfold vars_aux.is_defined_same_id in Hndef; simpl in Hndef.
    destruct (AtomSetImpl.eq_dec (singleton id0) (singleton id0)) as [|Hcontr]; try done.
    elim Hcontr; done.
  }

  { unfold maydiff_update_opt, maydiff_update.
    rewrite <- Heqbsame.
    destruct (vars_aux.is_defined_same_id (ret cmd1) (ret cmd2)); done.
  }

  Case "2. return with same id".
  destruct cmd1; try done; destruct cmd2; try done; simpl in *; subst.
  destruct noret5; [|done]. destruct noret0; [|done].
  unfold vars_aux.is_defined_same_id in Hdef; simpl in Hdef.
  exploit AtomSetFacts2.eq_dec_singleton_eq; eauto; intro.
  subst.
  unfold maydiff_add_def_new in Hmd; simpl in Hmd.
  unfold maydiff_sem in *; intros.
  destruct (id_ext_dec (id0, ntag_new) x).

  - subst; unfold variable_equivalent; simpl.
    unfold maydiff_update in H. simpl in H.
    destruct (id_dec id0 id0); [|done]. simpl in H.
    unfold is_defined_same_id in H. simpl in H.
    destruct (AtomSetImpl.eq_dec (singleton id0) (singleton id0)); [|done]. simpl in H.
    unfold maydiff_add_def_new in H. unfold def_cmd in H.
    rewrite IdExtSetFacts2.F.add_b in H. apply orb_false_iff in H. destruct H as [H _].
    unfold add_ntag in H.
    unfold IdExtSetFacts2.F.eqb in H.
    by destruct (IdExtSetFacts.eq_dec (id0, ntag_new) (id0, ntag_new)).

  - unfold maydiff_update in H; simpl in H.
    unfold vars_aux.is_defined_same_id in H; simpl in H.
    match goal with [H: context[if ?a then _ else _] |- _] => destruct a end.
    + eapply Hmd; repeat rewrite IdExtSetFacts.add_b.
      apply orb_false_iff; split.
      unfold vars_aux.add_ntag, IdExtSetFacts.eqb.
      match goal with [ |- context[IdExtSetFacts.eq_dec ?a ?b]] =>
        (destruct (IdExtSetFacts.eq_dec a b); done) end.
      apply orb_false_iff; split.
      unfold vars_aux.add_ntag, IdExtSetFacts.eqb.
      match goal with [ |- context[IdExtSetFacts.eq_dec ?a ?b]] =>
        (destruct (IdExtSetFacts.eq_dec a b); done) end.
      done.
    + destruct (AtomSetImpl.eq_dec (singleton id0) (singleton id0)); [|done].
      simpl in H. unfold maydiff_add_def_new in H; simpl in H.
      eapply Hmd; rewrite IdExtSetFacts.add_b.
      apply orb_false_iff; split.
      unfold vars_aux.add_ntag, IdExtSetFacts.eqb.
      match goal with [ |- context[IdExtSetFacts.eq_dec ?a ?b]] =>
        (destruct (IdExtSetFacts.eq_dec a b); done) end.
      done.
Qed.

Definition read_only_function_id m ocmd :=
  match ocmd with
    | ret cmd =>
      match cmd with
        | insn_call _ _ _ _ _ fv _ =>
          match fv with
            | value_id fid
            | value_const (const_gid _ fid) =>
              match lookupFdecViaIDFromModule m fid with
                | ret fdec_intro (fheader_intro (fnattrs_intro _ _ _ _ a) _ _ _ _)
                  _ =>
                  in_dec attribute_dec attribute_readnone a \/
                  in_dec attribute_dec attribute_readonly a
                | merror => False
              end \/
              match lookupFdefViaIDFromModule m fid with
                | ret fdef_intro (fheader_intro (fnattrs_intro _ _ _ _ a) _ _ _ _)
                  _ =>
                  in_dec attribute_dec attribute_readnone a \/
                  in_dec attribute_dec attribute_readonly a
                | merror => False
              end
            | _ => False
          end
        | _ => False
      end
    | _ => False
  end.

Lemma call_hfilter_preserves_invariant_sem_aux':
  forall ocmd mem mem' gmax inv inv' cfg olc lc m
    (Hcall: is_void_call ocmd)
    (Hro: read_only_function_id m ocmd -> memory_extends (CurTargetData cfg) mem' mem)
    (Hsu: self_use_check ocmd = true)
    (Hmem: Mem.nextblock mem <= Mem.nextblock mem')
    (Hinv': inv' = filter_eq_heap_by_only_read_memory_value m ocmd inv)
    (Hinv: eqs_sem cfg olc lc mem gmax inv),
    eqs_sem cfg olc lc mem' gmax inv'.
Proof.
  intros; destruct ocmd as [cmd|]; [|done]; destruct cmd; try done; simpl in *.
  destruct inv as [ireg iheap inreg].
  unfold filter_eq_heap_by_only_read_memory_value in Hinv'.
  destruct inv' as [ireg' iheap' inreg']; inv Hinv'.
  (* unfold vars_aux.stale_alloca; simpl. *)
  unfold eqs_sem; splits; simpl.

  Case "1. register equations: involved only with old_alloca".
  destruct Hinv as [Hreg _]; simpl in Hreg.
  unfold eqs_eq_reg_sem in *; intros.
  exploit Hreg; eauto; intro Hrege; clear Hreg.
  inv Hrege; [by eapply eq_reg_sem_value; eauto|].
  eapply eq_reg_sem_old_alloca; eauto.
  omega.

  Case "2. heap equations: involved only with heap filter".
  destruct Hinv as [_ [Hheap Hnreg]]; simpl in *.
  remember (only_read_memory_value m value0) as bro; destruct bro.

  SCase "2.1. readonly".
  destruct value0; try done.
  { simpl in Heqbro; unfold only_read_memory in Heqbro.
    symmetry in Heqbro; rewrite orb_true_iff in Heqbro.
    destruct Heqbro as [Heqbrol|Heqbrog].
    + exploit Hro. left.
      destruct (lookupFdecViaIDFromModule m id0); [|done].
      destruct f. destruct fheader5. destruct fnattrs5.
      simpl in Heqbrol.
      apply orb_true_iff in Heqbrol; destruct Heqbrol; [by left|by right].
      by eapply memory_extends_prop.
    + exploit Hro. right.
      destruct (lookupFdefViaIDFromModule m id0); [|done].
      destruct f. destruct fheader5. destruct fnattrs5.
      simpl in Heqbrog.
      apply orb_true_iff in Heqbrog; destruct Heqbrog; [by left|by right].
      by eapply memory_extends_prop.
  }
  { simpl in Heqbro.
    destruct const5; try done.
    unfold only_read_memory in Heqbro.
    symmetry in Heqbro; rewrite orb_true_iff in Heqbro.
    destruct Heqbro as [Heqbrol|Heqbrog].
    + exploit Hro. left.
      destruct (lookupFdecViaIDFromModule m id0); [|done].
      destruct f. destruct fheader5. destruct fnattrs5.
      simpl in Heqbrol.
      apply orb_true_iff in Heqbrol; destruct Heqbrol; [by left|by right].
      by eapply memory_extends_prop.
    + exploit Hro. right.
      destruct (lookupFdefViaIDFromModule m id0); [|done].
      destruct f. destruct fheader5. destruct fnattrs5.
      simpl in Heqbrog.
      apply orb_true_iff in Heqbrog; destruct Heqbrog; [by left|by right].
      by eapply memory_extends_prop.
  }

  SCase "2.2. not readonly".
  unfold eqs_eq_heap_sem; intros.
  rewrite EqHeapSetFacts.empty_b in H; done.

  Case "3. register non-equations: not changed".
  destruct Hinv as [_ [_ Hnreg]]; simpl in Hnreg; done.
Qed.

Lemma call_addneq_preserves_invariant_sem':
  forall ocmd1 ocmd2 inv1 inv2 cfg1 cfg2 lc1 lc2
    mem1 mem2 iso1 iso2 gmax li1 li2 olc1 olc2 gids1 gids2
    (Hcall1: is_void_call ocmd1)
    (Hcall2: is_void_call ocmd2)

    (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2)),
    invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2
    olc1 olc2 gmax li1 li2 (mkInvariant (vars_aux.add_pointer_non_equations inv1 ocmd1 gids1)
      (vars_aux.add_pointer_non_equations inv2 ocmd2 gids2) iso1 iso2).
Proof.
  intros.
  destruct ocmd1 as [cmd1|]; [|done]; destruct ocmd2 as [cmd2|]; [|done].
  destruct cmd1; try done; destruct cmd2; try done.
Qed.

Lemma call_hfilter_preserves_invariant_sem':
  forall ocmd1 ocmd2 inv1 inv2 inv1' inv2' mem1' mem2'
    m1 m2 li1 pi1 li2 pi2 cfg1 cfg2 lc1 lc2 mem1 mem2 alpha' gmax olc1 olc2
    iso1 iso2
    (Hcall1: is_void_call ocmd1)
    (Hcall2: is_void_call ocmd2)
    (Hro1: read_only_function_id m1 ocmd1 ->
      memory_extends (CurTargetData cfg1) mem1' mem1)
    (Hro2: read_only_function_id m2 ocmd2 ->
      memory_extends (CurTargetData cfg2) mem2' mem2)
    (Hsu1: self_use_check ocmd1 = true)
    (Hsu2: self_use_check ocmd2 = true)

    (Hmem': valid_memories alpha' gmax mem1' mem2' li1 pi1 li2 pi2)
    (Hmem1: Mem.nextblock mem1 <= Mem.nextblock mem1')
    (Hmem2: Mem.nextblock mem2 <= Mem.nextblock mem2')
    (Hinv1': inv1' = filter_eq_heap_by_only_read_memory_value m1 ocmd1 inv1)
    (Hinv2': inv2' = filter_eq_heap_by_only_read_memory_value m2 ocmd2 inv2)

    (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2)),
    invariant_sem cfg1 cfg2 lc1 lc2 mem1' mem2'
    olc1 olc2 gmax li1 li2 (mkInvariant inv1' inv2' iso1 iso2).
Proof.
  intros.
  destruct Hinv as [Hinv1 [Hinv2 [Hiso1 Hiso2]]];
    rr; splits; simpl in *; try done.
  - eapply call_hfilter_preserves_invariant_sem_aux';
    try eapply Hinv1'; try eapply Hinv1''; eauto.
  - eapply call_hfilter_preserves_invariant_sem_aux';
    try eapply Hinv2'; try eapply Hinv2''; eauto.
Qed.

Lemma call_addcmd_preserves_invariant_sem':
  forall ocmd1 ocmd2 inv1 inv2 cfg1 cfg2 lc1 lc2 mem1 mem2 gmax olc1 olc2
    iso1 iso2 li1 li2
    (Hcall1: is_void_call ocmd1)
    (Hcall2: is_void_call ocmd2)

    (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2)),
    invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2
    olc1 olc2 gmax li1 li2 (mkInvariant
      (vars_aux.add_ntag_option_cmd_to_eqs inv1 ocmd1)
      (vars_aux.add_ntag_option_cmd_to_eqs inv2 ocmd2) 
      (register_isolated_pointers_orig ocmd1 ocmd2 iso1)
      (register_isolated_pointers_opt ocmd1 ocmd2 iso2)).
Proof.
  intros.
  destruct ocmd1 as [cmd1|]; [|done]; destruct ocmd2 as [cmd2|]; [|done].
  destruct cmd1; try done; destruct cmd2; try done.
Qed.

Lemma invariant_proceed_preserves_hint_sem_insn_call':
  forall m1 m2 hint nhint pecs1 pecs2 ptns1 ptns2 pi1 li1 pi2 li2
    alpha gmax cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2
    ocmd1 ocmd2 pec1 pec2

    (Hsim: hint_sem_insn hint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha gmax cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2)
    (Hpec1: pst1 = pec1::pecs1) (Hpec2: pst2 = pec2::pecs2)
    (Hpop1: pop_state_ocmd pst1 pns1 ocmd1)
    (Hpop2: pop_state_ocmd pst2 pns2 ocmd2)
    (Hprc: invariant_proceed m1 m2 hint ocmd1 ocmd2 = ret nhint)

    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hwfm: wf_sb_mi gmax alpha pmem1 pmem2)

    (Hcall1: is_void_call ocmd1)
    (Hcall2: is_void_call ocmd2),

    forall alpha' (Haincr: inject_incr' alpha alpha' li1 pi1 li2 pi2)
      (* knows everything about mem1' and mem2', which will be proved
         when we begin to prove the refinement property. *)
      mem1' mem2'
      (Hvmem: valid_memories alpha' gmax mem1' mem2' li1 pi1 li2 pi2)
      (Hvals: valid_allocas mem1' mem2' (Allocas pec1) (Allocas pec2))
      (Hmem1: Mem.nextblock pmem1 <= Mem.nextblock mem1')
      (Hmem2: Mem.nextblock pmem2 <= Mem.nextblock mem2')

      (Heqm1: is_call_readonly m1 (mkState pst1 pmem1) ->
        memory_extends (CurTargetData cfg1) mem1' pmem1)
      (Heqm2: is_call_readonly m2 (mkState pst2 pmem2) ->
        memory_extends (CurTargetData cfg2) mem2' pmem2),

    hint_sem_insn nhint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha' gmax cfg1 (retval_update_void pst1) mem1' (decrease_top pns1)
      cfg2 (retval_update_void pst2) mem2' (decrease_top pns2).
Proof.
  intros; inv Hsim; inv H2; inv H6.
  destruct pec1 as [cf1 cb1 cc1 t1 lc1 als1], pec2 as [cf2 cb2 cc2 t2 lc2 als2];
    simpl in *.

  (* Gathering information from invariant_proceed. *)
  simpl; move Hsem at bottom; destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
  destruct hint as [md [inv1 inv2 iso1 iso2] ir]; simpl in *.
  move Hprc at bottom; unfold invariant_proceed in Hprc; simpl in Hprc.
  remember (heap_eq_check md inv1 inv2 iso1 iso2 ocmd1 ocmd2) as hcheck;
    destruct hcheck; [|done]; simpl in Hprc; symmetry in Heqhcheck.
  remember (self_use_check ocmd1) as su1; destruct su1; [|done]; simpl in Hprc.
  remember (self_use_check ocmd2) as su2; destruct su2; [|done]; simpl in Hprc.
  symmetry in Heqsu1, Heqsu2.
  inv Hprc; simpl.

  eapply hint_sem_insn_intro; try done.

  Case "1. hint_sem".
  exists (update_olc_by_ocmd olc1 lc1 ocmd1).
  exists (update_olc_by_ocmd olc2 lc2 ocmd2).

  (* A. increasing alpha *)
  hexploit inject_incr_preserves_maydiff_sem; eauto; clear Hmd; intro Hmd.

  (* B. remove old / new to old *)
  hexploit call_oldnew_preserves_hint_sem'; try reflexivity.
  { apply Hcall1. }
  { apply Hcall2. }
  { apply Heqsu1. }
  { apply Heqsu2. }  
  { apply Hmd. }
  { apply Hinv. }
  clear Hmd Hinv; intros [Hmd Hinv].

  (* C. update maydiff *)
  hexploit call_update_md_preserves_maydiff_sem'.
  { apply Hcall1. }
  { apply Hcall2. }
  { apply Heqsu1. }
  { apply Heqsu2. }
  { apply Hinv. }
  { reflexivity. }
  { apply Hmd. }
  clear Hmd; intros Hmd.

  (* D. eliminating addneq: no neq's are added. *)
  hexploit call_addneq_preserves_invariant_sem'.
  { apply Hcall1. }
  { apply Hcall2. }
  { apply Hinv. }
  instantiate (1:=(collect_global_ids (get_products_from_module m2))).
  instantiate (1:=(collect_global_ids (get_products_from_module m1))).
  clear Hinv; intros Hinv.

  (* D. filter / stale *)
  hexploit call_hfilter_preserves_invariant_sem'.
  { apply Hcall1. }
  { apply Hcall2. }
  { instantiate (1:=pmem1). instantiate (1:=mem1').
    instantiate (1:=cfg1). instantiate (1:=m1).
    destruct ocmd1 as [cmd1|]; [|done]; destruct cmd1; try done; simpl in *.
    move Hpop1 at bottom.
    remember (pop_one_X cc1 n1) as pop1; destruct pop1; [|done].
    unfold pop_one_X in Heqpop1.
    destruct (noop_idx_zero_exists n1); [by rewrite <-Hpop1 in Heqpop1|].
    destruct cc1; [done|].
    inv Heqpop1; inv H0.
    destruct value0; try done.
  }
  { instantiate (1:=pmem2). instantiate (1:=mem2').
    instantiate (1:=cfg2). instantiate (1:=m2).
    destruct ocmd2 as [cmd2|]; [|done]; destruct cmd2; try done; simpl in *.
    move Hpop2 at bottom.
    remember (pop_one_X cc2 n2) as pop2; destruct pop2; [|done].
    unfold pop_one_X in Heqpop2.
    destruct (noop_idx_zero_exists n2); [by rewrite <-Hpop2 in Heqpop2|].
    destruct cc2; [done|].
    inv Heqpop2; inv H0.
    destruct value0; try done.
  }
  { apply Heqsu1. }
  { apply Heqsu2. }
  { apply Hvmem. }
  { auto. }
  { auto. }
  { reflexivity. }
  { reflexivity. }
  { apply Hinv. }
  clear Hinv; intros Hinv.

  (* E. eliminating addcmd: call_insn's are not added. *)
  hexploit call_addcmd_preserves_invariant_sem'.
  { apply Hcall1. }
  { apply Hcall2. }
  { apply Hinv. }
  clear Hinv; intros Hinv.
  simpl in *.

  (* Done! *)
  done.

  Case "2. allocas_equivalent".
  simpl; move Haequiv at bottom.
  eapply alpha_incr_preserves_allocas_equivalent; eauto.

  Case "3. globals_equivalent".
  simpl; move Hgequiv at bottom.
  eapply alpha_incr_preserves_globals_equivalent; eauto.

Qed.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
