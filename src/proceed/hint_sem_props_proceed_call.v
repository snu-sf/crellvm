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

Require Import hint_sem_props_proceed_oldnew.
Require Import hint_sem_props_proceed_step_defs.

Require Import FSetFacts.

Import Opsem.
Import syntax_ext.
Import hints.

Definition retval_update st rid rv : (@Opsem.ECStack DGVs) :=
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
            (updateAddAL _ lc rid rv) als)
          ::ecs
      end
  end.

Definition decrease_top ns : noop_stack_t :=
  match ns with
    | nil => nil
    | n::ns => (noop_idx_decrease n)::ns
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

Inductive memory_extends TD (mem1 mem2:mem) : Prop :=
| memory_extends_intro:
  forall
    (Hextends: forall ptr typ align val
      (Hval: ret val = mload TD mem2 ptr typ align),
      ret val = mload TD mem1 ptr typ align),
    memory_extends TD mem1 mem2.

Lemma memory_extends_prop
  cfg olc lc mem1 mem2 ih
  (Hsem: eqs_eq_heap_sem cfg olc lc mem2 ih)
  (Hext: memory_extends (CurTargetData cfg) mem1 mem2) :
  eqs_eq_heap_sem cfg olc lc mem1 ih.
Proof.
  intros ptr typ align rhs Heq.
  generalize (Hsem ptr typ align rhs Heq). clear Hsem.
  unfold eq_heap_sem.
  destruct (getOperandValueExt (CurTargetData cfg) ptr olc lc (Globals cfg)); [|done].
  destruct (getOperandValueExt (CurTargetData cfg) rhs olc lc (Globals cfg)); [|done].
  intros H mp Hmp.
  generalize (H mp Hmp). clear H.
  inv Hext. inv Hmp.
  generalize (Hextends mp typ align). clear Hextends.
  destruct (mload (CurTargetData cfg) mem2 mp typ align); [|done].
  intro H.
  by rewrite <- (H g eq_refl).
Qed.

Lemma inject_incr_preserves_maydiff_sem:
  forall lc1 lc2 alpha alpha' olc1 olc2 md li1 pi1 li2 pi2
    (Haincr: inject_incr' alpha alpha' li1 pi1 li2 pi2)
    (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md),
    maydiff_sem lc1 lc2 alpha' olc1 olc2 md.
Proof.
  intros.
  unfold maydiff_sem in *; intros; exploit Hmd; eauto; intro Hbrd; clear Hmd.
  unfold variable_equivalent in *.
  destruct (lookupALExt olc1 lc1 x); [|done].
  destruct (lookupALExt olc2 lc2 x); [|done].
  destruct Haincr as [Haincr _]; eapply gv_inject_incr; eauto.
Qed.

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

Ltac call_destruct_tac :=
  match goal with
    | [H1: is_general_call ?ocmd1 ?rid1, H2: is_general_call ?ocmd2 ?rid2 |- _] =>
      let cmd1 := fresh "cmd1" in let cmd2 := fresh "cmd2" in
      destruct ocmd1 as [cmd1|]; [|done]; destruct ocmd2 as [cmd2|]; [|done];
      destruct cmd1; try done; destruct cmd2; try done; simpl in *; subst rid1 rid2
  end.

Lemma call_maydiff_add_preserves_maydiff_sem_left:
  forall lc1 lc2 olc1 olc2 alpha' md ocmd1 rid1 rv1
    (Hcall1: is_general_call ocmd1 rid1)
    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md),
    maydiff_sem (updateAddAL GVs lc1 rid1 rv1) lc2
    alpha' (update_olc_by_ocmd olc1 lc1 ocmd1) olc2
    (maydiff_add_def_all_opt md ocmd1).
Proof.
  intros; destruct ocmd1 as [cmd1|]; [|done].
  simpl.
  remember (vars_aux.def_cmd cmd1) as cmd1id; destruct cmd1id.
  - unfold maydiff_add_def_all; rewrite <- Heqcmd1id.
    destruct cmd1; try done.
    simpl in *; inv Heqcmd1id.
    eapply update_preserves_maydiff_sem_left; eauto.
  - by destruct cmd1.
Qed.

Lemma call_maydiff_add_preserves_maydiff_sem_right:
  forall lc1 lc2 olc1 olc2 alpha' md ocmd2 rid2 rv2
    (Hcall1: is_general_call ocmd2 rid2)
    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md),
    maydiff_sem lc1 (updateAddAL GVs lc2 rid2 rv2)
    alpha' olc1 (update_olc_by_ocmd olc2 lc2 ocmd2)
    (maydiff_add_def_all_opt md ocmd2).
Proof.
  intros; destruct ocmd2 as [cmd2|]; [|done].
  simpl.
  remember (vars_aux.def_cmd cmd2) as cmd2id; destruct cmd2id.
  - unfold maydiff_add_def_all; rewrite <- Heqcmd2id.
    destruct cmd2; try done.
    simpl in *; inv Heqcmd2id.
    eapply update_preserves_maydiff_sem_right; eauto.
  - by destruct cmd2.
Qed.

Lemma call_oldnew_preserves_hint_sem:
  forall ocmd1 ocmd2 rid1 rid2 rv1 rv2 nd1 nd2 nd md md' inv1 inv2 inv1' inv2'
    cfg1 cfg2 lc1 lc2 mem1 mem2 alpha' gmax olc1 olc2 iso1 iso2 iso1' iso2' li1 li2
    (Hcall1: is_general_call ocmd1 rid1)
    (Hcall2: is_general_call ocmd2 rid2)
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
      maydiff_sem (updateAddAL GVs lc1 rid1 rv1) (updateAddAL GVs lc2 rid2 rv2)
      alpha' (update_olc_by_ocmd olc1 lc1 ocmd1) (update_olc_by_ocmd olc2 lc2 ocmd2)
      (maydiff_add_def_all_opt (maydiff_add_def_all_opt md' ocmd1) ocmd2)) \/
    (vars_aux.is_defined_same_id ocmd1 ocmd2 = true /\
      maydiff_sem (updateAddAL GVs lc1 rid1 rv1) (updateAddAL GVs lc2 rid2 rv2)
      alpha' (update_olc_by_ocmd olc1 lc1 ocmd1) (update_olc_by_ocmd olc2 lc2 ocmd2)
      (maydiff_add_def_new_opt (maydiff_add_def_new_opt md' ocmd1) ocmd2)))
    /\
    invariant_sem cfg1 cfg2 (updateAddAL GVs lc1 rid1 rv1)
    (updateAddAL GVs lc2 rid2 rv2) mem1 mem2
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
  - instantiate (1:=i1). instantiate (1:=i0).
    destruct (AtomSetImpl.eq_dec (singleton i0) (singleton i1)); done.
  intro; subst.

  hexploit oldnew_preserves_maydiff_sem_aux.
  - apply Hmd. - apply Heqdcmd1. - apply Heqdcmd2.
  instantiate (1:=rv2). instantiate (1:=rv1).
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

  eapply call_maydiff_add_preserves_maydiff_sem_right; eauto.
  eapply call_maydiff_add_preserves_maydiff_sem_left; eauto.

  SCase "2. invariant_sem".
  destruct Hinv as [Hinv1 [Hinv2 [Hiso1 Hiso2]]].
  rr; splits; simpl in *; try done.

  - destruct ocmd1 as [cmd1|]; [|done].
    destruct cmd1; try done; simpl in *.
    rewrite Hinv1'; subst; eapply oldnew_preserves_eqs_sem_cmd; eauto.
  - destruct ocmd2 as [cmd2|]; [|done].
    destruct cmd2; try done; simpl in *.
    rewrite Hinv2'; subst; eapply oldnew_preserves_eqs_sem_cmd; eauto.
  - destruct ocmd1 as [cmd1|]; [|done].
    destruct cmd1; try done; simpl in *.
    subst; eapply oldnew_preserves_iso_sem_cmd; eauto.
  - destruct ocmd2 as [cmd2|]; [|done].
    destruct cmd2; try done; simpl in *.
    subst; eapply oldnew_preserves_iso_sem_cmd; eauto.
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

Lemma call_update_md_preserves_maydiff_sem:
  forall ocmd1 ocmd2 rid1 rid2 md md' inv1 inv2 rv1 rv2
    cfg1 cfg2 lc1 lc2 mem1 mem2 alpha' gmax olc1 olc2 iso1 iso2 li1 li2
    (Hcall1: is_general_call ocmd1 rid1)
    (Hcall2: is_general_call ocmd2 rid2)
    (Hsu1: self_use_check ocmd1 = true)
    (Hsu2: self_use_check ocmd2 = true)

    (Hinv: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 rid1 rv1) (updateAddAL GVs lc2 rid2 rv2)
      mem1 mem2 olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hrv: gv_inject alpha' rv1 rv2)
    (Hmd': md' = maydiff_update_opt md inv1 inv2 ocmd1 ocmd2)

    (Hmd: (vars_aux.is_defined_same_id ocmd1 ocmd2 = false /\
      maydiff_sem (updateAddAL GVs lc1 rid1 rv1) (updateAddAL GVs lc2 rid2 rv2)
      alpha' olc1 olc2
      (maydiff_add_def_all_opt (maydiff_add_def_all_opt md ocmd1) ocmd2)) \/
    (vars_aux.is_defined_same_id ocmd1 ocmd2 = true /\
      maydiff_sem (updateAddAL GVs lc1 rid1 rv1) (updateAddAL GVs lc2 rid2 rv2)
      alpha' olc1 olc2
      (maydiff_add_def_new_opt (maydiff_add_def_new_opt md ocmd1) ocmd2))),

    maydiff_sem (updateAddAL GVs lc1 rid1 rv1) (updateAddAL GVs lc2 rid2 rv2)
    alpha' olc1 olc2 md'.
Proof.
  intros.
  destruct ocmd1 as [cmd1|]; [|done]; destruct ocmd2 as [cmd2|]; [|done].
  destruct Hmd as [[Hndef Hmd]|[Hdef Hmd]].

  Case "1. return with different id".
  rewrite Hmd'.
  remember (is_same_cmd md inv1 inv2 cmd1 cmd2) as bsame; destruct bsame.
  - simpl; simpl in Hmd.
    unfold maydiff_update_opt, maydiff_update.
    rewrite <- Heqbsame.
    destruct cmd1, cmd2; try done.
    simpl in Heqbsame.
    des_same_cmd_tac.
    destruct (id_dec id5 id0); try done; subst.
    unfold vars_aux.is_defined_same_id in Hndef; simpl in Hndef.
    destruct (AtomSetImpl.eq_dec (singleton id0) (singleton id0)) as [|Hcontr]; try done.
    elim Hcontr; done.

  - unfold maydiff_update_opt, maydiff_update.
    rewrite <- Heqbsame.
    destruct (vars_aux.is_defined_same_id (ret cmd1) (ret cmd2)); done.

  Case "2. return with same id".
  destruct cmd1; try done; destruct cmd2; try done; simpl in *; subst.
  unfold vars_aux.is_defined_same_id in Hdef; simpl in Hdef.
  exploit AtomSetFacts2.eq_dec_singleton_eq; eauto; intro.
  subst.
  unfold maydiff_add_def_new in Hmd; simpl in Hmd.
  unfold maydiff_sem in *; intros.
  destruct (id_ext_dec (rid2, ntag_new) x).

  - subst; unfold variable_equivalent; simpl.
    repeat rewrite lookupAL_updateAddAL_eq; eauto.

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
    + destruct (AtomSetImpl.eq_dec (singleton rid2) (singleton rid2)); [|done].
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

Lemma call_hfilter_preserves_invariant_sem_aux:
  forall ocmd rid mem mem' gmax inv inv' cfg olc lc m
    (Hcall: is_general_call ocmd rid)
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
  - simpl in Heqbro; unfold only_read_memory in Heqbro.
    symmetry in Heqbro; rewrite orb_true_iff in Heqbro.
    destruct Heqbro as [Heqbrol|Heqbrog].
    + exploit Hro. left.
      destruct (lookupFdecViaIDFromModule m id5); [|done].
      destruct f. destruct fheader5. destruct fnattrs5.
      simpl in Heqbrol.
      apply orb_true_iff in Heqbrol; destruct Heqbrol; [by left|by right].
      by eapply memory_extends_prop.
    + exploit Hro. right.
      destruct (lookupFdefViaIDFromModule m id5); [|done].
      destruct f. destruct fheader5. destruct fnattrs5.
      simpl in Heqbrog.
      apply orb_true_iff in Heqbrog; destruct Heqbrog; [by left|by right].
      by eapply memory_extends_prop.
  - simpl in Heqbro.
    destruct const5; try done.
    unfold only_read_memory in Heqbro.
    symmetry in Heqbro; rewrite orb_true_iff in Heqbro.
    destruct Heqbro as [Heqbrol|Heqbrog].
    + exploit Hro. left.
      destruct (lookupFdecViaIDFromModule m id5); [|done].
      destruct f. destruct fheader5. destruct fnattrs5.
      simpl in Heqbrol.
      apply orb_true_iff in Heqbrol; destruct Heqbrol; [by left|by right].
      by eapply memory_extends_prop.
    + exploit Hro. right.
      destruct (lookupFdefViaIDFromModule m id5); [|done].
      destruct f. destruct fheader5. destruct fnattrs5.
      simpl in Heqbrog.
      apply orb_true_iff in Heqbrog; destruct Heqbrog; [by left|by right].
      by eapply memory_extends_prop.

  SCase "2.2. not readonly".
  unfold eqs_eq_heap_sem; intros.
  rewrite EqHeapSetFacts.empty_b in H; done.

  Case "3. register non-equations: not changed".
  destruct Hinv as [_ [_ Hnreg]]; simpl in Hnreg; done.
Qed.

Lemma call_addneq_preserves_invariant_sem:
  forall ocmd1 ocmd2 rid1 rid2 inv1 inv2 cfg1 cfg2 lc1 lc2
    mem1 mem2 iso1 iso2 gmax li1 li2 olc1 olc2 gids1 gids2
    (Hcall1: is_general_call ocmd1 rid1)
    (Hcall2: is_general_call ocmd2 rid2)

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

Lemma call_hfilter_preserves_invariant_sem:
  forall ocmd1 ocmd2 rid1 rid2 inv1 inv2 inv1' inv2' mem1' mem2'
    m1 m2 li1 pi1 li2 pi2 cfg1 cfg2 lc1 lc2 mem1 mem2 alpha' gmax olc1 olc2
    iso1 iso2
    (Hcall1: is_general_call ocmd1 rid1)
    (Hcall2: is_general_call ocmd2 rid2)
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
  - eapply call_hfilter_preserves_invariant_sem_aux;
    try eapply Hinv1'; try eapply Hinv1''; eauto.
  - eapply call_hfilter_preserves_invariant_sem_aux;
    try eapply Hinv2'; try eapply Hinv2''; eauto.
Qed.

Lemma call_addcmd_preserves_invariant_sem:
  forall ocmd1 ocmd2 rid1 rid2 inv1 inv2 cfg1 cfg2 lc1 lc2 mem1 mem2 gmax olc1 olc2
    iso1 iso2 li1 li2
    (Hcall1: is_general_call ocmd1 rid1)
    (Hcall2: is_general_call ocmd2 rid2)

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

Lemma invariant_proceed_preserves_hint_sem_insn_call:
  forall m1 m2 hint nhint pecs1 pecs2 ptns1 ptns2 pi1 li1 pi2 li2
    alpha gmax cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2
    ocmd1 ocmd2 rid1 rid2 pec1 pec2

    (Hsim: hint_sem_insn hint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha gmax cfg1 pst1 pmem1 pns1 cfg2 pst2 pmem2 pns2)
    (Hpec1: pst1 = pec1::pecs1) (Hpec2: pst2 = pec2::pecs2)
    (Hpop1: pop_state_ocmd pst1 pns1 ocmd1)
    (Hpop2: pop_state_ocmd pst2 pns2 ocmd2)
    (Hprc: invariant_proceed m1 m2 hint ocmd1 ocmd2 = ret nhint)

    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hwfm: wf_sb_mi gmax alpha pmem1 pmem2)

    (Hcall1: is_general_call ocmd1 rid1)
    (Hcall2: is_general_call ocmd2 rid2),

    forall alpha' (Haincr: inject_incr' alpha alpha' li1 pi1 li2 pi2)
      (* knows everything about mem1' and mem2', which will be proved
         when we begin to prove the refinement property. *)
      rv1 rv2 mem1' mem2'
      (Hvmem: valid_memories alpha' gmax mem1' mem2' li1 pi1 li2 pi2)
      (Hvals: valid_allocas mem1' mem2' (Allocas pec1) (Allocas pec2))
      (Hmem1: Mem.nextblock pmem1 <= Mem.nextblock mem1')
      (Hmem2: Mem.nextblock pmem2 <= Mem.nextblock mem2')

      (Hrv: gv_inject alpha' rv1 rv2)
      (Heqm1: is_call_readonly m1 (mkState pst1 pmem1) ->
        memory_extends (CurTargetData cfg1) mem1' pmem1)
      (Heqm2: is_call_readonly m2 (mkState pst2 pmem2) ->
        memory_extends (CurTargetData cfg2) mem2' pmem2),

    hint_sem_insn nhint pecs1 pecs2 ptns1 ptns2 pi1 pi2 li1 li2
      alpha' gmax cfg1 (retval_update pst1 rid1 rv1) mem1' (decrease_top pns1)
      cfg2 (retval_update pst2 rid2 rv2) mem2' (decrease_top pns2).
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
  hexploit call_oldnew_preserves_hint_sem; try reflexivity.
  - apply Hcall1. - apply Hcall2. - apply Heqsu1. - apply Heqsu2.
  - apply Hmd. - apply Hinv.
  instantiate (1:=rv2). instantiate (1:=rv1).
  clear Hmd Hinv; intros [Hmd Hinv].

  (* C. update maydiff *)
  hexploit call_update_md_preserves_maydiff_sem.
  - apply Hcall1. - apply Hcall2. - apply Heqsu1. - apply Heqsu2.
  - apply Hinv. - apply Hrv. - reflexivity. - apply Hmd.
  clear Hmd; intros Hmd.

  (* D. eliminating addneq: no neq's are added. *)
  hexploit call_addneq_preserves_invariant_sem.
  - apply Hcall1. - apply Hcall2. - apply Hinv.
  instantiate (1:=(collect_global_ids (get_products_from_module m2))).
  instantiate (1:=(collect_global_ids (get_products_from_module m1))).
  clear Hinv; intros Hinv.

  (* D. filter / stale *)
  hexploit call_hfilter_preserves_invariant_sem.
  - apply Hcall1. - apply Hcall2.
  - instantiate (1:=pmem1). instantiate (1:=mem1').
    instantiate (1:=cfg1). instantiate (1:=m1).
    destruct ocmd1 as [cmd1|]; [|done]; destruct cmd1; try done; simpl in *.
    move Hpop1 at bottom.
    remember (pop_one_X cc1 n1) as pop1; destruct pop1; [|done].
    unfold pop_one_X in Heqpop1.
    destruct (noop_idx_zero_exists n1); [by rewrite <-Hpop1 in Heqpop1|].
    destruct cc1; [done|].
    inv Heqpop1; inv H0.
    destruct value0; try done.
  - instantiate (1:=pmem2). instantiate (1:=mem2').
    instantiate (1:=cfg2). instantiate (1:=m2).
    destruct ocmd2 as [cmd2|]; [|done]; destruct cmd2; try done; simpl in *.
    move Hpop2 at bottom.
    remember (pop_one_X cc2 n2) as pop2; destruct pop2; [|done].
    unfold pop_one_X in Heqpop2.
    destruct (noop_idx_zero_exists n2); [by rewrite <-Hpop2 in Heqpop2|].
    destruct cc2; [done|].
    inv Heqpop2; inv H0.
    destruct value0; try done.
  - apply Heqsu1. - apply Heqsu2. - apply Hvmem. - auto. - auto.
  - reflexivity. - reflexivity.
  - apply Hinv.
  clear Hinv; intros Hinv.

  (* E. eliminating addcmd: call_insn's are not added. *)
  hexploit call_addcmd_preserves_invariant_sem.
  - apply Hcall1. - apply Hcall2. - apply Hinv.
  clear Hinv; intros Hinv.

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
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
