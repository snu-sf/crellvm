Require Import vgtac.

Require Import vellvm.
Require Import program_sim.

Require Import syntax_ext.
Require Import validator_aux.
Require Import validator.
Require Import validator_props.
Require Import logical_step.
Require Import state_props.
Require Import hints.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import syntax_ext.
Require Import basic_const_inject.

Require Import hint_sem_props_resolve_defs.

Require Import lopsem.
Require Import behavior.
Require Import lbehavior.
Require Import simulation_local.
Require Import simulation_global.

Require Import paco.
Require Import Classical_Prop.

Import Opsem.

Section SimulationRefinement.
  Variable
    (m1 m2:module)
    (cfg1 cfg2:OpsemAux.Config)
    (Hmatch: matched_module_cfg m1 m2 cfg1 cfg2)
    (Hcfg1: OpsemPP.wf_Config cfg1)
    (Hcfg2: OpsemPP.wf_Config cfg2)
    (fn_al1 fn_al2:AssocList fdef_noop_t)
    (fh_al:hints.products_hint_t)
    (gmax:Z).

  Variable
    (Hgna1: globals_no_alias (Globals cfg1))
    (Hgna2: globals_no_alias (Globals cfg2))
    (Htd: CurTargetData cfg1 = CurTargetData cfg2).

  Variable
    (Hvalid_products1_1:
     forall id fd1 (Hfdef1: ret fd1 = lookupFdefViaIDFromProducts (CurProducts cfg1) id),
     exists fd2,
     ret fd2 = lookupFdefViaIDFromProducts (CurProducts cfg2) id)
    (Hvalid_products1_2:
     forall id fd2 (Hfdef2: ret fd2 = lookupFdefViaIDFromProducts (CurProducts cfg2) id),
     exists fd1,
     ret fd1 = lookupFdefViaIDFromProducts (CurProducts cfg1) id)
    (Hvalid_products2:
     forall id,
       lookupFdecViaIDFromProducts (CurProducts cfg1) id =
       lookupFdecViaIDFromProducts (CurProducts cfg2) id)
    (simulation__callExternalOrIntrinsics :
      forall
        alpha gmax
        TD id typ typargs deckind
        gl1 mem1 gvs1
        gl2 mem2 gvs2
        (Hgl: globals_equivalent alpha gmax gl1 gl2)
        (Hwf: genericvalues_inject.wf_sb_mi gmax alpha mem1 mem2)
        (Hgvs: genericvalues_inject.gv_list_inject alpha gvs1 gvs2)
        oresult1 tr mem1' (H1: ret (oresult1, tr, mem1') = callExternalOrIntrinsics TD gl1 mem1 id typ typargs deckind gvs1),
        exists oresult2, exists mem2',
          ret (oresult2, tr, mem2') = callExternalOrIntrinsics TD gl2 mem2 id typ typargs deckind gvs2 /\
          (forall result1 (Hresult1: ret result1 = oresult1),
            exists result2,
              ret result2 = oresult2 /\
              genericvalues_inject.gv_inject alpha result1 result2))
    (callExternalOrIntrinsics_mem_nextblock :
      forall td gl mem fid rt la dck gvs oresult tr mem'
        (H: callExternalOrIntrinsics td gl mem fid rt la dck gvs = ret (oresult, tr, mem')),
        Mem.nextblock mem <= Mem.nextblock mem').

  Variable (Hvalid: valid_products m1 m2 (CurProducts cfg1) (CurProducts cfg2) fn_al1 fn_al2 fh_al).

  Lemma lstuck_state_lsop_star cfg pnoops lst1 lst2 tr
    (Hstuck: lstuck_state cfg pnoops lst1)
    (Hsteps: lsop_star cfg pnoops lst1 lst2 tr) :
    lst1 = lst2 /\ tr = E0.
  Proof.
    inv Hsteps; [done|].
    unfold lstuck_state in Hstuck. contradict Hstuck.
    eexists. eexists. eauto.
  Qed.

  Lemma hint_sem_global_done_1
    alpha li1 li2 lst1 lst2
    (Hsim: hint_sem_global m1 m2 cfg1 cfg2 fn_al1 fn_al2 fh_al gmax alpha li1 li2 lst1.(state).(ECS) lst1.(state).(Mem) lst1.(ns) lst2.(state).(ECS) lst2.(state).(Mem) lst2.(ns))
    (Hstuck2: lstuck_state cfg2 fn_al2 lst2)
    (Hfinal2: s_isFinialState cfg2 lst2.(state) <> None) :
    lstuck_state cfg1 fn_al1 lst1 /\ s_isFinialState cfg1 lst1.(state) <> None.
  Proof.
    destruct lst1 as [[ecs1 mem1] ns1], lst2 as [[ecs2 mem2] ns2].
    destruct ecs2 as [|ec2 ecs2]; [done|]. destruct ec2. simpl in *.
    destruct CurCmds0; [|done]. destruct Terminator0; try done.
    - destruct ecs2; [|done].
      remember (getOperandValue (CurTargetData cfg2) value5 Locals0 (Globals cfg2)) as v2. destruct v2 as [v2|]; [|done].
      inv Hsim. inv Hec2. inv Hcons.
      remember (noop_idx_zero_exists n2) as h2. destruct h2.
      + exfalso. apply Hstuck2.
        exploit stuttering_lsInsn';
          [|by intros [? [Hstep ?]]; eexists; eexists; apply Hstep].
        intro. inv FH; simpl in *; inv H.
        by erewrite stutter_num_noop_idx_zero_exists' in *; eauto.
      + exploit Hvalid_term;
          [by eapply valid_products_valid_fdef'; eauto|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac]; eauto.
        * unfold pop_one_X. by rewrite <- Heqh2.
        intros [Hcmds1 [Himpl Hterm]].
        unfold pop_one_X in Hcmds1.
        remember (noop_idx_zero_exists n1) as h1. destruct h1; [done|]. destruct cmds1; [|done].
        destruct term1; inv Hterm. destruct_and.
        split.
        * intros [lst1' [tr1 Hstep1]].
          exploit no_stuttering_lsInsn; eauto.
          eapply no_stuttering_cons; simpl; eauto.
          by apply noop_idx_zero_exists_stutter_num'.
          intro Hstep. simpl in Hstep. inv Hstep.
        * eapply hint_sem_props_implies.invariant_implies_preserves_hint_sem_fdef in Hinsn; eauto.
          inv Hinsn. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
          exploit eq_check_value_prop_1; eauto.
          by inv Hvmem.
          by rewrite <- getOperandValue_equals_getOperandValueExt_new; eauto.
          simpl. intros [v1 [Hv1 Hinj]].
          rewrite <- getOperandValue_equals_getOperandValueExt_new in Hv1. by rewrite Hv1.
    - destruct ecs2; [|done].
      inv Hsim. inv Hec2. inv Hcons.
      remember (noop_idx_zero_exists n2) as h2. destruct h2.
      + exfalso. apply Hstuck2.
        exploit stuttering_lsInsn';
          [|by intros [? [Hstep ?]]; eexists; eexists; apply Hstep].
        intro. inv FH; simpl in *; inv H.
        by erewrite stutter_num_noop_idx_zero_exists' in *; eauto.
      + exploit Hvalid_term;
          [by eapply valid_products_valid_fdef'; eauto|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac]; eauto.
        * unfold pop_one_X. by rewrite <- Heqh2.
        intros [Hcmds1 [Himpl Hterm]].
        unfold pop_one_X in Hcmds1.
        remember (noop_idx_zero_exists n1) as h1. destruct h1; [done|]. destruct cmds1; [|done].
        destruct term1; inv Hterm. destruct_and.
        split.
        * intros [lst1' [tr1 Hstep1]].
          exploit no_stuttering_lsInsn; eauto.
          eapply no_stuttering_cons; simpl; eauto.
          by apply noop_idx_zero_exists_stutter_num'.
          intro Hstep. simpl in Hstep. inv Hstep.
        * done.
  Qed.

  Lemma hint_sem_global_done_2
    alpha li1 li2 lst1 lst2
    (Hsim: hint_sem_global m1 m2 cfg1 cfg2 fn_al1 fn_al2 fh_al gmax alpha li1 li2 lst1.(state).(ECS) lst1.(state).(Mem) lst1.(ns) lst2.(state).(ECS) lst2.(state).(Mem) lst2.(ns))
    (Hstuck1: lstuck_state cfg1 fn_al1 lst1)
    (Hfinal1: s_isFinialState cfg1 lst1.(state) <> None) :
    lstuck_state cfg2 fn_al2 lst2 /\ s_isFinialState cfg2 lst2.(state) <> None.
  Proof.
    destruct lst1 as [[ecs1 mem1] ns1], lst2 as [[ecs2 mem2] ns2].
    destruct ecs1 as [|ec1 ecs1]; [done|]. destruct ec1. simpl in *.
    destruct CurCmds0; [|done]. destruct Terminator0; try done.
    - destruct ecs1; [|done].
      remember (getOperandValue (CurTargetData cfg1) value5 Locals0
              (Globals cfg1)) as v1. destruct v1 as [v1|]; [|done].
      inv Hsim. inv Hec1. inv Hcons.
      remember (noop_idx_zero_exists n1) as h1. destruct h1.
      + exfalso. apply Hstuck1.
        exploit stuttering_lsInsn';
          [|by intros [? [Hstep ?]]; eexists; eexists; apply Hstep].
        intro. inv FH; simpl in *; inv H.
        by erewrite stutter_num_noop_idx_zero_exists' in *; eauto.
      + exploit Hvalid_term_2;
          [by eapply valid_products_valid_fdef'; eauto|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac]; eauto.
        * unfold pop_one_X. by rewrite <- Heqh1.
        intros [Hcmds1 [Himpl Hterm]].
        unfold pop_one_X in Hcmds1.
        remember (noop_idx_zero_exists n2) as h2. destruct h2; [done|]. destruct cmds2; [|done].
        destruct term2; inv Hterm. destruct_and.
        split.
        * intros [lst2' [tr2 Hstep2]].
          exploit no_stuttering_lsInsn; eauto.
          eapply no_stuttering_cons; simpl; eauto.
          by apply noop_idx_zero_exists_stutter_num'.
          intro Hstep. simpl in Hstep. inv Hstep.
        * eapply hint_sem_props_implies.invariant_implies_preserves_hint_sem_fdef in Hinsn; eauto.
          inv Hinsn. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
          exploit eq_check_value_prop_2; eauto.
          by inv Hvmem.
          by rewrite <- getOperandValue_equals_getOperandValueExt_new; eauto.
          simpl. intros [v2 [Hv2 Hinj]].
          rewrite <- getOperandValue_equals_getOperandValueExt_new in Hv2. by rewrite Hv2.
    - destruct ecs1; [|done].
      inv Hsim. inv Hec1. inv Hcons.
      remember (noop_idx_zero_exists n1) as h1. destruct h1.
      + exfalso. apply Hstuck1.
        exploit stuttering_lsInsn';
          [|by intros [? [Hstep ?]]; eexists; eexists; apply Hstep].
        intro. inv FH; simpl in *; inv H.
        by erewrite stutter_num_noop_idx_zero_exists' in *; eauto.
      + exploit Hvalid_term_2;
          [by eapply valid_products_valid_fdef'; eauto|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac]; eauto.
        * unfold pop_one_X. by rewrite <- Heqh1.
        intros [Hcmds1 [Himpl Hterm]].
        unfold pop_one_X in Hcmds1.
        remember (noop_idx_zero_exists n2) as h2. destruct h2; [done|]. destruct cmds2; [|done].
        destruct term2; inv Hterm. destruct_and.
        split.
        * intros [lst1' [tr1 Hstep1]].
          exploit no_stuttering_lsInsn; eauto.
          eapply no_stuttering_cons; simpl; eauto.
          by apply noop_idx_zero_exists_stutter_num'.
          intro Hstep. simpl in Hstep. inv Hstep.
        * eapply hint_sem_props_implies.invariant_implies_preserves_hint_sem_fdef in Hinsn; eauto.
  Qed.

  Lemma destruct_State (st: @State DGVs) :
    st = mkState (ECS st) (Mem st).
  Proof. by destruct st. Qed.

  Lemma hint_sem_global_lsInsn
    alpha li1 li2 lst1 lst2 lst2' tr
    (Hsim: hint_sem_global m1 m2 cfg1 cfg2 fn_al1 fn_al2 fh_al gmax alpha li1 li2 lst1.(state).(ECS) lst1.(state).(Mem) lst1.(ns) lst2.(state).(ECS) lst2.(state).(Mem) lst2.(ns))
    (Hinsn: lsInsn cfg2 fn_al2 lst2 lst2' tr) :
    (lstuck_state cfg1 fn_al1 lst1 /\ s_isFinialState cfg1 lst1.(state) = None) \/
    (exists lst1', lsInsn cfg1 fn_al1 lst1 lst1' tr /\
     exists alpha', exists li1', exists li2', hint_sem_global m1 m2 cfg1 cfg2 fn_al1 fn_al2 fh_al gmax alpha' li1' li2' lst1'.(state).(ECS) lst1'.(state).(Mem) lst1'.(ns) lst2'.(state).(ECS) lst2'.(state).(Mem) lst2'.(ns)).
  Proof.
    destruct (classic (exists mst1, exists mtr1, lsInsn cfg1 fn_al1 lst1 mst1 mtr1)).
    + right.
      destruct H as [mst1 [mtr1 Hinsn1]].
      inv Hinsn1. inv Hinsn.
      exploit global_hint_sem_F_step_hint_sem; eauto.
      - instantiate (4 := Mem (state mst1)).
        instantiate (4 := ECS (state mst1)).
        repeat rewrite <- destruct_State.
        eauto.
      intros [li1' [pi1 [li2' [pi2 [? [? HF]]]]]]. subst.
      exploit HF.
      - instantiate (4 := Mem (state lst2')).
        instantiate (4 := ECS (state lst2')).
        repeat rewrite <- destruct_State.
        by eauto.
      intros [alpha' [li1'' [li2'' [ecs1' [mem1' [ns1' [na1' [Hstep1' [Hincr' X]]]]]]]]].
      rewrite <- destruct_State in Hstep1'.
      exploit logical_semantic_step_lsInsn; [by apply Hstep1'|].
      intros [Hmatch' Hstep].
      eexists. split; [by apply Hstep|].
      eexists. eexists. eexists. simpl. eauto.
    + remember (s_isFinialState cfg1 lst1.(state)) as retval1. destruct retval1 as [retval1|].
      * exploit hint_sem_global_done_2; eauto. by rewrite <- Heqretval1.
        intros [Hstuck2 Hfinal2].
        exfalso. apply Hstuck2. eexists. eexists. eauto.
      * by left.
  Qed.

  Require Import Equality.

  Lemma hint_sem_global_lsop_star
    alpha li1 li2 lst1 lst2 lst2'
    (Hsim: hint_sem_global m1 m2 cfg1 cfg2 fn_al1 fn_al2 fh_al gmax alpha li1 li2 lst1.(state).(ECS) lst1.(state).(Mem) lst1.(ns) lst2.(state).(ECS) lst2.(state).(Mem) lst2.(ns))
    (Hlsop_star: lsop_star cfg2 fn_al2 lst2 lst2' E0) :
    (exists lst1', lsop_star cfg1 fn_al1 lst1 lst1' E0 /\ lstuck_state cfg1 fn_al1 lst1' /\ s_isFinialState cfg1 lst1'.(state) = None) \/
    (exists lst1', lsop_star cfg1 fn_al1 lst1 lst1' E0 /\
     exists alpha', exists li1', exists li2', hint_sem_global m1 m2 cfg1 cfg2 fn_al1 fn_al2 fh_al gmax alpha' li1' li2' lst1'.(state).(ECS) lst1'.(state).(Mem) lst1'.(ns) lst2'.(state).(ECS) lst2'.(state).(Mem) lst2'.(ns)).
  Proof.
    generalize dependent Hsim.
    generalize dependent lst1.
    generalize dependent li2.
    generalize dependent li1.
    generalize dependent alpha.
    dependent induction Hlsop_star; intros alpha li1 li2 lst_src Hsim.
    - right. exists lst_src. split; [by econs|].
      eexists. eexists. eexists. eauto.
    - exploit E0_app_inv; eauto. intros [? ?]. subst.
      exploit hint_sem_global_lsInsn; eauto. intros [Hobs|[lst1' [Hlst1' [alpha' [li1' [li2' Hsim']]]]]].
      + left. destruct Hobs as [Hstuck1 Hfinal1].
        eexists. splits; [|by eauto|by eauto].
        rewrite <- E0_right. econs; eauto.
      + exploit IHHlsop_star; eauto. intros [Hobs|[lst1'' [Hlst1'' [alpha'' [li1'' [li2'' Hsim'']]]]]].
        * left. destruct Hobs as [lst1'' [Hlst1'' [Hstuck1 Hfinal1]]].
          eexists. splits; [|by eauto|by eauto].
          rewrite <- E0_right. econs; eauto.
        * right. eexists. split; [by rewrite <- E0_left; eapply lsop_star_cons; eauto|].
          eexists. eexists. eexists. eauto.
  Qed.

  Lemma hint_sem_global_refinement
    alpha li1 li2 lst1 lst2
    (Hsim: hint_sem_global m1 m2 cfg1 cfg2 fn_al1 fn_al2 fh_al gmax alpha li1 li2 lst1.(state).(ECS) lst1.(state).(Mem) lst1.(ns) lst2.(state).(ECS) lst2.(state).(Mem) lst2.(ns))
    obs (Hbev2: lbehave cfg2 fn_al2 lst2 obs) :
    lbehave cfg1 fn_al1 lst1 obs.
  Proof.
    generalize dependent obs.
    generalize dependent li2.
    generalize dependent li1.
    generalize dependent alpha.
    generalize dependent lst2.
    generalize dependent lst1.
    pcofix CIH. intros lst1 lst2 alpha li1 li2 Hsim obs Hbev2.
    punfold Hbev2. inv Hbev2.
    exploit hint_sem_global_lsop_star; eauto. intros [Hobs|[lst1' [Hlst1' [alpha' [li1' [li2' Hsim']]]]]].
    - destruct Hobs as [lst1' [Hlst1' [Hstuck1 Hfinal1]]].
      pfold. econs; eauto.
    inv MAT.
    + pfold. econs; [|by eauto].
      assert (lstuck_state cfg1 fn_al1 lst1').
      * intros [lst1'' [tr1 Hstep1]]. apply STUCK.
        inv Hstep1.
        exploit global_hint_sem_F_progress_hint_sem; eauto.
          instantiate (4 := Mem (state (lst1''))).
          instantiate (4 := ECS (state (lst1''))).
          repeat rewrite <- destruct_State.
          by eauto.
        rewrite <- destruct_State.
        intros [ecs2' [mem2' [ns2' [na2' [tr2 Hstep2]]]]].
        exploit logical_semantic_step_lsInsn; eauto.
        intros [Hmatch2' X]. eexists. eexists. eauto.
      eapply lbeh_err; eauto.
      remember (s_isFinialState cfg1 (state lst1')) as f1. destruct f1 as [f1|]; [|done].
      exploit hint_sem_global_done_2; eauto.
      * by rewrite <- Heqf1.
      * intros [_ ?]. by rewrite NFINAL in H0.
    + exploit hint_sem_global_done_1; eauto. intros [Hstuck1 Hfinal1].
      pfold. econs; [|by eauto].
      eapply lbeh_done; eauto.
    + pclearbot. pfold. econs; [|by eauto].
      exploit hint_sem_global_lsInsn; eauto. intros [Hobs|[lst1'' [Hlst1'' [alpha'' [li1'' [li2'' Hsim'']]]]]].
      * destruct Hobs as [Hstuck1 Hfinal1].
        eapply lbeh_err; eauto.
      * eapply lbeh_inftau; eauto.
    + pclearbot. pfold. econs; [|by eauto].
      exploit hint_sem_global_lsInsn; eauto. intros [Hobs|[lst1'' [Hlst1'' [alpha'' [li1'' [li2'' Hsim'']]]]]].
      * destruct Hobs as [Hstuck1 Hfinal1].
        eapply lbeh_err; eauto.
      * eapply lbeh_evt; eauto.
  Qed.
End SimulationRefinement.

Section Refinement.
  Variable
    (m1 m2:module) (Hm1: wf_system [m1]) (Hm2: wf_system [m2])
    (fn_al1 fn_al2:AssocList fdef_noop_t)
    (fh_al:hints.products_hint_t).

  Variable (Hvalid: valid_module m1 m2 fn_al1 fn_al2 fh_al).

  Lemma monad_prop {A} (a:monad A) :
    match a with | ret x => ret x | merror => merror end = a.
  Proof. by destruct a. Qed.

  Lemma lookupFdefViaIDFromSystem_getParentOfFdefFromSystem fd m fid
    (H: ret fd = lookupFdefViaIDFromSystem [m] fid) :
    getParentOfFdefFromSystem fd [m] = ret m.
  Proof.
    simpl. destruct (productInModuleB_dec (product_fdef fd) m); [done|].
    destruct m. simpl in *.
    rewrite monad_prop in H.
    symmetry in H. apply lookupFdefViaIDFromProducts_inv in H.
    by rewrite e in H.
  Qed.

  Lemma valid_products_valid_fdef_1'
    fid
    fdef2 (Hfdef2: ret fdef2 = lookupFdefViaIDFromProducts (get_products_from_module m2) fid) :
    exists fdef1, (ret fdef1 = lookupFdefViaIDFromProducts (get_products_from_module m1) fid) /\
      exists fh, (ret fh = lookupAL fdef_hint_t fh_al fid) /\
        valid_fdef m1 m2 fdef1 fdef2 (lookupALOpt one_noop_t fn_al1 fid)
        (lookupALOpt one_noop_t fn_al2 fid) fh.
  Proof.
    destruct m1, m2. simpl in *.
    apply andb_true_iff in Hvalid. destruct Hvalid as [Hln Hprd].
    apply andb_true_iff in Hln. destruct Hln as [Hlo Hnd].
    destruct (layouts_dec layouts5 layouts0); [subst|done].
    destruct (namedts_dec namedts5 namedts0); [subst|done].

    generalize dependent fid.
    generalize dependent Hprd.
    generalize dependent (module_intro layouts0 namedts0 products0).
    intros m2' _ _.
    generalize dependent (module_intro layouts0 namedts0 products5).
    intros m1' _ _.
    clear -products0 products5.
    generalize dependent m2'.
    generalize dependent m1'.
    generalize dependent products0.
    generalize dependent products5.
    induction products5; intros [|hd1 tl1] m1 m2 Hv fid H2; try by inv H2.
    - destruct a, hd1; simpl in *;
      repeat
        match goal with
          | [H: vgtac.is_true (false) |- _] =>
            inv H
          | [H: vgtac.is_true (_ && _) |- _] =>
            apply andb_true_iff in H
          | [H: (_ && _) = true |- _] =>
            apply andb_true_iff in H
          | [H: _ /\ _ |- _] =>
            destruct H
          | [H: proj_sumbool (id_dec ?a ?b) = true |- _] =>
            destruct (id_dec a b); [|done]
          | [H: my_gvar_dec.my_gvar_dec _ _ = true |- _] =>
            apply my_gvar_dec.my_gvar_dec_spec in H; subst
          | [fd: fdec |- _] => destruct fd
        end;
        (try by inv Hv);
        (try by eapply IHproducts5; eauto).
      rewrite e in *.
      destruct (getFdefID fdef0 == fid); [subst|].
      + eexists; split; [done|].
        remember (lookupAL fdef_hint_t fh_al (getFdefID fdef0)) as fh; destruct fh as [fh|]; [|done].
        exists fh; split; [done|].
        rewrite ? get_noop_by_fname_lookupALOpt in H1.
        by inv H2.
      + by eapply IHproducts5; eauto.
  Qed.

  Lemma genGlobalAndInitMem_prop lo nd prd1' prd1 prd2' prd2 gl lc m pn1 pn2 ph
    (Hv: valid_products (module_intro lo nd prd1') (module_intro lo nd prd2') prd1 prd2 pn1 pn2 ph) :
    genGlobalAndInitMem (lo, nd) prd1 gl lc m = genGlobalAndInitMem (lo, nd) prd2 gl lc m.
  Proof.
    generalize dependent m.
    generalize dependent lc.
    generalize dependent gl.
    generalize dependent prd2.
    generalize dependent prd1.
    induction prd1; intros [|prd2 prds2] Hv gl lc m; try by inv Hv.
    - inv Hv. destruct a; try done. by destruct fdec5.
    - destruct a, prd2; inv Hv; try by destruct fdec5.
      + apply andb_true_iff in H0. destruct H0 as [H0 Hv].
        apply my_gvar_dec.my_gvar_dec_spec in H0. subst.
        destruct gvar0; simpl.
        * destruct (initGlobal (lo, nd) gl m id5 typ5 const5 align5); [|done].
          destruct p. by apply IHprd1.
        * destruct (getExternalGlobal m id5); [|done].
          by apply IHprd1.
      + destruct fdec5, fdec0.
        apply andb_true_iff in H0. destruct H0 as [H0 Hv].
        apply andb_true_iff in H0. destruct H0 as [H0 H1].
        destruct (fheader_dec fheader5 fheader0); [subst|done].
        destruct (deckind_dec deckind0 deckind5); [subst|done].
        destruct fheader0. simpl.
        destruct (initFunTable m id5); [|done].
        by apply IHprd1.
      + apply andb_true_iff in H0. destruct H0 as [H0 Hv].
        apply andb_true_iff in H0. destruct H0 as [H0 H1].
        destruct (id_dec (getFdefID fdef5) (getFdefID fdef0)); [subst|done].
        remember (lookupAL fdef_hint_t ph (getFdefID fdef5)) as fh. destruct fh as [fh|]; [|done].
        destruct fdef5, fdef0. simpl in *.
        apply andb_true_iff in H1. destruct H1 as [H1 Hb].
        apply andb_true_iff in H1. destruct H1 as [Hd Hinit].
        destruct (fheader_dec fheader5 fheader0); [subst|done].
        destruct fheader0. destruct (initFunTable m id5); [|done].
        by apply IHprd1.
  Qed.

  Hypothesis s_genInitState_prop_1 :
    forall m main args cfg ist
    (H: @s_genInitState DGVs [m] main args Mem.empty = ret (cfg, ist)),
    (forall (x : atom) (v : GenericValue), ret v = lookupAL GenericValue (Globals cfg) x -> not_undef v) /\
    globals_no_alias (Globals cfg) /\
    is_global_ids (collect_global_ids (get_products_from_module m)) (Globals cfg).

  Hypothesis s_genInitState_prop_2 :
    forall m main args cfg ist
    (H: @s_genInitState DGVs [m] main args Mem.empty = ret (cfg, ist)),
    readonly m cfg ist nil.

  Lemma ls_genInitState_prop_1 m fn_al main args cfg ist
    (H: ls_genInitState [m] fn_al main args Mem.empty = ret (cfg, ist)) :
    get_products_from_module m = CurProducts cfg.
  Proof.
    unfold ls_genInitState in H.
    remember (lookupFdefViaIDFromSystem [m] main) as f. destruct f; [|done].
    erewrite lookupFdefViaIDFromSystem_getParentOfFdefFromSystem in H; eauto.
    destruct m. simpl in *. unfold initTargetData in H.
    rewrite monad_prop in Heqf.
    destruct (genGlobalAndInitMem (layouts5, namedts5) products5 nil nil Mem.empty); [|done].
    destruct p. destruct p. destruct (getEntryBlock f); [|done]. destruct b. destruct s.
    destruct f. destruct fheader5. destruct (initLocals (layouts5, namedts5) args5 args); [|done].
    by inv H.
  Qed.

  Lemma ls_genInitState_prop_2 main args cfg2 ist2
    (H: ls_genInitState [m2] fn_al2 main args Mem.empty = ret (cfg2, ist2)) :
    exists cfg1, exists ist1,
    ls_genInitState [m1] fn_al1 main args Mem.empty = ret (cfg1, ist1) /\
    CurTargetData cfg1 = CurTargetData cfg2 /\
    Globals cfg1 = Globals cfg2 /\
    FunTable cfg1 = FunTable cfg2.
  Proof.
    exploit s_genInitState__opsem_wf; [apply Hm2|idtac|].
    - eapply ls_genInitState_s_genInitState; eauto.
    intros [Hcfg2 Hst2].

    unfold ls_genInitState in H.
    remember (lookupFdefViaIDFromSystem [m2] main) as f2. destruct f2; [|done].
    erewrite lookupFdefViaIDFromSystem_getParentOfFdefFromSystem in H; eauto.
    exploit valid_products_valid_fdef_1'; eauto.
    - destruct m2. simpl in *.
      rewrite monad_prop in Heqf2. eauto.
    intros [f1 [Hf1 [fh [Hfh Hv]]]].
    destruct m1, m2. simpl in *. unfold initTargetData in H.
    rewrite monad_prop in Heqf2.
    remember (genGlobalAndInitMem (layouts0, namedts0) products0 nil nil Mem.empty) as g2. destruct g2; [|done].
    destruct p. destruct p.
    remember (getEntryBlock f) as e2. destruct e2; [|done].
    destruct b. destruct s. destruct f. destruct fheader5.
    remember (initLocals (layouts0, namedts0) args5 args) as l2. destruct l2; [|done].
    inv H.

    simpl. unfold ls_genInitState.
    unfold lookupFdefViaIDFromSystem. unfold lookupFdefViaIDFromModules.
    unfold lookupFdefViaIDFromModule. rewrite <- Hf1.
    erewrite lookupFdefViaIDFromSystem_getParentOfFdefFromSystem; eauto;
    [|unfold lookupFdefViaIDFromSystem; unfold lookupFdefViaIDFromModules;
      unfold lookupFdefViaIDFromModule; rewrite monad_prop; eauto].
    apply andb_true_iff in Hvalid. destruct Hvalid as [Hln Hprd].
    apply andb_true_iff in Hln. destruct Hln as [Hlo Hnd].
    destruct (layouts_dec layouts5 layouts0); [subst|done].
    destruct (namedts_dec namedts5 namedts0); [subst|done].
    unfold initTargetData.
    erewrite genGlobalAndInitMem_prop; eauto. rewrite <- Heqg2.
    destruct f1. simpl in Hv.
    apply andb_true_iff in Hv. destruct Hv as [Hv Hb].
    apply andb_true_iff in Hv. destruct Hv as [Hh Hinit].
    destruct (fheader_dec fheader5 (fheader_intro fnattrs5 typ5 id5 args5 varg5)); [subst|done].
    destruct blocks5; [done|]. inv Heqe2.
    destruct blocks0; [done|].
    unfold valid_blocks in Hb. fold valid_blocks in Hb.
    apply andb_true_iff in Hb. destruct Hb as [Hb Hbs].
    destruct b. simpl in Hb.
    apply andb_true_iff in Hb. destruct Hb as [Hbid Hb].
    destruct (id_dec l1 l0); [subst|done].
    simpl. destruct s. rewrite <- Heql2.
    eexists. eexists. eauto.
  Qed.

  Lemma ls_genInitState_prop_3 main args cfg1 ist1 cfg2 ist2
    (Hl1: ls_genInitState [m1] fn_al1 main args Mem.empty = ret (cfg1, ist1))
    (Hl2: ls_genInitState [m2] fn_al2 main args Mem.empty = ret (cfg2, ist2)) :
    exists gmax, exists alpha,
      hint_sem_global m1 m2 cfg1 cfg2 fn_al1 fn_al2 fh_al
      gmax alpha [nil] [nil] (ECS (state ist1))
      (Mem (state ist1)) (ns ist1) (ECS (state ist2)) 
      (Mem (state ist2)) (ns ist2).
  Proof.
    exploit (s_genInitState_prop_1 m1). eapply ls_genInitState_s_genInitState; eauto. intros [Hg1 [Hg1' Hg1'']].
    exploit (s_genInitState_prop_1 m2). eapply ls_genInitState_s_genInitState; eauto. intros [Hg2 [Hg2' Hg2'']].
    exploit (s_genInitState_prop_2 m1). eapply ls_genInitState_s_genInitState; eauto. intros Hrd1.
    exploit (s_genInitState_prop_2 m2). eapply ls_genInitState_s_genInitState; eauto. intros Hrd2.
    exploit s_genInitState__opsem_wf; [apply Hm1|idtac|].
    - eapply ls_genInitState_s_genInitState; eauto.
    intros [Hcfg1 Hst1].
    exploit s_genInitState__opsem_wf; [apply Hm2|idtac|].
    - eapply ls_genInitState_s_genInitState; eauto.
    intros [Hcfg2 Hst2].

    unfold ls_genInitState in *.
    remember (lookupFdefViaIDFromSystem [m1] main) as f1. destruct f1 as [f1|]; [|done].
    remember (lookupFdefViaIDFromSystem [m2] main) as f2. destruct f2 as [f2|]; [|done].
    erewrite lookupFdefViaIDFromSystem_getParentOfFdefFromSystem in *; eauto.
    exploit valid_products_valid_fdef_1'; eauto.
    - destruct m2. simpl in *.
      rewrite monad_prop in Heqf2. eauto.
    intros [? [X [fh [Hfh Hv]]]].
    destruct m1, m2. simpl in *. rewrite monad_prop in Heqf1, Heqf2.
    rewrite <- Heqf1 in X. inv X.
    apply andb_true_iff in Hvalid. destruct Hvalid as [Hln Hprd].
    apply andb_true_iff in Hln. destruct Hln as [Hlo Hnd].
    destruct (layouts_dec layouts5 layouts0); [subst|done].
    destruct (namedts_dec namedts5 namedts0); [subst|done].
    unfold initTargetData in *. erewrite genGlobalAndInitMem_prop in Hl1; eauto.
    remember (genGlobalAndInitMem (layouts0, namedts0) products0 nil nil Mem.empty) as g.
 destruct g as [g|]; [|done].
    destruct g. destruct p.
    destruct f1, f2. simpl in Hv.
    apply andb_true_iff in Hv. destruct Hv as [Hv Hb].
    apply andb_true_iff in Hv. destruct Hv as [Hh Hinit].
    destruct (fheader_dec fheader5 fheader0); [subst|done].
    destruct blocks5, blocks0; try done. simpl in Hinit.
    destruct b. destruct s. simpl in *.
    destruct b0. destruct s. simpl in *.
    apply andb_true_iff in Hb. destruct Hb as [Hb Hbs].
    apply andb_true_iff in Hb. destruct Hb as [Hl Hh0].
    destruct (id_dec l0 l1); [subst|done].
    remember (lookupAL block_hint_t (block_hints fh) l1) as h0. destruct h0 as [h0|]; [|done].
    apply andb_true_iff in Hinit. destruct Hinit as [Hinit Hinit'].
    apply andb_true_iff in Hinit. destruct Hinit as [Hinit Hp2].
    apply andb_true_iff in Hinit. destruct Hinit as [_ Hp1].
    destruct phinodes5; [|done]. destruct phinodes0; [|done].
    destruct h0. destruct phi_hint as [|[]]; try done. destruct phi_hint; [|done]. simpl in *.
    apply andb_true_iff in Hh0. destruct Hh0 as [Hh01 Hh00].
    apply andb_true_iff in Hh01. destruct Hh01 as [Hh02 Hh01].
    apply andb_true_iff in Hh02. destruct Hh02 as [Hh03 Hh02].
    destruct cmds_hint as [|[]]; try done. destruct l0; [done|].
    apply andb_true_iff in Hh03. destruct Hh03 as [Hh04 Hh03].
    apply andb_true_iff in Hh04. destruct Hh04 as [Hh05 Hh04].
    destruct cmds_hint; [|done].
    destruct (l_dec a a0); [subst|done].
    destruct fheader0.
    remember (initLocals (layouts0, namedts0) args5 args) as lc0. destruct lc0 as [lc0|]; [|done].
    inv Hl1. inv Hl2. simpl.
    exploit lookupFdefViaIDFromProducts_ideq; eauto. simpl. intro. subst.
 
    exploit genGlobalAndInitMem__wf_globals_Mem; eauto.
    intros [Hwflc [[Hwfgl Hwfmem] [Hinj [Hwfm [Hft [Hlc _]]]]]].
    eexists. eexists. econs; eauto.
    - simpl. by destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l1 l1).
    - simpl. by destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l1 l1).
    - simpl. instantiate (1 := a0).
      by destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) a0 a0).
    - apply hint_lookup_nil.
    - exploit valid_phis_nil; eauto. intro Himpl.
      eapply hint_sem_props_implies.invariant_implies_preserves_hint_sem_fdef; eauto.
      eapply hint_sem_props_resolve.infrules_resolve_preserves_hint_sem_fdef; eauto.
      + by econs.
      + apply hint_sem_props_resolve.infrules_correct.
      econs; simpl; try by eauto.
      + exists nil. exists nil. split.
        * intros x _. unfold variable_equivalent.
          destruct x. destruct n; [done|]. simpl.
          remember (lookupAL GVs lc0 i2) as v. destruct v as [v|]; [|done].
          eapply Hlc; eauto.
        * move Hinit' at bottom.
          unfold valid_initial_phi_hint in Hinit'.
          apply andb_true_iff in Hinit'. destruct Hinit' as [Hinit' Hir].
          apply andb_true_iff in Hinit'. destruct Hinit' as [Hinit' Hil].
          apply andb_true_iff in Hinit'. destruct Hinit' as [Hel Her].
          apply andb_true_iff in Her. destruct Her as [Her Hrn].
          apply andb_true_iff in Her. destruct Her as [Hre Hrh].
          apply andb_true_iff in Hel. destruct Hel as [Hel Hln].
          apply andb_true_iff in Hel. destruct Hel as [Hle Hlh].
          repeat econs; repeat intro;
          (try by eauto);
          (try match goal with
                 | [H: EqHeapSetImpl.is_empty ?s = true,
                    H': vgtac.is_true (EqHeapSetImpl.mem ?x ?s) |- _] =>
                 apply EqHeapSetFacts.is_empty_iff in H; exploit H; eauto;
                   [apply EqHeapSetFacts.mem_iff; eauto|done]
                 | [H: NeqRegSetImpl.is_empty ?s = true,
                    H': vgtac.is_true (NeqRegSetImpl.mem ?x ?s) |- _] =>
                 apply NeqRegSetFacts.is_empty_iff in H; exploit H; eauto;
                   [apply NeqRegSetFacts.mem_iff; eauto|done]
                 | [H: IdExtSetImpl.is_empty ?s = true,
                    H': IdExtSetImpl.In ?x ?s |- _] =>
                 apply IdExtSetFacts.is_empty_iff in H; exploit H; by eauto
               end).
        Ltac t :=
          match goal with
            | [H: EqRegSetImpl.is_empty ?s = true,
              H': vgtac.is_true (EqRegSetImpl.mem ?x ?s) |- _] =>
            apply EqRegSetFacts.is_empty_iff in H; exploit H; eauto;
              [apply EqRegSetFacts.mem_iff; eauto|done]
          end.
        instantiate (1 := nil). t. t.
        instantiate (1 := nil). t. t.
      + by econs.
      + econs; eauto. apply Hwfgl.
      + econs; eauto; (try done); (try by intros ? X; inv X).
    - by econs.
  Qed.

  Theorem refinement main args obs
    (H: behave_prog m2 main args obs) :
    behave_prog m1 main args obs.
  Proof.
    eapply lbehave_prog_behave_prog. instantiate (1 := fn_al1).
    eapply behave_prog_lbehave_prog in H. instantiate (1 := fn_al2) in H.
    inv H. rename Hinit into Hinit2. rename cfg into cfg2. rename ist into ist2.
    exploit ls_genInitState_prop_2; eauto.
    intros [cfg1 [ist1 [Hinit1 [Htd [Hgl Hft]]]]].
    exploit ls_genInitState_prop_3; eauto.
    intros [gmax [alpha Hsem]].
    exploit s_genInitState__opsem_wf; [apply Hm1|idtac|].
    - eapply ls_genInitState_s_genInitState; eauto.
    intros [Hcfg1 Hst1].
    exploit s_genInitState__opsem_wf; [apply Hm2|idtac|].
    - eapply ls_genInitState_s_genInitState; eauto.
    intros [Hcfg2 Hst2].
    exploit (ls_genInitState_prop_1 m1); eauto. intro Hcfg1'.
    exploit (ls_genInitState_prop_1 m2); eauto. intro Hcfg2'.

    econs; eauto.
    exploit (s_genInitState_prop_1 m1). eapply ls_genInitState_s_genInitState; eauto. intros [Hg1 [Hg1' Hg1'']].
    exploit (s_genInitState_prop_1 m2). eapply ls_genInitState_s_genInitState; eauto. intros [Hg2 [Hg2' Hg2'']].
    (* exploit (ls_genInitState_prop_1 m1); eauto. intros [Hprd1 [Hg1 [Hg1' Hg1'']]]. *)
    (* exploit (ls_genInitState_prop_1 m2); eauto. intros [Hprd2 [Hg2 [Hg2' Hg2'']]]. *)
    destruct m1, m2. simpl in Hcfg1', Hcfg2'. subst. unfold valid_module in Hvalid.
    apply andb_true_iff in Hvalid. destruct Hvalid as [Hln Hprd].
    apply andb_true_iff in Hln. destruct Hln as [Hlo Hnd].
    destruct (layouts_dec layouts5 layouts0); [subst|done].
    destruct (namedts_dec namedts5 namedts0); [subst|done].
    eapply (hint_sem_global_refinement _ _ cfg1 cfg2); eauto.
    - econs; eauto.
    - intros. exploit valid_products_valid_fdef; eauto.
      intros [? [? _]]. eexists. eauto.
    - intros. exploit valid_products_valid_fdef_1; eauto.
      intros [? [? _]]. eexists. eauto.
    - intros. exploit valid_products_fdec; eauto.
  Qed.
End Refinement.

(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
