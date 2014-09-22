Require Import vgtac.
Require Import vellvm.

Require Import decs.
Require Import validator_aux.
Require Import validator_props.
Require Import set_facts2.
Require Import state_props.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import logical_step.
Require Import infrules.
Require Import basic_const_inject.

Require Import hint_sem_props_resolve_defs.

Import Opsem.
Import syntax_ext.
Import hints.

Lemma cond_replace_value_ext_prop x y v1 v2 olc lc cfg
  (Hxy: lookupALExt olc lc x = getOperandValueExt (CurTargetData cfg) y olc lc (Globals cfg))
  (Hreplace: cond_replace_value x y v1 v2) :
  getOperandValueExt (CurTargetData cfg) v1 olc lc (Globals cfg) =
  getOperandValueExt (CurTargetData cfg) v2 olc lc (Globals cfg).
Proof.
  destruct v1, v2; inv Hreplace.
  - apply orb_true_iff in H0; destruct H0.
  + apply andb_true_iff in H; destruct H.
    repeat ((try infrule_tac); subst).
    destruct y; [|inv H0].
    destruct (id_ext_dec x1 x0); [subst|inv H0].
    by rewrite Hxy.
  + destruct (id_ext_dec x0 x1); subst; [done|inv H].
  - apply orb_true_iff in H0; destruct H0; [|inv H].
    apply andb_true_iff in H; destruct H.
    repeat ((try infrule_tac); subst).
    destruct y; [inv H0|].
    destruct (const_dec c c0); [subst|inv H0].
    by rewrite Hxy.
  - by repeat ((try infrule_tac); subst).
Qed.

Lemma cond_replace_rhs_ext_prop x y v1 v2 olc lc cfg gvs
  (Hxy: lookupALExt olc lc x = getOperandValueExt (CurTargetData cfg) y olc lc (Globals cfg))
  (Hreplace: cond_replace x y v1 v2)
  (Hv1: rhs_ext_value_sem cfg olc lc v1 gvs) :
  rhs_ext_value_sem cfg olc lc v2 gvs.
Proof.
  destruct v1, v2; inv Hreplace;
    repeat
      ((try infrule_tac);
        try match goal with
              | [H: (cond_replace_value _ _ _ _) = true |- _] =>
                eapply cond_replace_value_ext_prop in H; eauto
            end;
        subst);
      try inv Hv1.
  - econstructor; eauto.
    unfold BOPEXT in H6.
    by rewrite H0, H1 in H6.
  - econstructor; eauto.
    unfold FBOPEXT in H6.
    by rewrite H0, H1 in H6.
  - econstructor; eauto.
    by rewrite <- H2.
  - econstructor; eauto.
    by rewrite <- H3.
    by rewrite <- H1.
  - econstructor; eauto.
    by rewrite <- H2.
    rewrite <- H9.
    generalize dependent H1.
    generalize dependent lsv0.
    clear H9.
    induction lsv.
    + by intros [|rsv_hd rsv_tl] Hrepl; inv Hrepl.
    + intros [|rsv_hd rsv_tl] Hrepl; inv Hrepl; [by destruct a|].
      destruct a, rsv_hd; repeat ((try infrule_tac); subst).
      eapply cond_replace_value_ext_prop in H0; eauto.
      eapply IHlsv in H1; eauto.
      unfold values2GVsExt.
      rewrite H0.
      destruct (getOperandValueExt (CurTargetData cfg) v2 olc lc (Globals cfg)); [|done].
      fold values2GVsExt.
      by rewrite H1.
  - econstructor; eauto.
    unfold TRUNCEXT in H6.
    by rewrite H1 in H6.
  - econstructor; eauto.
    unfold EXTEXT in H5.
    by rewrite H1 in H5.
  - econstructor; eauto.
    unfold CASTEXT in H5.
    by rewrite H1 in H5.
  - econstructor; eauto.
    unfold ICMPEXT in H6.
    by rewrite H0, H1 in H6.
  - econstructor; eauto.
    unfold FCMPEXT in H6.
    by rewrite H0, H1 in H6.
  - eapply rhs_ext_select_true_sem; eauto.
    by rewrite <- H.
    by rewrite <- H1.
  - eapply rhs_ext_select_false_sem; eauto.
    by rewrite <- H.
    by rewrite <- H0.
  - econstructor; eauto.
    by rewrite <- H0.
Qed.

Lemma cond_same_value_prop
  m v (Hcond: cond_same_value m v)
  m1 cfg1 olc1 lc1 gvs1
  m2 cfg2 olc2 lc2 gvs2
  (Hmatched: matched_module_cfg m1 m2 cfg1 cfg2)
  maxb alpha mem1 mem2
  (Hwf: genericvalues_inject.wf_sb_mi maxb alpha mem1 mem2)
  (Hgl1: genericvalues_inject.wf_globals maxb (Globals cfg1))
  (Hgl2: genericvalues_inject.wf_globals maxb (Globals cfg2))
  (Hmem: maydiff_sem lc1 lc2 alpha olc1 olc2 m)
  (H1: getOperandValueExt (CurTargetData cfg1) v olc1 lc1 (Globals cfg1) = ret gvs1)
  (H2: getOperandValueExt (CurTargetData cfg2) v olc2 lc2 (Globals cfg2) = ret gvs2) :
  genericvalues_inject.gv_inject alpha gvs1 gvs2.
Proof.
  destruct v; inv Hcond; simpl in H1, H2; infrule_tac.
  - generalize (Hmem _ H0); clear H0; intro H0.
    unfold variable_equivalent in H0.
    by rewrite H1, H2 in H0.
  - inv Hmatched.
    rewrite Htd in H1.
    rewrite Hgl in H1.
    rewrite H2 in H1; inv H1.
    by eapply LLVMtyping_rules.const2GV_refl; eauto.
Qed.

Lemma cond_same_lsv_prop
  m l (Hcond: cond_same_lsv m l)
  m1 cfg1 olc1 lc1
  m2 cfg2 olc2 lc2
  (Hmatched: matched_module_cfg m1 m2 cfg1 cfg2)
  maxb alpha mem1 mem2
  (Hwf: genericvalues_inject.wf_sb_mi maxb alpha mem1 mem2)
  (Hgl1: genericvalues_inject.wf_globals maxb (Globals cfg1))
  (Hgl2: genericvalues_inject.wf_globals maxb (Globals cfg2))
  (Hmem: maydiff_sem lc1 lc2 alpha olc1 olc2 m) :
  forall gvs1 gvs2
    (H1: values2GVsExt (CurTargetData cfg1) l olc1 lc1 (Globals cfg1) = ret gvs1)
    (H2: values2GVsExt (CurTargetData cfg2) l olc2 lc2 (Globals cfg2) = ret gvs2),
    genericvalues_inject.gvs_inject alpha gvs1 gvs2.
Proof.
  induction l; intros gvs1 gvs2 H1 H2; inv Hcond; inv H1; inv H2; [done|].
  destruct a; infrule_tac.
  exploit (cond_same_value_prop m v); eauto.
  exploit IHl; eauto.
  by inv H1; inv H3.
Qed.

Lemma cond_same_prop
  m e (Hcond: cond_same m e)
  m1 cfg1 olc1 lc1 gvs1
  m2 cfg2 olc2 lc2 gvs2
  (Hmatched: matched_module_cfg m1 m2 cfg1 cfg2)
  maxb alpha mem1 mem2
  (Hwf: genericvalues_inject.wf_sb_mi maxb alpha mem1 mem2)
  (Hgl1: genericvalues_inject.wf_globals maxb (Globals cfg1))
  (Hgl2: genericvalues_inject.wf_globals maxb (Globals cfg2))
  (Hmem: maydiff_sem lc1 lc2 alpha olc1 olc2 m)

  (H1: rhs_ext_value_sem cfg1 olc1 lc1 e gvs1)
  (H2: rhs_ext_value_sem cfg2 olc2 lc2 e gvs2) :
  genericvalues_inject.gv_inject alpha gvs1 gvs2.
Proof.
  Ltac cond_same_value_tac :=
    repeat
      match goal with
        | [H: cond_same_value ?m ?v = true |- _] =>
          exploit (cond_same_value_prop _ _ H); eauto; clear H; intro H
        | [H: cond_same_lsv ?m ?v = true |- _] =>
          exploit (cond_same_lsv_prop _ _ H); eauto; clear H; intro H
      end.

  destruct e; inv Hcond; infrule_tac; try inv H1; try inv H2.
  - unfold BOPEXT in H7, H8; infrule_tac; cond_same_value_tac.
    exploit (genericvalues_inject.simulation__mbop alpha (CurTargetData cfg1) b s g1 g g2 g0); eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    by rewrite H7 in Hx1; inv Hx1.
  - unfold FBOPEXT in H7, H8; infrule_tac; cond_same_value_tac.
    exploit (genericvalues_inject.simulation__mfbop alpha (CurTargetData cfg1) fb fp g1 g g2 g0); eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    by rewrite H7 in Hx1; inv Hx1.
  - cond_same_value_tac.
    exploit (genericvalues_inject.simulation__extractGenericValue alpha gvs gvs0 (CurTargetData cfg1) t); eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    generalize dependent Hx1.
    generalize dependent H9.
    unfold extractGenericValue, genericvalues.LLVMgv.extractGenericValue.
    destruct (intConsts2Nats (CurTargetData cfg2) lc); [|done].
    destruct (mgetoffset (CurTargetData cfg2) t l0); [|done].
    destruct p; infrule_tac.
    unfold mget'; intros H1 H2.
    by rewrite H2 in H1; inv H1.
  - cond_same_value_tac.
    exploit (genericvalues_inject.simulation__insertGenericValue alpha gvs gvs0 (CurTargetData cfg1) t lc gvs1 u gvs' gvs'0); eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    generalize dependent Hx1.
    generalize dependent H13.
    unfold insertGenericValue, genericvalues.LLVMgv.insertGenericValue.
    destruct (intConsts2Nats (CurTargetData cfg2) lc); [|done].
    destruct (mgetoffset (CurTargetData cfg2) t l0); [|done].
    destruct p; infrule_tac.
    unfold mset'; intros H1 H2.
    by rewrite H2 in H1; inv H1.
  - cond_same_value_tac.
    apply dos_in_list_gvs_inv in H11; subst.
    apply dos_in_list_gvs_inv in H14; subst.
    exploit (genericvalues_inject.simulation__GEP); eauto.
    intros [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    unfold GEP in H15; infrule_tac; unfold gep in H15.
    by rewrite H15 in Hx1; inv Hx1.
  - unfold TRUNCEXT in H6, H7; infrule_tac; cond_same_value_tac.
    exploit genericvalues_inject.simulation__mtrunc; eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    by rewrite H6 in Hx1; inv Hx1.
  - unfold EXTEXT in H6, H7; infrule_tac; cond_same_value_tac.
    exploit genericvalues_inject.simulation__mext; eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    by rewrite H6 in Hx1; inv Hx1.
  - unfold CASTEXT in H6, H7; infrule_tac; cond_same_value_tac.
    exploit genericvalues_inject.simulation__mcast; eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    by rewrite H6 in Hx1; inv Hx1.
  - unfold ICMPEXT in H7, H8; infrule_tac; cond_same_value_tac.
    exploit (genericvalues_inject.simulation__micmp alpha (CurTargetData cfg1) c t g1 g g2 g0); eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    by rewrite H7 in Hx1; inv Hx1.
  - unfold FCMPEXT in H7, H8; infrule_tac; cond_same_value_tac.
    exploit (genericvalues_inject.simulation__mfcmp alpha (CurTargetData cfg1) fc fp g1 g g2 g0); eauto.
    intro HH; destruct HH as [x [Hx1 Hx2]].
    inv Hmatched. rewrite Htd in Hx1.
    by rewrite H7 in Hx1; inv Hx1.
  - by cond_same_value_tac.
  - cond_same_value_tac.
    inv H11; inv H14.
    exploit (genericvalues_inject.simulation__isGVZero alpha c c0 (CurTargetData cfg1)); eauto.
    intro Hc.
    inv Hmatched.
    by rewrite H12, Htd, H15 in Hc.
  - cond_same_value_tac.
    inv H11; inv H14.
    exploit (genericvalues_inject.simulation__isGVZero alpha c c0 (CurTargetData cfg1)); eauto.
    intro Hc.
    inv Hmatched.
    by rewrite H12, Htd, H15 in Hc.
  - by cond_same_value_tac.
  - by cond_same_value_tac.
Qed.

Lemma rhs_ext_value_sem_proper
  cfg olc lc e g1 g2
  (H1: rhs_ext_value_sem cfg olc lc e g1)
  (H2: rhs_ext_value_sem cfg olc lc e g2) :
  g1 = g2.
Proof.
  destruct e; inv H1; inv H2;
    unfold BOPEXT, FBOPEXT, TRUNCEXT, EXTEXT, CASTEXT, ICMPEXT, FCMPEXT in *;
      repeat
        match goal with
          | [H: context[getOperandValueExt ?a ?b ?c ?d ?e] |- _] =>
            destruct (getOperandValueExt a b c d e); try done
          | [H: context[lift_op1 DGVs _ _ _] |- _] =>
            rewrite lift_op1_prop in H
          | [H: context[lift_op2 DGVs _ _ _ _] |- _] =>
            rewrite lift_op2_prop in H
        end.
  - by rewrite H5 in H6; inv H6.
  - by rewrite H5 in H6; inv H6.
  - inv H5; inv H6.
    by rewrite H7 in H8; inv H8.
  - inv H6; inv H7; inv H8; inv H10.
    by rewrite H9 in H11; inv H11.
  - inv H6; inv H7.
    rewrite H8 in H11; inv H11.
    apply dos_in_list_gvs_inv in H9; subst.
    apply dos_in_list_gvs_inv in H12; subst.
    by rewrite H10 in H13; inv H13.
  - by rewrite H5 in H6; inv H6.
  - by rewrite H5 in H6; inv H6.
  - by rewrite H5 in H6; inv H6.
  - by rewrite H5 in H6; inv H6.
  - by rewrite H5 in H6; inv H6.
  - by inv H4; inv H5; inv H7; inv H10.
  - inv H4; inv H5; inv H7; inv H10.
    inv H8; inv H11.
    by rewrite H9 in H12.
  - inv H4; inv H5; inv H7; inv H10.
    inv H8; inv H11.
    by rewrite H9 in H12.
  - inv H4; inv H5; inv H7; inv H10.
    inv H8; inv H11.
    by rewrite H9 in H12.
  - by inv H0; inv H1.
Qed.

Lemma id_ext_updateAddAL_prop
  olc lc g x y
  (Hfresh: cond_fresh_id_ext x y) :
  lookupALExt (updateAddAL GVs olc x g) lc y =
  lookupALExt olc lc y.
Proof.
  destruct y; infrule_tac.
  rewrite <- lookupAL_updateAddAL_neq; auto.
  unfold cond_fresh_id_ext, fst in Hfresh.
  by destruct (id_dec x i0); auto.
Qed.

Lemma value_ext_updateAddAL_prop
  cfg olc lc g x v
  (Hfresh: cond_fresh_value_ext x v) :
  getOperandValueExt (CurTargetData cfg) v (updateAddAL GVs olc x g) lc (Globals cfg) =
  getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg).
Proof.
  destruct v; [|done]; simpl.
  by rewrite id_ext_updateAddAL_prop.
Qed.

Lemma values_ext_updateAddAL_prop
  cfg olc lc g x idxs :
  forall (Hfresh: cond_fresh_lsv x idxs),
  values2GVsExt (CurTargetData cfg) idxs (updateAddAL GVs olc x g) lc (Globals cfg) =
  values2GVsExt (CurTargetData cfg) idxs olc lc (Globals cfg).
Proof.
  induction idxs; intro Hfresh; [done|].
  destruct a; inv Hfresh; infrule_tac.
  exploit value_ext_updateAddAL_prop; eauto.
  intro Hhd; rewrite Hhd.
  destruct (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg)); [|done].
  by rewrite IHidxs.
Qed.

Ltac updateAddAL_tac :=
  repeat
    (match goal with
       | [H: vgtac.is_true (cond_fresh_value_ext ?x ?v) |-
         context[rhs_ext_value_sem ?cfg (updateAddAL _ ?olc ?x ?g) ?lc _ _]] =>
       exploit (value_ext_updateAddAL_prop cfg olc lc g x v); eauto; clear H; intro H
       | [H: cond_fresh_value_ext ?x ?v = true |-
         context[rhs_ext_value_sem ?cfg (updateAddAL _ ?olc ?x ?g) ?lc _ _]] =>
       exploit (value_ext_updateAddAL_prop cfg olc lc g x v); eauto; clear H; intro H
     end).

Lemma rhs_ext_updateAddAL_prop
  cfg olc lc g x e gvs
  (Hfresh: cond_fresh_rhs_ext x e)
  (Hsem: rhs_ext_value_sem cfg olc lc e gvs) :
  rhs_ext_value_sem cfg (updateAddAL GVs olc x g) lc e gvs.
Proof.  
  inv Hsem; unfold cond_fresh_rhs_ext in Hfresh; infrule_tac; updateAddAL_tac.
  - econstructor; eauto.
    generalize dependent H; unfold BOPEXT.
    by rewrite H0, H1.
  - econstructor; eauto.
  generalize dependent H; unfold FBOPEXT.
    by rewrite H0, H1.
  - econstructor; eauto.
    by rewrite Hfresh.
  - econstructor; eauto.
    by rewrite H2.
    by rewrite H3.
  - econstructor; eauto.
    by rewrite H3.
    exploit (values_ext_updateAddAL_prop); eauto.
    by intro Hs; rewrite Hs.
  - econstructor; eauto.
    generalize dependent H; unfold TRUNCEXT.
    by rewrite Hfresh.
  - econstructor; eauto.
    generalize dependent H; unfold EXTEXT.
    by rewrite Hfresh.
  - constructor; eauto.
    generalize dependent H; unfold CASTEXT.
    by rewrite Hfresh.
  - econstructor; eauto.
    generalize dependent H; unfold ICMPEXT.
    by rewrite H0, H1.
  - econstructor; eauto.
    generalize dependent H; unfold FCMPEXT.
    by rewrite H0, H1.
  - eapply rhs_ext_select_true_sem; eauto.
    by rewrite <- H.
    by rewrite H5.
  - eapply rhs_ext_select_false_sem; eauto.
    by rewrite <- H.
    by rewrite H4.
  - econstructor; eauto.
    by rewrite Hfresh.
Qed.

Lemma eqs_sem_reg_updateAddAL_prop
  cfg olc lc mem gmax
  t g z eqs_reg
  (Hz: ret g = lookupALExt olc lc z)
  (Ht: cond_fresh_eq_reg t eqs_reg)
  (Hsem: eqs_eq_reg_sem cfg olc lc mem gmax eqs_reg) :
  eqs_eq_reg_sem cfg (updateAddAL GVs olc t g) lc mem gmax
  (EqRegSetImpl.add
    (vars_aux.add_otag t, rhs_ext_value (value_ext_id z))
    eqs_reg).
Proof.
  intros lhs rhs Heq; infrule_tac.
  destruct Heq; infrule_tac.
  - econstructor; eauto.
    + unfold lookupALExt, vars_aux.add_otag.
      by rewrite lookupAL_updateAddAL_eq.
    + econstructor; infrule_tac.
      destruct z; destruct n.
      * unfold lookupALExt.
        destruct (id_dec i0 t); [subst|].
        by rewrite lookupAL_updateAddAL_eq.
        by rewrite <- lookupAL_updateAddAL_neq.
      * done.
    + infrule_tac.
  - unfold cond_fresh_eq_reg in Ht.
    generalize (Hsem lhs rhs H); clear Hsem; intro Hsem.
    apply EqRegSetFacts.for_all_iff in Ht; [|by repeat intro; subst].
    apply EqRegSetFacts.mem_iff in H.
    generalize (Ht (lhs, rhs) H); clear Ht; intro Ht; infrule_tac.
    inv Hsem.
    + econstructor; eauto.
      * by rewrite id_ext_updateAddAL_prop; eauto.
      * by apply rhs_ext_updateAddAL_prop; eauto.
    + eapply eq_reg_sem_old_alloca; eauto.
      by rewrite id_ext_updateAddAL_prop; eauto.
Qed.

Lemma eqs_sem_heap_updateAddAL_prop
  cfg olc lc mem
  t g z eqs_heap
  (Hz: ret g = lookupALExt olc lc z)
  (Ht: cond_fresh_eq_heap t eqs_heap)
  (Hsem: eqs_eq_heap_sem cfg olc lc mem eqs_heap) :
  eqs_eq_heap_sem cfg (updateAddAL GVs olc t g) lc mem
  eqs_heap.
Proof.
  intros lhs tt aa rhs Heq; infrule_tac.
  unfold cond_fresh_eq_reg in Ht.
  generalize (Hsem lhs tt aa rhs Heq); clear Hsem; intro Hsem.
  apply EqHeapSetFacts.for_all_iff in Ht; [|by repeat intro; subst].
  apply EqHeapSetFacts.mem_iff in Heq.
  generalize (Ht (lhs, tt, aa, rhs) Heq); clear Ht; intro Ht; infrule_tac.
  generalize dependent Hsem.
  unfold fst in H; unfold snd in H0.
  unfold eq_heap_sem.
  by repeat rewrite value_ext_updateAddAL_prop; eauto.
Qed.

Lemma neqs_sem_reg_updateAddAL_prop
  cfg olc lc
  t g z eqs_reg
  (Hz: ret g = lookupALExt olc lc z)
  (Ht: cond_fresh_neq_reg t eqs_reg)
  (Hsem: eqs_neq_reg_sem cfg olc lc eqs_reg) :
  eqs_neq_reg_sem cfg (updateAddAL GVs olc t g) lc
  eqs_reg.
Proof.
  intros lhs rhs Heq; infrule_tac.
  unfold cond_fresh_eq_reg in Ht.
  generalize (Hsem lhs rhs Heq); clear Hsem; intro Hsem.
  apply NeqRegSetFacts.for_all_iff in Ht; [|by repeat intro; subst].
  apply NeqRegSetFacts.mem_iff in Heq.
  generalize (Ht (lhs, rhs) Heq); clear Ht; intro Ht; infrule_tac.
  generalize dependent Hsem.
  unfold fst in H; unfold snd in H0.
  unfold neq_reg_sem.
  rewrite id_ext_updateAddAL_prop; eauto.
  destruct (lookupALExt olc lc lhs); [|done].
  destruct rhs; [|done].
  by rewrite id_ext_updateAddAL_prop; eauto.
Qed.

Lemma cond_is_defined_prop
  cfg olc lc mem gmax eqs z
  (Hsem: eqs_eq_reg_sem cfg olc lc mem gmax eqs)
  (Heqs: cond_is_defined z eqs) :
  lookupALExt olc lc z <> merror.
Proof.
  apply EqRegSetFacts.exists_iff in Heqs; [|by repeat intro; subst].
  inv Heqs; infrule_tac.
  destruct x as [lhs rhs]; unfold fst.
  apply EqRegSetFacts.mem_iff in H.
  generalize (Hsem _ _ H); clear H; intro H.
  inv H; inv H1.
  by rewrite Hlookup.
Qed.

Lemma fresh_maydiff_updateAddAL_prop
  lc1 lc2 alpha olc1 olc2 md
  var g1 g2 (Hg: genericvalues_inject.gv_inject alpha g1 g2)
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hvar: IdExtSetImpl.For_all (fun x => cond_fresh_id_ext var x = true) md) :
  maydiff_sem lc1 lc2 alpha
  (updateAddAL GVs olc1 var g1)
  (updateAddAL GVs olc2 var g2)
  md.
Proof.
  intros (xid, xntag) Hx.
  generalize (Hmd (xid, xntag) Hx); clear Hmd.
  unfold variable_equivalent.
  destruct xntag; simpl; [|done].
  destruct (id_dec xid var); [subst|].
  - by repeat rewrite lookupAL_updateAddAL_eq.
  - by repeat rewrite <- lookupAL_updateAddAL_neq.
Qed.

Lemma fresh_maydiff_deleteAL_prop
  lc1 lc2 alpha olc1 olc2 md var
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hvar: IdExtSetImpl.For_all (fun x => cond_fresh_id_ext var x = true) md) :
  maydiff_sem lc1 lc2 alpha
  (deleteAL GVs olc1 var)
  (deleteAL GVs olc2 var)
  md.
Proof.
  intros (xid, xntag) Hx.
  generalize (Hmd (xid, xntag) Hx); clear Hmd.
  unfold variable_equivalent.
  destruct xntag; simpl; [|done].
  destruct (id_dec var xid); [subst|].
  - by repeat rewrite lookupAL_deleteAL_eq.
  - by repeat rewrite lookupAL_deleteAL_neq.
Qed.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
