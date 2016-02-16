Require Import sflib.

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

Require Import hint_sem_props_implies.
Require Import hint_sem_props_resolve_defs.
Require Import hint_sem_props_resolve.
Require Import hint_sem_props_proceed.
Require Import hint_sem_props_proceed_call.
Require Import hint_sem_props_proceed_call_void.
Require Import hint_sem_props_proceed_branch.

Require Import lopsem.
Require Import excall.

Import Opsem.

Ltac destruct_and :=
  repeat
    match goal with
      | [H: vgtac.is_true (_ && _) |- _] =>
        apply andb_true_iff in H; destruct H
      | [H: _ && _ = true |- _] =>
        apply andb_true_iff in H; destruct H
      | [H: _ /\ _ |- _] =>
        destruct H
    end.

Lemma lookupAL_cons A k v l x :
  lookupAL A ((k,v)::l) x =
  if id_dec x k
    then ret v
    else lookupAL A l x.
Proof.
  simpl.
  unfold eq_dec.
  unfold EqDec_atom.
  unfold EqDec_eq_of_EqDec.
  unfold id_dec.
  done.
Qed.

Section SameContext.
  Inductive same_context (ec1 ec2: Opsem.ExecutionContext) fid : Prop :=
  | same_context_intro :
    forall
      (Hfid1: fid = getFheaderID (fheaderOfFdef (Opsem.CurFunction ec1)))
      (Hfid2: fid = getFheaderID (fheaderOfFdef (Opsem.CurFunction ec2))),
      same_context ec1 ec2 fid.

  Inductive same_context_bid (ec1 ec2: Opsem.ExecutionContext) fid bid : Prop :=
  | same_context_bid_intro :
    forall
      (Hsc: same_context ec1 ec2 fid)
      (Hbid1: bid = fst (Opsem.CurBB ec1)) (Hbid2: bid = fst (Opsem.CurBB ec2)),
      same_context_bid ec1 ec2 fid bid.

  Lemma same_context_bid_unique:
    forall {ec1 ec2 fid bid1 bid2}
      (Hsb1: same_context_bid ec1 ec2 fid bid1)
      (Hsb2: same_context_bid ec1 ec2 fid bid2),
      bid1 = bid2.
  Proof.
    intros; inversion Hsb1; inversion Hsb2; subst; done.
  Qed.

  Lemma same_context_symmetric: 
    forall {ec1 ec2 fid} (Hsc : same_context ec1 ec2 fid),
      same_context ec2 ec1 fid.
  Proof. 
    intros. inversion Hsc. eapply same_context_intro; eauto. 
  Qed.

  Lemma same_context_bid_symmetric:
    forall {ec1 ec2 fid bid}
      (Hsb1: same_context_bid ec1 ec2 fid bid),
      same_context_bid ec2 ec1 fid bid.
  Proof.
    intros. inversion Hsb1.
    apply same_context_bid_intro with (ec1:=ec2) (ec2:=ec1); auto.
    apply same_context_symmetric; auto.
  Qed.

  Lemma same_context_transitive:
    forall {ec1 ec2 ec3 fid} (Hsc1: same_context ec1 ec2 fid) (Hsc2: same_context ec2 ec3 fid),
      same_context ec1 ec3 fid.
  Proof.
    intros; inversion Hsc1; inversion Hsc2; subst.
    eapply same_context_intro; eauto.
  Qed.

  Lemma same_context_bid_transitive:
    forall {ec1 ec2 ec3 bid1 bid2 fid}
      (Hscb1: same_context_bid ec1 ec2 fid bid1)
      (Hscb2: same_context_bid ec2 ec3 fid bid2),
      bid1 = bid2 /\ same_context_bid ec1 ec3 fid bid1.
  Proof.
    intros; inversion Hscb1; inversion Hscb2; subst; split; try done.
    inversion Hsc; inversion Hsc0.
    eapply same_context_bid_intro; eauto.
    eapply same_context_intro; eauto.
  Qed.
End SameContext.

Inductive hint_lookup (hint:insn_hint_t) (cur1 cur2:cmds) (n1 n2:noop_t) :
  forall (all1 all2:cmds)
    (an1 an2:noop_t)
    (hints:list insn_hint_t), Prop :=
| hint_lookup_nil :
  forall hints,
    hint_lookup hint cur1 cur2 n1 n2 cur1 cur2 n1 n2 (hint::hints)
| hint_lookup_cons :
  forall all1 all2 an1 an2 cmd_opt1 cmd_opt2 next1 next2 nn1 nn2 hint' hints
    (Hpop1: (ret_pop_cmd cmd_opt1 next1 nn1) = pop_one_X all1 an1)
    (Hpop2: (ret_pop_cmd cmd_opt2 next2 nn2) = pop_one_X all2 an2)
    (Hlookup: hint_lookup hint cur1 cur2 n1 n2 next1 next2 nn1 nn2 hints),
    hint_lookup hint cur1 cur2 n1 n2 all1 all2 an1 an2 (hint'::hints).

Ltac eq_check_value_tac :=
  repeat
    (match goal with
       | [H: _ \/ _ |- _] => destruct H; infrule_tac
       | [Hmd: maydiff_sem ?lc1 _ _ ?olc1 _ ?md,
         Hgv: lookupALExt ?olc1 ?lc1 ?x = ret ?gv,
         Hx: IdExtSetImpl.mem ?x ?md = false |- _] =>
         generalize (Hmd x Hx); clear Hx; intro Hx
       | [Hmd: maydiff_sem _ ?lc2 _ _ ?olc2 ?md,
         Hgv: lookupALExt ?olc2 ?lc2 ?x = ret ?gv,
         Hx: IdExtSetImpl.mem ?x ?md = false |- _] =>
         generalize (Hmd x Hx); clear Hx; intro Hx
       | [H1: eqs_eq_reg_sem _ _ _ _ _ ?eqs_reg,
         H2: EqRegSetImpl.mem (?lhs, ?rhs) ?eqs_reg = true |- _] =>
         generalize (H1 _ _ H2); clear H2; intro H2
       | [H: eq_reg_sem _ _ _ _ _ _ (rhs_ext_value _) |- _] =>
         inv H; infrule_tac; simpl in *
       | [H1: lookupALExt ?olc ?lc ?x = ret ?gv,
         H2: context[match lookupALExt ?olc ?lc ?x with | ret _ => _ | merror => _ end] |- _] =>
       rewrite H1 in H2
       | [H: context[match lookupALExt ?olc ?lc ?x with | ret _ => _ | merror => False end] |- _] =>
         let v := fresh "v" in
         remember (lookupALExt olc lc x) as v; destruct v; [|done]
     end;
    unfold variable_equivalent in *).

Lemma eq_check_params_prop
  cfg1 cfg2 lc1 lc2 olc1 olc2 mem1 mem2
  md inv alpha gmax li1 li2
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2 inv)
  (Htd: CurTargetData cfg1 = CurTargetData cfg2)
  (Hwfm: genericvalues_inject.wf_sb_mi gmax alpha mem1 mem2)
  (Hgl: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2)) :
  forall p1 p2
  (Heq: eq_check_params md (invariant_original inv) (invariant_optimized inv) (vars_aux.add_ntag_params p1) (vars_aux.add_ntag_params p2))
  args1 (Hargs1: ret args1 = params2GVs (CurTargetData cfg1) p1 lc1 (Globals cfg1))
  args2 (Hargs2: ret args2 = params2GVs (CurTargetData cfg2) p2 lc2 (Globals cfg2)),
  genericvalues_inject.gv_list_inject alpha args1 args2.
Proof.
  induction p1 as [|[[p1t p1a] p1v] p1tl]; intros [|[[p2t p2a] p2v] p2tl] Heq args1 Hargs1 args2 Hargs2; inv Heq;
    simpl in *.
  - inv Hargs1. inv Hargs2.
    by constructor.
  - remember (getOperandValue (CurTargetData cfg1) p1v lc1 (Globals cfg1)) as gv1; destruct gv1; [|done].
    remember (getOperandValue (CurTargetData cfg2) p2v lc2 (Globals cfg2)) as gv2; destruct gv2; [|done].
    remember (params2GVs (CurTargetData cfg1) p1tl lc1 (Globals cfg1)) as gvs1; destruct gvs1 as [gvs1|]; [|done].
    remember (params2GVs (CurTargetData cfg2) p2tl lc2 (Globals cfg2)) as gvs2; destruct gvs2 as [gvs2|]; [|done].
    inv Hargs1. inv Hargs2.
    destruct_and.
    exploit eq_check_value_prop; eauto.
    by rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new; eauto.
    by rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new; eauto.
    intro Hinj; constructor; auto.
    by eapply IHp1tl; eauto.
Qed.    

Lemma eq_check_value_prop_1
  cfg1 cfg2 lc1 lc2 olc1 olc2 mem1 mem2
  md inv alpha gmax li1 li2
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2 inv)
  v1 v2 gvs2
  (Heq: eq_check_value md (invariant_original inv) (invariant_optimized inv) v1 v2)
  (Htd: CurTargetData cfg1 = CurTargetData cfg2)
  (Hwfm: genericvalues_inject.wf_sb_mi gmax alpha mem1 mem2)
  (Hgl: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))
  (H2: getOperandValueExt (CurTargetData cfg2) v2 olc2 lc2 (Globals cfg2) = ret gvs2) :
  exists gvs1,
    getOperandValueExt (CurTargetData cfg1) v1 olc1 lc1 (Globals cfg1) = ret gvs1 /\
    genericvalues_inject.gv_inject alpha gvs1 gvs2.
Proof.
  inv Hinv. inv H; infrule_tac. inv H0; infrule_tac.
  destruct v1, v2; inv Heq; simpl in H2; infrule_tac; eq_check_value_tac.
  - remember (lookupALExt olc1 lc1 x0) as gv1; destruct gv1; [|done].
    by eexists; split.
  - rewrite H2 in H10. inv H10.
    remember (lookupALExt olc1 lc1 x) as gv1; destruct gv1; [|done].
    by eexists; split.
  - rewrite H2 in Hlookup. inv Hlookup.
    remember (lookupALExt olc1 lc1 x) as gv1; destruct gv1; [|done].
    by eexists; split.
  - by eexists; split; eauto.
  - by eexists; split; eauto.
  - inv Hgl.
    eexists; split; eauto.
    rewrite Htd, Hgl2 in H9. rewrite H9 in H2. inv H2.
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    by rewrite Hgl2; eauto.
  - rewrite H2 in Hlookup. inv Hlookup.
    inv Hgl.
    exists gvs'. rewrite Htd, Hgl2. split; [done|].
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    by rewrite Hgl2; eauto.
  - inv Hgl.
    exists gvs2. rewrite Htd, Hgl2. split; [done|].
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    by rewrite Hgl2; eauto.
Qed.    

Lemma eq_check_params_prop_1
  cfg1 cfg2 lc1 lc2 olc1 olc2 mem1 mem2
  md inv alpha gmax li1 li2
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2 inv)
  (Htd: CurTargetData cfg1 = CurTargetData cfg2)
  (Hwfm: genericvalues_inject.wf_sb_mi gmax alpha mem1 mem2)
  (Hgl: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2)) :
  forall p1 p2
  (Heq: eq_check_params md (invariant_original inv) (invariant_optimized inv) (vars_aux.add_ntag_params p1) (vars_aux.add_ntag_params p2))
  args2 (Hargs2: ret args2 = params2GVs (CurTargetData cfg2) p2 lc2 (Globals cfg2)),
  exists args1,
    ret args1 = params2GVs (CurTargetData cfg1) p1 lc1 (Globals cfg1) /\
    genericvalues_inject.gv_list_inject alpha args1 args2.
Proof.
  induction p1 as [|[[p1t p1a] p1v] p1tl]; intros [|[[p2t p2a] p2v] p2tl] Heq args2 Hargs2; inv Heq;
    simpl in *.
  - inv Hargs2.
    by eexists; split.
  - remember (getOperandValue (CurTargetData cfg2) p2v lc2 (Globals cfg2)) as gv2; destruct gv2; [|done].
    remember (params2GVs (CurTargetData cfg2) p2tl lc2 (Globals cfg2)) as gvs2; destruct gvs2 as [gvs2|]; [|done].
    inv Hargs2.
    destruct_and.
    exploit eq_check_value_prop_1; eauto.
    by rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new; eauto.
    intros [gv1 [Hgv1 Hinj]].
    rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new in *.
    rewrite Hgv1.
    exploit IHp1tl; eauto.
    intros [gvs1 [Hgvs1 Hinjs]].
    rewrite <- Hgvs1.
    eexists; split; eauto.
    by constructor.
Qed.    

Lemma eq_check_value_prop_2
  cfg1 cfg2 lc1 lc2 olc1 olc2 mem1 mem2
  md inv alpha gmax li1 li2
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2 inv)
  v1 v2 gvs1
  (Heq: eq_check_value md (invariant_original inv) (invariant_optimized inv) v1 v2)
  (Htd: CurTargetData cfg1 = CurTargetData cfg2)
  (Hwfm: genericvalues_inject.wf_sb_mi gmax alpha mem1 mem2)
  (Hgl: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))
  (H1: getOperandValueExt (CurTargetData cfg1) v1 olc1 lc1 (Globals cfg1) = ret gvs1) :
  exists gvs2,
    getOperandValueExt (CurTargetData cfg2) v2 olc2 lc2 (Globals cfg2) = ret gvs2 /\
    genericvalues_inject.gv_inject alpha gvs1 gvs2.
Proof.
  inv Hinv. inv H; infrule_tac. inv H0; infrule_tac.
  destruct v1, v2; inv Heq; simpl in H1; infrule_tac; eq_check_value_tac.
  - remember (lookupALExt olc2 lc2 x0) as gv2; destruct gv2; [|done].
    by eexists; split.
  - by eexists; split; eauto.
  - by eexists; split; eauto.
  - rewrite H1 in Hlookup. inv Hlookup.
    by eexists; split; eauto.
  - rewrite H1 in H10. inv H10.
    by eexists; split; eauto.
  - rewrite H1 in Hlookup. inv Hlookup.
    inv Hgl.
    rewrite Htd, Hgl2 in H9. rewrite H9.
    eexists; split; eauto.
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    by rewrite Hgl2; eauto.
  - inv Hgl.
    rewrite Htd, Hgl2 in H1. rewrite H1 in H9. inv H9.
    eexists; split; eauto.
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    by rewrite Hgl2; eauto.
  - inv Hgl.
    rewrite Htd, Hgl2 in H1. rewrite H1.
    eexists; split; eauto.
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    by rewrite Hgl2; eauto.
Qed.    

Lemma eq_check_params_prop_2
  cfg1 cfg2 lc1 lc2 olc1 olc2 mem1 mem2
  md inv alpha gmax li1 li2
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2 inv)
  (Htd: CurTargetData cfg1 = CurTargetData cfg2)
  (Hwfm: genericvalues_inject.wf_sb_mi gmax alpha mem1 mem2)
  (Hgl: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2)) :
  forall p1 p2
  (Heq: eq_check_params md (invariant_original inv) (invariant_optimized inv) (vars_aux.add_ntag_params p1) (vars_aux.add_ntag_params p2))
  args1 (Hargs1: ret args1 = params2GVs (CurTargetData cfg1) p1 lc1 (Globals cfg1)),
  exists args2,
    ret args2 = params2GVs (CurTargetData cfg2) p2 lc2 (Globals cfg2) /\
    genericvalues_inject.gv_list_inject alpha args1 args2.
Proof.
  induction p1 as [|[[p1t p1a] p1v] p1tl]; intros [|[[p2t p2a] p2v] p2tl] Heq args1 Hargs1; inv Heq;
    simpl in *.
  - inv Hargs1.
    by eexists; split.
  - remember (getOperandValue (CurTargetData cfg1) p1v lc1 (Globals cfg1)) as gv1; destruct gv1; [|done].
    remember (params2GVs (CurTargetData cfg1) p1tl lc1 (Globals cfg1)) as gvs1; destruct gvs1 as [gvs1|]; [|done].
    inv Hargs1.
    destruct_and.
    exploit eq_check_value_prop_2; eauto.
    by rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new; eauto.
    intros [gv2 [Hgv2 Hinj]].
    rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new in *.
    rewrite Hgv2.
    exploit IHp1tl; eauto.
    intros [gvs2 [Hgvs2 Hinjs]].
    rewrite <- Hgvs2.
    eexists; split; eauto.
    by constructor.
Qed.    

Lemma invariant_proceed_heap_eq_check
  m1 m2 hint' hint
  cmd_opt1 cmd_opt2
  (H: ret hint' = invariant_proceed m1 m2 hint cmd_opt1 cmd_opt2) :
  heap_eq_check
  (hint_maydiff hint)
  (invariant_original (hint_invariant hint))
  (invariant_optimized (hint_invariant hint))
  (iso_original (hint_invariant hint))
  (iso_optimized (hint_invariant hint))
  cmd_opt1 cmd_opt2.
Proof.
  unfold invariant_proceed in H.
  match goal with
    | [H: ret _ = if ?c then merror else ?e |- _] =>
      remember c as cond; destruct cond; [done|]
  end.
  clear -Heqcond.
  symmetry in Heqcond.
  by apply negb_false_iff in Heqcond.
Qed.

Lemma getOperandValue_compat: forall a b c d, genericvalues.LLVMgv.getOperandValue a b c d = @getOperandValue DGVs a b c d.
Proof.
  done.
Qed.

Section Relation.
  Variable
    (m1 m2:module)
    (cfg1 cfg2:OpsemAux.Config)
    (Hmatch: matched_module_cfg m1 m2 cfg1 cfg2)
    (Hcfg1: OpsemPP.wf_Config cfg1)
    (Hcfg2: OpsemPP.wf_Config cfg2)
    (fn_al1 fn_al2:AssocList fdef_noop_t)
    (gmax:Z) (pi1 pi2:list mblock).

  Inductive same_fid (fdef1 fdef2:fdef) (fid:id) : Prop :=
  | same_fid_intro :
    forall
      (Hfid1: fid = getFdefID fdef1)
      (Hfid2: fid = getFdefID fdef2),
      same_fid fdef1 fdef2 fid.

  Variable
    (fdef1 fdef2:fdef)
    (fid:id) (Hfid: same_fid fdef1 fdef2 fid)
    (fh: hints.fdef_hint_t).
  
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
       lookupFdecViaIDFromProducts (CurProducts cfg2) id).

  Definition is_excall cfg (st: Opsem.State) (fd:fdec) : Prop :=
    match st with
      | Opsem.mkState ec ecs _ =>
        match ec with
          | Opsem.mkEC _ _ (ccmd::ccmds) _ _ _ =>
            match ccmd with
              | insn_call _ _ _ _ _ fv _ =>
                exists fptrs, exists fptr,
                  Opsem.getOperandValue (CurTargetData cfg) fv (Opsem.Locals ec) (Globals cfg) =
                  Some fptrs /\
                  fptr @ fptrs /\
                  OpsemAux.lookupExFdecViaPtr (CurProducts cfg) (FunTable cfg) fptr = Some fd
              | _ => False
            end
          | _ => False
        end
    end.
  
  Inductive is_same_call (st1 st2:State) : Prop :=
  | is_same_call_call :
    forall fid
      (H1: is_call cfg1 st1 fid)
      (H2: is_call cfg2 st2 fid),
      is_same_call st1 st2
  | is_same_call_excall :
    forall
      fdec
      (H1: is_excall cfg1 st1 fdec)
      (H2: is_excall cfg2 st2 fdec),
      is_same_call st1 st2.

  Inductive is_call_readonly' m st : Prop :=
  | _is_call_readonly' : is_call_readonly m st -> is_call_readonly' m st.

  Definition is_call_readonly'' m (st: Opsem.State) : bool :=
    match st with
      | Opsem.mkState ec ecs _ =>
        match ec with
          | Opsem.mkEC _ _ (ccmd::ccmds) _ _ _ =>
            match ccmd with
              | insn_call _ _ _ _ _ fv _ =>
                match fv with
                  | value_id f
                  | value_const (const_gid _ f) =>
                    (match (lookupFdecViaIDFromModule m f) with
                       | Some (fdec_intro (fheader_intro
                         (fnattrs_intro _ _ _ _ a) _ _ _ _) _)
                       => (in_dec attribute_dec attribute_readnone a || in_dec attribute_dec attribute_readonly a)
                       | _ => false
                     end) ||
                    (match (lookupFdefViaIDFromModule m f) with
                       | Some (fdef_intro (fheader_intro
                         (fnattrs_intro _ _ _ _ a) _ _ _ _) _)
                       => (in_dec attribute_dec attribute_readnone a || in_dec attribute_dec attribute_readonly a)
                       | _ => false
                     end)
                  | _ => false
                end
              | _ => false
            end
          | _ => false
        end
    end.

  Definition is_call_readonly''' m st := is_call_readonly'' m st.
  Global Opaque is_call_readonly'''.

  Lemma is_call_readonly'''_prop m st :
    is_call_readonly''' m st = is_call_readonly'' m st.
  Proof.
    Local Transparent is_call_readonly'''.
    by unfold is_call_readonly'''.
    Global Opaque is_call_readonly'''.
  Qed.

  Lemma is_call_readonly_iff' m st :
    is_call_readonly m st <-> is_call_readonly''' m st.
  Proof.
    rewrite is_call_readonly'''_prop. admit. (*
    destruct st as [[|ec ecs] mem]; [done|].
    destruct ec. destruct CurCmds0 as [|c cmds]; [done|].
    destruct c; try done.
    destruct value0; (try done); simpl.
    - destruct (lookupFdecViaIDFromModule m id0) as [fdec|].
      + destruct fdec. destruct fheader5. destruct fnattrs5.
        destruct (in_dec attribute_dec attribute_readnone attributes2); simpl;
          [by econs; intros; auto|].
        destruct (in_dec attribute_dec attribute_readonly attributes2); simpl;
          [by econs; intros; auto|].
        destruct (lookupFdefViaIDFromModule m id0);
          [|by econs; intros; auto; by destruct H as [[]|]].
        destruct f. destruct fheader5. destruct fnattrs5.
        destruct (in_dec attribute_dec attribute_readnone attributes3); simpl;
          [by econs; intros; auto|].
        destruct (in_dec attribute_dec attribute_readonly attributes3); simpl;
          [by econs; intros; auto|].
        econs; intros; auto; by destruct H as [[]|[]].
      + destruct (lookupFdefViaIDFromModule m id0);
          [|by econs; intros; auto; by destruct H as [[]|]].
        destruct f. destruct fheader5. destruct fnattrs5.
        destruct (in_dec attribute_dec attribute_readnone attributes2); simpl;
          [by econs; intros; auto|].
        destruct (in_dec attribute_dec attribute_readonly attributes2); simpl;
          [by econs; intros; auto|].
        econs; intros; auto; by destruct H as [|[]].
    - destruct const5; try done.
      destruct (lookupFdecViaIDFromModule m id0) as [fdec|].
      + destruct fdec. destruct fheader5. destruct fnattrs5.
        destruct (in_dec attribute_dec attribute_readnone attributes2); simpl;
          [by econs; intros; auto|].
        destruct (in_dec attribute_dec attribute_readonly attributes2); simpl;
          [by econs; intros; auto|].
        destruct (lookupFdefViaIDFromModule m id0);
          [|by econs; intros; auto; by destruct H as [[]|]].
        destruct f. destruct fheader5. destruct fnattrs5.
        destruct (in_dec attribute_dec attribute_readnone attributes3); simpl;
          [by econs; intros; auto|].
        destruct (in_dec attribute_dec attribute_readonly attributes3); simpl;
          [by econs; intros; auto|].
        econs; intros; auto; by destruct H as [[]|[]].
      + destruct (lookupFdefViaIDFromModule m id0);
          [|by econs; intros; auto; by destruct H as [[]|]].
        destruct f. destruct fheader5. destruct fnattrs5.
        destruct (in_dec attribute_dec attribute_readnone attributes2); simpl;
          [by econs; intros; auto|].
        destruct (in_dec attribute_dec attribute_readonly attributes2); simpl;
          [by econs; intros; auto|].
        econs; intros; auto; by destruct H as [|[]]. *)
  Qed.

  Lemma is_call_readonly_iff m st :
    is_call_readonly' m st <-> is_call_readonly''' m st.
  Proof.
    econs; intro.
    - apply is_call_readonly_iff'. by inv H.
    - econs. by apply is_call_readonly_iff'.
  Qed.

  Inductive match_call
    (rel: atom -> meminj -> list mblock -> list mblock ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      Prop) :
    atom -> meminj -> list mblock -> list mblock ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
  | match_call_intro :
    forall
      pbid alpha li1 li2
      fdef1 block1 cmds1 term1 locals1 allocas1 pecs1 mem1 n1 pns1
      fdef2 block2 cmds2 term2 locals2 allocas2 pecs2 mem2 n2 pns2
      id1 noret1 clattrs1 typ1 varg1 value1 params1
      id2 noret2 clattrs2 typ2 varg2 value2 params2
      ncmds1 nn1 (Hpop1: ret_pop_cmd (ret (insn_call id1 noret1 clattrs1 typ1 varg1 value1 params1)) ncmds1 nn1 = pop_one_X cmds1 n1)
      ncmds2 nn2 (Hpop2: ret_pop_cmd (ret (insn_call id2 noret2 clattrs2 typ2 varg2 value2 params2)) ncmds2 nn2 = pop_one_X cmds2 n2)
      (Hnoret: noret_dec noret1 noret2)
      (Hclattrs: decs.clattrs_dec clattrs1 clattrs2)
      (Htyp: typ_dec typ1 typ2)
      (Hvarg: varg_dec varg1 varg2)
      (Hsame_call: is_same_call
        (mkState (mkEC fdef1 block1 cmds1 term1 locals1 allocas1) pecs1 mem1)
        (mkState (mkEC fdef2 block2 cmds2 term2 locals2 allocas2) pecs2 mem2))
      (Hparams:
        exists gvs1, ret gvs1 = @params2GVs DGVs (CurTargetData cfg1) params1 locals1 (Globals cfg1) /\
        exists gvs2, ret gvs2 = @params2GVs DGVs (CurTargetData cfg2) params2 locals2 (Globals cfg2) /\
        genericvalues_inject.gv_list_inject alpha gvs1 gvs2)
      (Hnext:
        forall alpha' (Hincr: inject_incr' alpha alpha' li1 pi1 li2 pi2)
          mem1' mem2'
          (Hvmem: valid_memories alpha' gmax mem1' mem2' li1 pi1 li2 pi2)
          (Hvals: valid_allocas mem1' mem2' allocas1 allocas2)
          (Hmem1: Mem.nextblock mem1 <= Mem.nextblock mem1')
          (Hmem2: Mem.nextblock mem2 <= Mem.nextblock mem2')          

          (Heqm1: is_call_readonly' m1 (mkState (mkEC fdef1 block1 cmds1 term1 locals1 allocas1) pecs1 mem1) ->
            memory_extends (CurTargetData cfg1) mem1' mem1)
          (Heqm2: is_call_readonly' m2 (mkState (mkEC fdef2 block2 cmds2 term2 locals2 allocas2) pecs2 mem2) ->
            memory_extends (CurTargetData cfg2) mem2' mem2)

          ec1' ec2'
          (Hnoret: if noret1
           then ec1' = mkEC fdef1 block1 ncmds1 term1 locals1 allocas1 /\
                ec2' = mkEC fdef2 block2 ncmds2 term2 locals2 allocas2
           else
             exists rv1, exists rv2,
               genericvalues_inject.gv_inject alpha' rv1 rv2 /\
               ec1' = mkEC fdef1 block1 ncmds1 term1 (updateAddAL _ locals1 id1 rv1) allocas1 /\
               ec2' = mkEC fdef2 block2 ncmds2 term2 (updateAddAL _ locals2 id2 rv2) allocas2)

          (Hwf1': OpsemPP.wf_State cfg1 (mkState ec1' pecs1 mem1'))
          (Hwf2': OpsemPP.wf_State cfg2 (mkState ec2' pecs2 mem2')),
          rel pbid alpha' li1 li2
          (ec1'::pecs1) mem1' (nn1::pns1)
          (ec2'::pecs2) mem2' (nn2::pns2)),
      match_call
      rel pbid alpha li1 li2
      ((mkEC fdef1 block1 cmds1 term1 locals1 allocas1)::pecs1) mem1 (n1::pns1)
      ((mkEC fdef2 block2 cmds2 term2 locals2 allocas2)::pecs2) mem2 (n2::pns2).

  Inductive match_return :
    meminj ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
  | match_return_value :
    forall
      alpha
      fdef1 block1 id1 typ1 ret1 locals1 allocas1 pecs1 mem1 n1 pns1
      fdef2 block2 id2 typ2 ret2 locals2 allocas2 pecs2 mem2 n2 pns2
      (Hn1: negb (noop_idx_zero_exists n1))
      (Hn2: negb (noop_idx_zero_exists n2))
      (Htyp: typ_dec typ1 typ2)
      retval1 (Hretval1: ret retval1 = @getOperandValue DGVs (CurTargetData cfg1) ret1 locals1 (Globals cfg1))
      retval2 (Hretval2: ret retval2 = @getOperandValue DGVs (CurTargetData cfg2) ret2 locals2 (Globals cfg2))
      (Hinj: genericvalues_inject.gv_inject alpha retval1 retval2),
      match_return
      alpha
      ((mkEC fdef1 block1 nil (insn_return id1 typ1 ret1) locals1 allocas1)::pecs1) mem1 (n1::pns1)
      ((mkEC fdef2 block2 nil (insn_return id2 typ2 ret2) locals2 allocas2)::pecs2) mem2 (n2::pns2)
  | match_return_void :
    forall
      alpha
      fdef1 block1 id1 locals1 allocas1 pecs1 mem1 n1 pns1
      fdef2 block2 id2 locals2 allocas2 pecs2 mem2 n2 pns2
      (Hn1: negb (noop_idx_zero_exists n1))
      (Hn2: negb (noop_idx_zero_exists n2)),
      match_return
      alpha
      ((mkEC fdef1 block1 nil (insn_return_void id1) locals1 allocas1)::pecs1) mem1 (n1::pns1)
      ((mkEC fdef2 block2 nil (insn_return_void id2) locals2 allocas2)::pecs2) mem2 (n2::pns2).

  Inductive is_ordinary cfg st ns : Prop :=
  | is_ordinary_stuttering :
    forall
      nhd ntl (Hns: ns = nhd::ntl)
      x (Hstut: S x = stutter_num nhd),
      is_ordinary cfg st ns
  | is_ordinary_cmd :
    forall
      (Hncall: forall fid, ~ is_call cfg st fid)
      (Hnexcall: forall fdec, ~ is_excall cfg st fdec)
      (Hnret: ~ is_return st),
      is_ordinary cfg st ns.

  Definition F_progress :
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
    fun
      ecs1 mem1 ns1
      ecs2 mem2 ns2 =>

      forall
        ec1 ec1' ecs1' mem1' ns1' na1' tr1
        (Hstep1: logical_semantic_step cfg1 fn_al1 (mkState ec1 ecs1 mem1) (mkState ec1' ecs1' mem1') ns1 ns1' na1' tr1),

        (* exists *)
        (exists ec2 ec2' ecs2', exists mem2', exists ns2', exists na2', exists tr2,
          logical_semantic_step cfg2 fn_al2 (mkState ec2 ecs2 mem2) (mkState ec2' ecs2' mem2') ns2 ns2' na2' tr2).

  Definition F_step
    (rel:
      atom -> meminj -> list mblock -> list mblock ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      Prop) :
    atom -> meminj -> list mblock -> list mblock ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
    fun pbid alpha li1 li2
      ecs1 mem1 ns1
      ecs2 mem2 ns2 =>

      forall
        ec1 ec1' ecs1' ec2 mem1' ns1' na1' tr1
        (Hstep1: logical_semantic_step cfg1 fn_al1 (mkState ec1 ecs1 mem1) (mkState ec1' ecs1' mem1') ns1 ns1' na1' tr1),

        (* logical step *)
        (is_ordinary cfg1 (mkState ec1 ecs1 mem1) ns1 /\
         is_ordinary cfg2 (mkState ec2 ecs2 mem2) ns2 /\
         forall 
          ec2' ecs2' mem2' ns2' na2' tr
          (Hstep: logical_semantic_step cfg2 fn_al2 (mkState ec2 ecs2 mem2) (mkState ec2' ecs2' mem2') ns2 ns2' na2' tr),
          exists pbid', exists alpha', exists li1', exists li2', exists ecs1', exists mem1', exists ns1', exists na1',
            logical_semantic_step cfg1 fn_al1 (mkState ec1 ecs1 mem1) (mkState ec1' ecs1' mem1') ns1 ns1' na1' tr /\
            inject_incr' alpha alpha' li1 pi1 li2 pi2 /\
            rel pbid' alpha' li1' li2' ecs1' mem1' ns1' ecs2' mem2' ns2') \/
         (* call *)
        (match_call rel pbid alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2) \/
         (* return *)
        (match_return alpha ecs1 mem1 ns1 ecs2 mem2 ns2).
  
  Definition F
    (rel:
      atom -> meminj -> list mblock -> list mblock ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      Prop) :
    atom -> meminj -> list mblock -> list mblock ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
    fun pbid alpha li1 li2
      ecs1 mem1 ns1
      ecs2 mem2 ns2 =>

      F_progress
      ecs1 mem1 ns1
      ecs2 mem2 ns2 /\

      F_step rel
      pbid alpha li1 li2
      ecs1 mem1 ns1
      ecs2 mem2 ns2.

  Inductive hint_sem :
    atom -> meminj -> list mblock -> list mblock ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=

  | hint_sem_intro :
    forall pbid alpha li1 li2 bid
      ec1 phis1 all_cmds1 cmds1 term1 locals1 allocas1 pecs1 mem1 n1 pns1
      ec2 phis2 all_cmds2 cmds2 term2 locals2 allocas2 pecs2 mem2 n2 pns2
      (Hec1: ec1 = mkEC fdef1 (bid, stmts_intro phis1 all_cmds1 term1) cmds1 term1 locals1 allocas1)
      (Hec2: ec2 = mkEC fdef2 (bid, stmts_intro phis2 all_cmds2 term2) cmds2 term2 locals2 allocas2)
      (Hstmts1: ret (stmts_intro phis1 all_cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid)
      (Hstmts2: ret (stmts_intro phis2 all_cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)
      (Hctx: same_context ec1 ec2 fid)

      (Hwf1: OpsemPP.wf_State cfg1 (mkState ec1 pecs1 mem1))
      (Hwf2: OpsemPP.wf_State cfg2 (mkState ec2 pecs2 mem2))
      (Hpecs: list_forall2
        (fun ec1 ec2 =>
          match CurCmds ec1, CurCmds ec2 with
            | (insn_call _ noret1 _ _ _ _ _)::_, (insn_call _ noret2 _ _ _ _ _)::_ =>
              noret_dec noret1 noret2
            | _, _ =>
              False
          end)
        pecs1 pecs2)

      (Hgna1: globals_no_alias (Globals cfg1))
      (Hgna2: globals_no_alias (Globals cfg2))
      (Hftable: ftable_simulation alpha (FunTable cfg1) (FunTable cfg2))
      (Htd: CurTargetData cfg1 = CurTargetData cfg2)

      an1 (Han1: an1 = get_noop_by_bb bid (lookupALOpt _ fn_al1 fid))
      an2 (Han2: an2 = get_noop_by_bb bid (lookupALOpt _ fn_al2 fid))
      block_hint (Hblock_hint: ret block_hint = lookupAL _ (block_hints fh) bid)
      hints (Hhints: ret hints = lookupAL _ (cmds_hint block_hint) pbid)
      hint (Hhint: hint_lookup hint cmds1 cmds2 n1 n2 all_cmds1 all_cmds2 an1 an2 hints)
      
      (Hinsn: hint_sem_insn hint pecs1 pecs2 pns1 pns2 pi1 pi2 li1 li2
        alpha gmax
        cfg1 (ec1::pecs1) mem1 (n1::pns1)
        cfg2 (ec2::pecs2) mem2 (n2::pns2)),

      hint_sem pbid alpha li1 li2
      (ec1::pecs1) mem1 (n1::pns1)
      (ec2::pecs2) mem2 (n2::pns2).

  Variable (Hvalid: valid_fdef m1 m2 fdef1 fdef2 (lookupALOpt _ fn_al1 fid) (lookupALOpt _ fn_al2 fid) fh).

  Inductive valid_edge pbid bid : Prop :=
  | valid_edge_intro :
    forall
      pphis2 pcmds2 pterm2 (Hpstmts2: ret (stmts_intro pphis2 pcmds2 pterm2) = lookupBlockViaLabelFromFdef fdef2 pbid)
      phis2 cmds2 term2 (Hstmts2: ret (stmts_intro phis2 cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)
      (Hin: List.In bid (basic_aux.get_all_nexts pterm2)),
      valid_edge pbid bid.

  Lemma Hvalid_block
    bid
    phis2 cmds2 term2 (Hstmts2: ret (stmts_intro phis2 cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid) :
    exists phis1, exists cmds1, exists term1,
      ret (stmts_intro phis1 cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid /\
      valid_block m1 m2 (bid, stmts_intro phis1 cmds1 term1) (bid, stmts_intro phis2 cmds2 term2) (lookupALOpt _ fn_al1 fid) (lookupALOpt _ fn_al2 fid) (block_hints fh).
  Proof.
    clear Hfid.
    destruct fdef1, fdef2. simpl in Hstmts2.
    apply andb_true_iff in Hvalid. destruct Hvalid as [_ Hvalid_blocks]. clear Hvalid.
    generalize dependent Hvalid_blocks.
    generalize dependent Hstmts2.
    generalize dependent blocks0.
    induction blocks5; destruct blocks0; intros Hstmts2 Hvalid_blocks; try done.
    apply andb_true_iff in Hvalid_blocks; fold valid_blocks in Hvalid_blocks.
    destruct Hvalid_blocks as [Hvalid_block Hvalid_blocks].
    destruct a, b.
    apply andb_true_iff in Hvalid_block; destruct Hvalid_block as [H1 H2].
    destruct (id_dec l0 l1); inv H1.
    rewrite lookupAL_cons in Hstmts2.
    unfold lookupBlockViaLabelFromFdef. rewrite lookupAL_cons.
    destruct (id_dec bid l1); [subst|].
    - inv Hstmts2.
      destruct s. eexists. eexists. eexists. split; auto.
      apply andb_true_iff; split; [by destruct (id_dec l1 l1)|].
      done.
    - by eapply IHblocks5; eauto.
  Qed.

  Lemma Hvalid_edge
    pbid bid (Hedge: valid_edge pbid bid)
    pblock_hint (Hpblock_hint: ret pblock_hint = lookupAL _ (block_hints fh) pbid) :
    exists phis1, exists cmds1, exists term1,
    exists phis2, exists cmds2, exists term2,
      ret (stmts_intro phis1 cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid /\
      ret (stmts_intro phis2 cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid /\
      exists block_hint, exists hint,
        ret block_hint = lookupAL _ (block_hints fh) bid /\
        ret hint = lookupAL _ (phi_hint block_hint) pbid /\
        invariant_implies (infrules_resolve m1 m2 (term_hint pblock_hint)) hint.
  Proof.
    inv Hedge.
    exploit (Hvalid_block pbid); eauto.
    intros [pphis1 [pcmds1 [pterm1 [Hpstmts1 Hpvalid_block]]]].
    apply andb_true_iff in Hpvalid_block; destruct Hpvalid_block as [_ Hpvalid_block].
    rewrite <- Hpblock_hint in Hpvalid_block.
    unfold valid_stmts in Hpvalid_block. destruct_and.
    apply andb_true_iff in H0. destruct_and.
    simpl in H3.
    generalize dependent H3.
    generalize dependent Hin.
    generalize (basic_aux.get_all_nexts pterm2) as bids.
    induction bids; intro Hin; [by inv Hin|]; simpl.
    intros HH. apply andb_true_iff in HH. destruct HH as [Hterm Hterms].
    remember (lookupAL _ (block_hints fh) a) as block_hint; destruct block_hint as [block_hint|]; [|done].
    remember (lookupAL _ (phi_hint block_hint) pbid) as hint; destruct hint as [hint|]; [|done].
    inv Hin.
    - exploit (Hvalid_block bid); eauto.
      intros [phis1 [cmds1 [term1 [Hstmts1 Hvalid_block]]]].
      apply andb_true_iff in Hvalid_block; destruct Hvalid_block as [_ Hvalid_block].
      rewrite <- Heqblock_hint in Hvalid_block.
      unfold valid_stmts in Hvalid_block. destruct_and.
      exists phis1. exists cmds1. exists term1.
      exists phis2. exists cmds2. exists term2.
      split; [done|].
      split; [done|].
      eexists. eexists.
      by repeat split; eauto.
    - by apply IHbids.
  Qed.    

  Lemma Hvalid_phi
    pbid bid (Hedge: valid_edge pbid bid)
    pblock_hint (Hpblock_hint: ret pblock_hint = lookupAL _ (block_hints fh) pbid)
    phis1 cmds1 term1 (Hstmts1: ret (stmts_intro phis1 cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid)
    phis2 cmds2 term2 (Hstmts2: ret (stmts_intro phis2 cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)
    block_hint (Hblock_hint: ret block_hint = lookupAL _ (block_hints fh) bid)
    hint (Hhint: ret hint = lookupAL _ (phi_hint block_hint) pbid) :
    exists hint', exists hints'', exists hint'',
      ret hint' = invariant_proceed_phis hint phis1 phis2 pbid /\
      ret hints'' = lookupAL _ (cmds_hint block_hint) pbid /\
      (forall an1 an2, hint_lookup hint'' cmds1 cmds2 an1 an2 cmds1 cmds2 an1 an2 hints'') /\
      invariant_implies (infrules_resolve m1 m2 hint') hint''.
  Proof.
    exploit Hvalid_block; eauto.
    intros [phis1' [cmds1' [term1' [Hstmts1' Hvalid_block]]]].
    rewrite <- Hstmts1 in Hstmts1'. inv Hstmts1'.
    apply andb_true_iff in Hvalid_block0; destruct Hvalid_block0 as [_ Hvalid_block].
    rewrite <- Hblock_hint in Hvalid_block.
    apply andb_true_iff in Hvalid_block. destruct_and.
    generalize dependent H.
    generalize dependent Hhint.
    generalize (cmds_hint block_hint).
    generalize (phi_hint block_hint).
    induction a; [|destruct a]; intro b; destruct b as [|[]]; intros Hhint Hvalid_phis;
      (try by inv Hhint);
      (try by inv Hvalid_phis).
    destruct l0; [done|].
    unfold valid_AL_phis in Hvalid_phis. fold valid_AL_phis in Hvalid_phis.
    destruct_and. apply decs.l_dec_r in H; inv H. rewrite lookupAL_cons in *.
    destruct (id_dec pbid a1); [subst|].
    - unfold valid_phis in H4. inv Hhint.
      remember (invariant_proceed_phis i0 phis1 phis2 a1) as hint''; destruct hint'' as [hint''|]; [|done].
      eexists. eexists. eexists.
      repeat split; try by eauto.
      by constructor.
    - by exploit IHa; eauto.
  Qed.

  Lemma Hvalid_cmds
    pbid bid
    phis2 cmds2 term2 (Hstmts2: ret (stmts_intro phis2 cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)
    block_hint (Hblock_hint: ret block_hint = lookupAL _ (block_hints fh) bid)
    hints (Hhint: ret hints = lookupAL _ (cmds_hint block_hint) pbid) :
    exists phis1, exists cmds1, exists term1,
      ret (stmts_intro phis1 cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid /\
      valid_cmds m1 m2 cmds1 cmds2 (get_noop_by_bb bid (lookupALOpt _ fn_al1 fid)) (get_noop_by_bb bid (lookupALOpt _ fn_al2 fid)) hints.
  Proof.
    exploit Hvalid_block; eauto.
    intros [phis1 [cmds1 [term1 [Hstmts1 Hvalid_block]]]].
    eexists. eexists. eexists. split; [by eauto|].
    apply andb_true_iff in Hvalid_block; destruct Hvalid_block as [_ Hvalid_block].
    rewrite <- Hblock_hint in Hvalid_block.
    unfold valid_stmts in Hvalid_block. destruct_and.
    unfold valid_AL_cmds in H2; simpl in H2.
    eapply forallb_forall in H2.
    - by instantiate (1 := (pbid, hints)) in H2.
    - generalize dependent Hhint. clear.
      induction (cmds_hint block_hint); [done|]; intro H.
      destruct a. rewrite lookupAL_cons in H.
      destruct (id_dec pbid a); [subst|].
      + left. by inv H.
      + right. apply IHa. done.
  Qed.

  Lemma Hvalid_cmd
    bid block_hint (Hblock_hint: ret block_hint = lookupAL _ (block_hints fh) bid)
    pbid hints (Hhints: ret hints = lookupAL _ (cmds_hint block_hint) pbid)
    phis1 cmds1 term1 (Hstmts1: ret (stmts_intro phis1 cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid)
    phis2 cmds2 term2 (Hstmts2: ret (stmts_intro phis2 cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)
    
    hint cur1 n1 cur2 n2 cur2' n2' cmd_opt2
    (Hlookup: hint_lookup hint cur1 cur2 n1 n2 cmds1 cmds2 (get_noop_by_bb bid (lookupALOpt _ fn_al1 fid)) (get_noop_by_bb bid (lookupALOpt _ fn_al2 fid)) hints)
    (H2: (ret_pop_cmd cmd_opt2 cur2' n2') = pop_one_X cur2 n2) :
    exists cmd_opt1, exists cur1', exists n1', exists hint', exists hint'',
      (ret_pop_cmd cmd_opt1 cur1' n1') = pop_one_X cur1 n1 /\
      ret hint' = invariant_proceed m1 m2 hint cmd_opt1 cmd_opt2 /\
      hint_lookup hint'' cur1' cur2' n1' n2' cmds1 cmds2 (get_noop_by_bb bid (lookupALOpt _ fn_al1 fid)) (get_noop_by_bb bid (lookupALOpt _ fn_al2 fid)) hints /\
      invariant_implies (infrules_resolve m1 m2 hint') hint''.
  Proof.
    exploit Hvalid_cmds; eauto. clear Hvalid.
    intros [phis1' [cmds1' [term1' [Hstmts1' Hvalid_cmds]]]].
    rewrite <- Hstmts1 in Hstmts1'. inv Hstmts1'.
    generalize dependent Hvalid_cmds0.
    clear Hstmts1 Hstmts2 Hhints.
    generalize dependent cmds2.
    generalize dependent cmds1.
    generalize ((get_noop_by_bb bid (lookupALOpt one_noop_t fn_al2 fid))).
    generalize ((get_noop_by_bb bid (lookupALOpt one_noop_t fn_al1 fid))).
    induction hints; intros an1 an2 cmds1 cmds2 Hlookup Hvalid_cmds; [by inv Hlookup|].
    unfold valid_cmds in Hvalid_cmds. fold valid_cmds in Hvalid_cmds.
    inv Hlookup.
    - rewrite <- H2 in Hvalid_cmds.
      remember (pop_one_X cmds1 an1) as pop1; destruct pop1; [|done].
      destruct hints as [|hint'' hints]; [done|].
      exists o. exists l0. exists n.
      remember (invariant_proceed m1 m2 a o cmd_opt2) as hint'; destruct hint' as [hint'|]; [|done].
      destruct_and.
      exists hint'. exists hint''. repeat split; auto.
      econstructor; eauto.
      by constructor.
    - rewrite <- Hpop1, <- Hpop2 in Hvalid_cmds.
      destruct hints as [|hint' hints]; [done|].
      remember (invariant_proceed m1 m2 a cmd_opt1 cmd_opt0) as hint''; destruct hint'' as [hint''|]; [|done].
      destruct_and.
      exploit IHhints; eauto.
      intros [cmd_opt3 [cur1' [n1' [hint'0 [hint''0 HH]]]]]. destruct_and.
      eexists. eexists. eexists. eexists. eexists. repeat split; eauto.
      by econstructor; eauto.
  Qed.  

  Lemma Hvalid_term
    bid block_hint (Hblock_hint: ret block_hint = lookupAL _ (block_hints fh) bid)
    pbid hints (Hhints: ret hints = lookupAL _ (cmds_hint block_hint) pbid)
    phis1 cmds1 term1 (Hstmts1: ret (stmts_intro phis1 cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid)
    phis2 cmds2 term2 (Hstmts2: ret (stmts_intro phis2 cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)
    
    an1 (Han1: an1 = get_noop_by_bb bid (lookupALOpt _ fn_al1 fid))
    an2 (Han2: an2 = get_noop_by_bb bid (lookupALOpt _ fn_al2 fid))
    hint cur1 n1 cur2 n2
    (Hlookup: hint_lookup hint cur1 cur2 n1 n2 cmds1 cmds2 an1 an2 hints)
    (Hterm2: ret_pop_terminator = pop_one_X cur2 n2) :
    ret_pop_terminator = pop_one_X cur1 n1 /\
    invariant_implies hint (term_hint block_hint) /\
    terminator_args_eq_check term1 term2 (term_hint block_hint).
  Proof.
    exploit Hvalid_block; eauto.
    intros [phis1' [cmds1' [term1' [Hstmts1' Hvalid_block]]]].
    rewrite <- Hstmts1 in Hstmts1'. inv Hstmts1'.
    apply andb_true_iff in Hvalid_block0; destruct Hvalid_block0 as [_ Hvalid_block].
    rewrite <- Hblock_hint in Hvalid_block.
    unfold valid_stmts in Hvalid_block. destruct_and.
    apply andb_true_iff in H0. destruct H0 as [Hvalid_term _].
    unfold valid_AL_cmds_to_term in H1; simpl in H1.
    eapply forallb_forall in H1.
    instantiate (1 := (pbid, hints)) in H1. simpl in H1.
    unfold valid_AL_cmds in H2; simpl in H2.
    eapply forallb_forall in H2.
    instantiate (1 := (pbid, hints)) in H2. simpl in H2.
    - clear H Hstmts1 Hstmts2 Hhints.
      generalize dependent cmds2.
      generalize dependent cmds1.
      generalize (get_noop_by_bb bid (lookupALOpt one_noop_t fn_al2 fid)).
      generalize (get_noop_by_bb bid (lookupALOpt one_noop_t fn_al1 fid)).
      generalize dependent H1.
      induction hints; intros Hvalid_terms an1 an2 cmds1 cmds2 Hlookup Hvalid_cmds; [by inv Hvalid_terms|].
      inv Hlookup.
      + unfold valid_cmds in Hvalid_cmds.
        rewrite <- Hterm2 in Hvalid_cmds.
        remember (pop_one_X cmds1 an1) as pop1; destruct pop1; [done|].
        by destruct hints.
      + unfold valid_cmds in Hvalid_cmds. fold valid_cmds in Hvalid_cmds.
        rewrite <- Hpop1, <- Hpop2 in Hvalid_cmds.
        destruct hints as [|hint' hints]; [done|].
        remember (invariant_proceed m1 m2 a cmd_opt1 cmd_opt2) as hint''; destruct hint'' as [hint''|]; [|done].
        destruct_and.
        by exploit IHhints; eauto.
    - generalize dependent Hhints. clear.
      induction (cmds_hint block_hint); [done|]; intro H.
      destruct a. rewrite lookupAL_cons in H.
      destruct (id_dec pbid a); [subst|].
      + left. by inv H.
      + right. apply IHa. done.
    - generalize dependent Hhints. clear.
      induction (cmds_hint block_hint); [done|]; intro H.
      destruct a. rewrite lookupAL_cons in H.
      destruct (id_dec pbid a); [subst|].
      + left. by inv H.
      + right. apply IHa. done.
  Qed.

  Lemma Hvalid_term_2
    bid block_hint (Hblock_hint: ret block_hint = lookupAL _ (block_hints fh) bid)
    pbid hints (Hhints: ret hints = lookupAL _ (cmds_hint block_hint) pbid)
    phis1 cmds1 term1 (Hstmts1: ret (stmts_intro phis1 cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid)
    phis2 cmds2 term2 (Hstmts2: ret (stmts_intro phis2 cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)
    
    an1 (Han1: an1 = get_noop_by_bb bid (lookupALOpt _ fn_al1 fid))
    an2 (Han2: an2 = get_noop_by_bb bid (lookupALOpt _ fn_al2 fid))
    hint cur1 n1 cur2 n2
    (Hlookup: hint_lookup hint cur1 cur2 n1 n2 cmds1 cmds2 an1 an2 hints)
    (Hterm1: ret_pop_terminator = pop_one_X cur1 n1) :
    ret_pop_terminator = pop_one_X cur2 n2 /\
    invariant_implies hint (term_hint block_hint) /\
    terminator_args_eq_check term1 term2 (term_hint block_hint).
  Proof.
    exploit Hvalid_block; eauto.
    intros [phis1' [cmds1' [term1' [Hstmts1' Hvalid_block]]]].
    rewrite <- Hstmts1 in Hstmts1'. inv Hstmts1'.
    apply andb_true_iff in Hvalid_block0; destruct Hvalid_block0 as [_ Hvalid_block].
    rewrite <- Hblock_hint in Hvalid_block.
    unfold valid_stmts in Hvalid_block. destruct_and.
    apply andb_true_iff in H0. destruct H0 as [Hvalid_term _].
    unfold valid_AL_cmds_to_term in H1; simpl in H1.
    eapply forallb_forall in H1.
    instantiate (1 := (pbid, hints)) in H1. simpl in H1.
    unfold valid_AL_cmds in H2; simpl in H2.
    eapply forallb_forall in H2.
    instantiate (1 := (pbid, hints)) in H2. simpl in H2.
    - clear H Hstmts1 Hstmts2 Hhints.
      generalize dependent cmds2.
      generalize dependent cmds1.
      generalize (get_noop_by_bb bid (lookupALOpt one_noop_t fn_al2 fid)).
      generalize (get_noop_by_bb bid (lookupALOpt one_noop_t fn_al1 fid)).
      generalize dependent H1.
      induction hints; intros Hvalid_terms an1 an2 cmds1 cmds2 Hlookup Hvalid_cmds; [by inv Hvalid_terms|].
      inv Hlookup.
      + unfold valid_cmds in Hvalid_cmds.
        rewrite <- Hterm1 in Hvalid_cmds.
        remember (pop_one_X cmds2 an2) as pop2; destruct pop2; [done|].
        by destruct hints.
      + unfold valid_cmds in Hvalid_cmds. fold valid_cmds in Hvalid_cmds.
        rewrite <- Hpop1, <- Hpop2 in Hvalid_cmds.
        destruct hints as [|hint' hints]; [done|].
        remember (invariant_proceed m1 m2 a cmd_opt1 cmd_opt2) as hint''; destruct hint'' as [hint''|]; [|done].
        destruct_and.
        by exploit IHhints; eauto.
    - generalize dependent Hhints. clear.
      induction (cmds_hint block_hint); [done|]; intro H.
      destruct a. rewrite lookupAL_cons in H.
      destruct (id_dec pbid a); [subst|].
      + left. by inv H.
      + right. apply IHa. done.
    - generalize dependent Hhints. clear.
      induction (cmds_hint block_hint); [done|]; intro H.
      destruct a. rewrite lookupAL_cons in H.
      destruct (id_dec pbid a); [subst|].
      + left. by inv H.
      + right. apply IHa. done.
  Qed.

  Inductive cmd'_t : Set :=
  | cmd'_cmd
  | cmd'_call.

  Definition cmd' (cmd_opt:monad cmd) :=
    match cmd_opt with
      | ret (insn_call _ _ _ _ _ _ _) => cmd'_call
      | _ => cmd'_cmd
    end.

  Inductive term'_t : Set :=
  | term'_unreachable
  | term'_return
  | term'_branch.

  Definition term' (term:terminator) :=
    match term with
      | insn_return _ _ _
      | insn_return_void _ => term'_return
      | insn_br _ _ _ _
      | insn_br_uncond _ _ => term'_branch
      | insn_unreachable _ => term'_unreachable
    end.

  Lemma logical_semantic_step_term_na_merror
    cfg fn_al fdef bb cmds term locals allocas pecs mem ec ecs' mem' n ns ns' na tr
    (Hstep: logical_semantic_step cfg fn_al
      (mkState (mkEC fdef bb cmds term locals allocas) pecs mem)
      (mkState ec ecs' mem')
      (n::ns) ns' na tr)
    (Hpop: ret_pop_terminator = pop_one_X cmds n) :
    na = merror.
  Proof.
    inv Hstep. inv Hec. inv Hpn. simpl in *.
    inv Hpop0; [|done]. admit. (*
    by rewrite Hpop1 in Hpop. *)
  Qed.

  Lemma logical_semantic_step_term_tr_E0
    cfg fn_al fdef bb cmds term locals allocas pecs mem ec' ecs' mem' n ns ns' na tr
    (Hstep: logical_semantic_step cfg fn_al
      (mkState (mkEC fdef bb cmds term locals allocas) pecs mem)
      (mkState ec' ecs' mem')
      (n::ns) ns' na tr)
    (Hpop: ret_pop_terminator = pop_one_X cmds n) :
    tr = E0.
  Proof.
    inv Hstep. inv Hec. inv Hpn. simpl in *. admit. (*
    inv Hpop0.
    rewrite Hpop1 in Hpop; inv Hpop.
    unfold pop_one_X in Hpop.
    destruct (noop_idx_zero_exists hpn); [done|].
    destruct cmds; [|done].
    by inv Hstep0. *)
  Qed.

  Lemma logical_semantic_step_branch_inv
    cfg fn_al fdef bb cmds term locals allocas pecs mem ec' ecs' mem' n ns ns' na tr
    (Hterm: term'_branch = term' term)
    (Hstep: logical_semantic_step cfg fn_al
      (mkState (mkEC fdef bb cmds term locals allocas) pecs mem)
      (mkState ec' ecs' mem')
      (n::ns) ns' na tr)
    (Hpop: ret_pop_terminator = pop_one_X cmds n) :
    exists l', exists phis', exists cmds', exists term', exists lc',
      na = merror /\
      ret stmts_intro phis' cmds' term' = lookupBlockViaLabelFromFdef fdef l' /\
      (mkEC fdef (l', stmts_intro phis' cmds' term') cmds' term' lc' allocas)::pecs = ecs' /\
      (get_noop_by_bb l' (lookupALOpt one_noop_t fn_al (getFdefID fdef)))::ns = ns'.
  Proof.
    inv Hstep. inv Hec. inv Hpn. simpl in *. admit. (*
    inv Hpop0.
    rewrite Hpop1 in Hpop; inv Hpop.
    unfold pop_one_X in Hpop.
    destruct (noop_idx_zero_exists hpn); [done|].
    destruct cmds; [|done].
    destruct term; inv Hterm.
    - inv Hstep0.
      inv Hnoop; [by inv Hnnn|].
      inv Hnnn; [by destruct Hret|].
      destruct Hbrc as [_ Hbrc]. simpl in *.
      destruct Hbrc as [conds' [c' [Hconds [Hc Hbid]]]].
      rewrite getOperandValue_compat in *. rewrite Hconds in H13. inv H13.
      inv H14. inv Hc.
      assert (bid = if isGVZero TD c' then l2 else l1); [by destruct (isGVZero TD c')|subst].
      repeat eexists; try done.
      rewrite H15. by destruct (isGVZero TD c').
    - inv Hstep0.
      inv Hnoop; [by inv Hnnn|].
      inv Hnnn; [by destruct Hret|].
      destruct Hbrc as [_ Hbrc]. simpl in *. subst.
      by repeat eexists. *)
  Qed.

  Lemma logical_semantic_step_cmd_inv
    cfg fn_al fdef bb cmds term locals allocas pecs mem ec' ecs' mem' n ns ns' na tr
    (Hstep: logical_semantic_step cfg fn_al
      (mkState (mkEC fdef bb cmds term locals allocas) pecs mem)
      (mkState ec' ecs' mem')
      (n::ns) ns' na tr)
    ocmd nc nn (Hpop: ret_pop_cmd ocmd nc nn = pop_one_X cmds n)
    (Hncall: forall id, ~ is_general_call ocmd id) :
    exists lc', exists allocas',
      (mkEC fdef bb nc term lc' allocas')::pecs = ecs' /\
      ns' = nn::ns.
  Proof.
    inv Hstep. inv Hec. inv Hpn. simpl in *. admit. (*
    inv Hpop0; rewrite <- Hpop in Hpop1; inv Hpop1.
    inv Hnoop; [|by destruct rcmd].
    destruct rcmd.
    - (* cmd *)
      unfold pop_one_X in Hpop.
      remember (noop_idx_zero_exists hpn) as nhpn; destruct nhpn; [done|].
      destruct cmds; [done|].
      inv Hpop.
      inv Hnnn; try done.
      + (* cmd *)
        inv Hstep0; try by eexists; eexists; repeat split; eauto.
        by elim (Hncall rid).
      + (* call *)
        destruct cfg, c0; try done.
        by elim (Hncall id5).
      + (* excall *)
        destruct cfg, c0; try done.
        by elim (Hncall id5).
    - (* nop *)
      inv Hstep0. inv H. inv Hnnn; try done.
      eexists. eexists.
      repeat split; repeat f_equal; eauto.
      inv Hpop. unfold pop_one_X in H0.
      destruct (noop_idx_zero_exists hpn); [by inv H0|].
      by destruct cmds. *)
  Qed.

  Lemma inject_incr'_refl alpha l1 p1 l2 p2 :
    inject_incr' alpha alpha l1 p1 l2 p2.
  Proof. done. Qed.

  Lemma logical_step_preservation
    cfg fn_al (Hcfg: OpsemPP.wf_Config cfg)
    (ps ns:@State DGVs) (pn nn:noop_stack_t) (na:new_alloca_t) (tr:trace)
    (Hstep: logical_semantic_step cfg fn_al ps ns pn nn na tr)
    (Hp: OpsemPP.wf_State cfg ps) :
    OpsemPP.wf_State cfg ns.
  Proof.
    destruct ps, ns. inv Hstep. simpl in *. inv Hec. inv H.
    destruct pst.
    - inv Hstep0. inv H.
    done.
    - by eapply @OpsemPP.preservation; eauto.
    - by eapply @OpsemPP.preservation; eauto.
  Qed.

  Lemma align_dec_r x1 x2 (H: decs.align_dec x1 x2) : x1 = x2.
  Proof.
    eapply decs.dec_r; eauto.
  Qed.

  Lemma mem_inj__ppfree : forall mi Mem0 M2 M2' mgb hi lo
    (b2 : Values.block) (delta : Z) blk,
    genericvalues_inject.wf_sb_mi mgb mi Mem0 M2 ->
    memory_sim.MoreMem.mem_inj mi Mem0 M2 ->
    Mem.free M2 blk lo hi = ret M2' ->
    (lo, hi) = Mem.bounds M2 blk ->
    (forall sb ofs, mi sb <> ret (blk, ofs)) ->
    genericvalues_inject.wf_sb_mi mgb mi Mem0 M2' /\ memory_sim.MoreMem.mem_inj mi Mem0 M2'.
  Proof.
    intros mi Mem0 M2 M2' mgb hi lo b2 delta blk Hwfmi Hmsim1 H0 HeqR2 H4.
    split.
    SCase "wfmi".
    clear - Hwfmi H0 H4.
    inversion_clear Hwfmi.
    split; eauto with mem.
    SSCase "Hmap3".
    intros.
    by erewrite Mem.nextblock_free; eauto.
    SSCase "bounds".
    intros.
    by erewrite (Mem.bounds_free M2 _ _ _ M2'); eauto.

    SCase "msim".
    clear - Hmsim1 Hwfmi H0 H4.
    inv Hwfmi.
    eapply memory_sim.MoreMem.free_right_inj; eauto.
    intros.
    by exploit H4; eauto.
  Qed.

  Lemma free_allocas_progress
    TD alpha li1 li2 allocas1 allocas2
    (Haequiv: allocas_equivalent alpha li1 li2 allocas1 allocas2) :
    forall
      mem1 mem2
      (Hwf: genericvalues_inject.wf_sb_mi gmax alpha mem1 mem2)
      (Hinj: memory_sim.MoreMem.mem_inj alpha mem1 mem2),
      (forall b : Values.block,
        In b li2 -> forall sb : Values.block, alpha sb <> ret (b, 0)) ->
      (forall b : Values.block, In b li1 -> alpha b = merror) ->
      (forall b : mblock,
        In b li1 ->
        In b allocas1 ->
        let (l, h) := Mem.bounds mem1 b in Mem.free mem1 b l h <> merror) ->
      (forall b : mblock,
        In b li2 ->
        In b allocas2 ->
        let (l, h) := Mem.bounds mem2 b in Mem.free mem2 b l h <> merror) ->
      NoDup allocas1 ->
      NoDup allocas2 ->
      free_allocas TD mem1 allocas1 <> merror ->
      free_allocas TD mem2 allocas2 <> merror.
  Proof.
    induction Haequiv; intros mem1 mem2 Hwf Hmemi Hli2none Hli1none Hf1 Hf2 Hnd1 Hnd2 He1 He2; simpl in *.
    - by inv He2.
    - remember (free TD mem1 (blk2GV TD b1)) as mem1'; destruct mem1' as [mem1'|]; [|done].
    generalize Heqmem1'. intro X. unfold free in X. simpl in X.
    remember (Mem.bounds mem1 b1) as bounds1; destruct bounds1.
    edestruct genericvalues_inject.mem_inj__pfree; eauto.
    
    exploit (IHHaequiv mem1' mem2); eauto.
    + intros. remember (Mem.bounds mem1' b) as bounds1'; destruct bounds1'.
    Local Transparent Mem.free.
    unfold Mem.free.
    destruct (Mem.range_perm_dec mem1' b z1 z2 Freeable); [done|].
    contradict n.
    eapply memory_props.MemProps.range_perm_mfree_1; eauto.
    * split; [|done]. intro Heq; subst.
    by inv Hnd1.
    * exploit Hf1; eauto.
    erewrite <- memory_props.MemProps.bounds_mfree; eauto.
    rewrite <- Heqbounds1'.
    unfold Mem.free.
    by destruct (Mem.range_perm_dec mem1 b z1 z2 Freeable).
    Local Opaque Mem.free.
    + by inv Hnd1.
    - remember (free TD mem2 (blk2GV TD b2)) as mem2'; destruct mem2' as [mem2'|].
    generalize Heqmem2'. intro X. unfold free in X. simpl in X.
    remember (Mem.bounds mem2 b2) as bounds2; destruct bounds2.
    edestruct mem_inj__ppfree; eauto.
    + repeat intro.
    inv Hwf. exploit mi_range_block. apply H. intro HH; subst.
    by exploit Hli2none; eauto.
    + exploit (IHHaequiv mem1 mem2'); eauto.
    * intros. remember (Mem.bounds mem2' b) as bounds1'; destruct bounds1'.
    Local Transparent Mem.free.
    unfold Mem.free.
    destruct (Mem.range_perm_dec mem2' b z1 z2 Freeable); [done|].
    contradict n.
    eapply memory_props.MemProps.range_perm_mfree_1; eauto.
    split; [|done]. intro Heq; subst.
    by inv Hnd2.
    exploit Hf2; eauto.
    erewrite <- memory_props.MemProps.bounds_mfree; eauto.
    rewrite <- Heqbounds1'.
    unfold Mem.free.
    by destruct (Mem.range_perm_dec mem2 b z1 z2 Freeable).
    Local Opaque Mem.free.
    * by inv Hnd2.
    + exploit Hf2; eauto.
    unfold free in *. simpl in *.
    destruct (Mem.bounds mem2 b2).
    by rewrite <- Heqmem2'.
    - remember (free TD mem1 (blk2GV TD b1)) as mem1'; destruct mem1' as [mem1'|]; [|done].
    remember (free TD mem2 (blk2GV TD b2)) as mem2'; destruct mem2' as [mem2'|].
    + generalize Heqmem1'. intro X. unfold free in X. simpl in X.
    remember (Mem.bounds mem1 b1) as bounds1; destruct bounds1.
    exploit genericvalues_inject.mem_inj__free; eauto.
    intros [mem2'' [Hmem2'' [Hmwf Hminj]]].
    inv Hwf.
    erewrite mi_bounds in Heqbounds1; eauto.
    repeat rewrite Zplus_0_r in Hmem2''.
    generalize Heqmem2'. intro Y. unfold free in Y. simpl in Y.
    rewrite <- Heqbounds1 in Y. rewrite Hmem2'' in Y. inv Y.
    exploit (IHHaequiv mem1' mem2''); eauto.
    * intros. remember (Mem.bounds mem1' b) as bounds1'; destruct bounds1'.
    Local Transparent Mem.free.
    unfold Mem.free.
    destruct (Mem.range_perm_dec mem1' b z1 z2 Freeable); [done|].
    contradict n.
    eapply memory_props.MemProps.range_perm_mfree_1; eauto.
    split; [|done]. intro Heq; subst.
    by inv Hnd1.
    exploit Hf1; eauto.
    erewrite <- memory_props.MemProps.bounds_mfree; eauto.
    rewrite <- Heqbounds1'.
    unfold Mem.free.
    by destruct (Mem.range_perm_dec mem1 b z1 z2 Freeable).
    Local Opaque Mem.free.
    * intros. remember (Mem.bounds mem2'' b) as bounds2'; destruct bounds2'.
    Local Transparent Mem.free.
    unfold Mem.free.
    destruct (Mem.range_perm_dec mem2'' b z1 z2 Freeable); [done|].
    contradict n.
    eapply memory_props.MemProps.range_perm_mfree_1; eauto.
    eauto.
    split; [|done]. intro Heq; subst.
    by inv Hnd2.
    exploit Hf2; eauto.
    erewrite <- memory_props.MemProps.bounds_mfree; eauto.
    rewrite <- Heqbounds2'.
    unfold Mem.free.
    by destruct (Mem.range_perm_dec mem2 b z1 z2 Freeable).
    Local Opaque Mem.free.
    * by inv Hnd1.
    * by inv Hnd2.
    + unfold free in *. simpl in *.
    remember (Mem.bounds mem1 b1) as bounds1; destruct bounds1.
    exploit genericvalues_inject.mem_inj__free; eauto.
    intros [mem2' [Hmem2' [Hmwf Hminj]]].
    remember (Mem.bounds mem2 b2) as bounds2; destruct bounds2.
    inv Hwf.
    erewrite mi_bounds in Heqbounds1; eauto.
    rewrite <- Heqbounds1 in Heqbounds2. inv Heqbounds2.
    simpl in *.
    repeat rewrite Zplus_0_r in Hmem2'.
    rewrite Hmem2' in Heqmem2'. inv Heqmem2'.
  Qed.

  Ltac progress_tac :=
    repeat
      (try match goal with
         | [H: False |- _] => inv H
         | [H: ret _ = ret _ |- _] => inv H
         | [H: proj_sumbool (decs.align_dec ?a ?b) = true |- _] =>
            apply align_dec_r in H
         | [H:vgtac.is_true (_ && _) |- _] => apply andb_true_iff in H; destruct H
         | [H:_ && _ = true |- _] => apply andb_true_iff in H; destruct H
         | [H:_ /\ _ |- _] => destruct H
         | [H: _ @ _ |- _] => inv H
         | [H: exists _, _ |- _] => destruct H
         | [H: _ /\ _ |- _] => destruct H
         | [|- context[getOperandValueExt _ (vars_aux.add_ntag_value _) _ _ _]] =>
           rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new
         | [H: context[getOperandValueExt _ (vars_aux.add_ntag_value _) _ _ _] |- _] =>
           rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new in H
         | [H: ret_pop_cmd _ _ _ = ret_pop_cmd _ _ _ |- _] => inv H
         | [H: ret_pop_cmd _ _ _ = ret_pop_terminator |- _] => inv H
         | [H: ret_pop_terminator = ret_pop_cmd _ _ _ |- _] => inv H
         | [ec: ExecutionContext |- _] => destruct ec
         | [H: false = noop_idx_zero_exists ?n |- context[noop_idx_zero_exists ?n]] =>
           rewrite <- H
         | [|- context[getOperandValueExt _ (vars_aux.add_ntag_value _) _ _ _]] =>
           rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new
         | [Hn: false = noop_idx_zero_exists ?n,
            Hp: context[noop_idx_zero_exists ?n] |- _] =>
           rewrite <- Hn in Hp
         | [Hn: false = noop_idx_zero_exists ?n,
            Hp: pop_one nil ?n _ _ _ |- _] =>
           inv Hp; unfold pop_one_X in *
         | [Hn: false = noop_idx_zero_exists ?n,
            Hp: pop_one (_::_) ?n _ _ _ |- _] =>
           inv Hp; unfold pop_one_X in *
         | [H: match ?l with | nil => _ | _ :: _ => False end |- _] =>
           destruct l; [|done]
         | [H: match ?l with | nil => False | _ :: _ => _ end |- _] =>
           destruct l; [done|]
         | [H: match ?x with | ret _ => _ | merror => False end |- _] =>
           let y := fresh "y" in
           remember x as y; destruct y; [|done]
         | [H: match ?x with | ret _ => False | merror => _ end |- _] =>
           let y := fresh "y" in
           remember x as y; destruct y; [done|]
         | [H: ret_pop_cmd (ret _) _ _ = if ?c then ret_pop_cmd merror _ _ else _ |- _] =>
           let c' := fresh "c" in
           remember c as c'; destruct c'; [done|]
         | [H: ret_pop_terminator = if ?c then ret_pop_cmd _ _ _ else _ |- _] =>
           let c' := fresh "c" in
           remember c as c'; destruct c'; [done|]
         | [H: ret_pop_cmd _ _ _ =
           match ?l with
             | nil => ret_pop_terminator
             | _::_ => _
           end |- _] =>
           let l' := fresh "l" in
           remember l as l'; destruct l'; [done|]
         | [H: ret_pop_terminator =
           match ?l with
             | nil => _
             | _::_ => ret_pop_cmd _ _ _
           end |- _] =>
           let l' := fresh "l" in
           remember l as l'; destruct l'; [|done]
         | [H: match ?t with
                 | insn_return _ _ _ => _
                 | insn_return_void _ => _
                 | insn_br _ _ _ _ => _
                 | insn_br_uncond _ _ => _
                 | insn_unreachable _ => _
               end |- _] =>
           destruct t
         | [H:
           match ?c with
             | insn_bop _ _ _ _ _ => _
             | insn_fbop _ _ _ _ _ => _
             | insn_extractvalue _ _ _ _ _ => _
             | insn_insertvalue _ _ _ _ _ _ => _
             | insn_malloc _ _ _ _ => _
             | insn_free _ _ _ => _
             | insn_alloca _ _ _ _ => _
             | insn_load _ _ _ _ => _
             | insn_store _ _ _ _ _ => _
             | insn_gep _ _ _ _ _ _ => _
             | insn_trunc _ _ _ _ _ => _
             | insn_ext _ _ _ _ _ => _
             | insn_cast _ _ _ _ _ => _
             | insn_icmp _ _ _ _ _ => _
             | insn_fcmp _ _ _ _ _ => _
             | insn_select _ _ _ _ _ => _
             | insn_call _ _ _ _ _ _ _ => _
           end |- _] =>
           destruct c
         | [H:
           match ?c with
             | insn_bop _ _ _ _ _ => _
             | insn_fbop _ _ _ _ _ => _
             | insn_extractvalue _ _ _ _ _ => _
             | insn_insertvalue _ _ _ _ _ _ => _
             | insn_malloc _ _ _ _ => _
             | insn_free _ _ _ => _
             | insn_alloca _ _ _ _ => _
             | insn_load _ _ _ _ => _
             | insn_store _ _ _ _ _ => _
             | insn_gep _ _ _ _ _ _ => _
             | insn_trunc _ _ _ _ _ => _
             | insn_ext _ _ _ _ _ => _
             | insn_cast _ _ _ _ _ => _
             | insn_icmp _ _ _ _ _ => _
             | insn_fcmp _ _ _ _ _ => _
             | insn_select _ _ _ _ _ => _
             | insn_call _ _ _ _ _ _ _ => _
           end = true |- _] =>
           destruct c
         | [H: false = noop_idx_zero_exists ?n |- pop_one nil ?n _ _ _] =>
           by eapply pop_one_terminator; eauto; unfold pop_one_X; rewrite <- H

          | [H: ?a -> ?a |- _] => clear H
          | [H: genericvalues_inject.gv_inject _ nil nil |- _] => inv H
          | [H: genericvalues_inject.gv_inject _ nil (_::_) |- _] => inv H
          | [H: genericvalues_inject.gv_inject _ (_::_) nil |- _] =>
            inv H
          | [H: genericvalues_inject.gv_inject _ nil ?l |- _] =>
            inv H
          | [H: genericvalues_inject.gv_inject _ ?l nil |- _] =>
            inv H
          | [|- ret _ = ret _ -> _] =>
            let H := fresh "H" in intro H; inv H
          | [H: existT ?a (?b:nat) ?c = existT ?a ?b ?d |- _] =>
            apply Eqdep_dec.inj_pair2_eq_dec in H; [|decide equality]             
       end; simpl; eauto; unfold pop_one_X in *).

  Ltac progress_tac_agr :=
    repeat
      (try match goal with
             | [H: ?a = ?a |- _] => clear H
             | [H: context[if noop_idx_zero_exists ?n then _ else _] |- _] =>
               let nn := fresh "nn" in
                 remember (noop_idx_zero_exists n) as nn; destruct nn
             | [|- context[eq_nat_dec ?a ?b]] =>
               destruct (eq_nat_dec a b); try done
             | [|- context[if zlt ?a ?b then _ else _]] =>
               destruct (zlt a b); try done
             | [|- context[if zeq ?a ?b then _ else _]] =>
               destruct (zeq a b); try done
             | [H: ret _ = invariant_proceed _ _ _ _ _ |- _] =>
               exploit invariant_proceed_heap_eq_check; eauto;
                 intro; symmetry in H
             | [H: vgtac.is_true (heap_eq_check _ _ _ _ _ (ret ?c) _) |- _] =>
               destruct c; inv H
             | [H: vgtac.is_true (heap_eq_check _ _ _ _ _ ?oc _) |- _] =>
               destruct oc; inv H
             | [H: vgtac.is_true (terminator_args_eq_check ?t _ _) |- _] =>
               destruct t; inv H
           end; progress_tac; destruct_and).

  Lemma insert_if :
    forall A B C (f:A->B->C) (a1:A) (c:bool) (a21 a22:B),
      (if c then f a1 a21 else f a1 a22) = f a1 (if c then a21 else a22).
  Proof.
    by destruct c.
  Qed.
  Ltac to_right :=
    match goal with
      | [H: ?a = ?b |- context[match ?a with | ret _ => _ | merror => _ end]] =>
        rewrite H
      | [H: ?a = ?b |- context[if ?a then _ else _]] =>
        rewrite H
      | [|- context[if ?c then ?f ?a ?b1 else ?f ?a ?b2]] => rewrite insert_if
    end.
  Ltac to_left :=
    match goal with
      | [H: ?b = ?a |- context[match ?a with | ret _ => _ | merror => _ end]] =>
        rewrite <- H
      | [H: ?b = ?a |- context[if ?a then _ else _]] =>
        rewrite <- H
    end.
  Ltac to_ss :=
    match goal with
      | [H: genericvalues_inject.gv_inject _ ?g _ |- context[isGVZero _ ?g]] =>
        erewrite genericvalues_inject.simulation__isGVZero; [|by eauto]
    end.
  Ltac to_split :=
    match goal with
      | [|- vgtac.is_true (_ && _)] => apply andb_true_iff; split
      | [|- is_true (_ && _)] => apply andb_true_iff; split
      | [|- _ && _ = true] => apply andb_true_iff; split
    end.
  Lemma cfg_fold :
    forall cfg,
      mkCfg (CurSystem cfg) (CurTargetData cfg) (CurProducts cfg) (Globals cfg) (FunTable cfg) = cfg.
  Proof. by destruct cfg. Qed.
  Ltac clean :=
    repeat
      (try match goal with
             | [H: ?a = ?a |- _] => clear H
             | [|- (exists _, _) -> _] => intro
             | [H: exists _, _ |- _] => destruct H
             | [H: _ /\ _ |- _] => destruct H
             | [H: _ @ _ |- _] => inv H
             | [H: _::_ = _::_ |- _] => inv H
             | [H: context[mkCfg (CurSystem ?cfg) (CurTargetData ?cfg) (CurProducts ?cfg) (Globals ?cfg) (FunTable ?cfg)] |- _] => rewrite cfg_fold in H
             | [|- context[mkCfg (CurSystem ?cfg) (CurTargetData ?cfg) (CurProducts ?cfg) (Globals ?cfg) (FunTable ?cfg)]] => rewrite cfg_fold
           end; subst).

  Ltac exploit_eq_check_value :=
    match goal with
      | [H: eq_check_value _ _ _ _ _ = true |- _] =>
        let gvs := fresh "gvs" in
          let Hgvs := fresh "Hgvs" in
            let Hinj := fresh "Hinj" in
              exploit eq_check_value_prop_2; eauto; clear H
    end.

  Ltac exploit_eq_check_params :=
    match goal with
      | [H: eq_check_params _ _ _ _ _ = true |- _] =>
        let gvs := fresh "gvs" in
          let Hgvs := fresh "Hgvs" in
            let Hinj := fresh "Hinj" in
              exploit eq_check_params_prop_2; eauto; clear H
    end.

  Lemma lookupFdefViaIDFromProducts_ideq products id fd
    (H: lookupFdefViaIDFromProducts products id = ret fd) :
    getFdefID fd = id.
  Proof.
    destruct fd. destruct fheader5. simpl in *.
    by exploit lookupFdefViaIDFromProducts_ideq; eauto.
  Qed.

  Lemma hint_sem_F_step_hint_sem
    pbid alpha li1 li2
    ecs1 mem1 ns1
    ecs2 mem2 ns2
    (Hsem: hint_sem pbid alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2) :
    F_step hint_sem pbid alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2.
  Proof.
    inv Hsem. repeat intro.
    remember
    (if noop_idx_zero_exists n2
     then false
     else match cmds2 with
            | nil => true
            | _::_ => false
          end) as Hterm2; destruct Hterm2.
    (* unreachable/return/branch *)
    remember (noop_idx_zero_exists n2) as nn2; destruct nn2; [done|].
    destruct cmds2; [|done].
    exploit Hvalid_term; eauto.
    { unfold pop_one_X.
      by destruct (noop_idx_zero_exists n2); [done|].
    }
    intros [Hpop1 [Himpl Hterm]].
    simpl. unfold pop_one_X in Hpop1.
    remember (noop_idx_zero_exists n1) as nn1; destruct nn1; [done|].
    destruct cmds1; [|done]. admit. admit. (*

    exploit (logical_semantic_step_term_na_merror cfg1); eauto.
    { by unfold pop_one_X; rewrite <- Heqnn1. }
    exploit (logical_semantic_step_term_tr_E0 cfg1); eauto.
    { by unfold pop_one_X; rewrite <- Heqnn1. }
    intros; subst.
    
    remember (term' term2) as Hterm2; destruct Hterm2.

    (* unreachable *)
    destruct term2; simpl in HeqHterm2; try done.
    inv Hstep1. inv Hec. inv Hpn. simpl in *.
    inv Hpop; [by unfold pop_one_X in Hpop0; rewrite <- Heqnn1 in Hpop0|].
    by inv Hstep.

    (* return *)
    right. right.
    destruct term2; inv HeqHterm0; destruct term1; inv Hterm; destruct_and.
    { (* return value *)
      exploit invariant_implies_preserves_hint_sem_fdef; eauto.
      intro Hinsn'. inv Hinsn'. simpl in *.
      destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
      inv Hstep1. inv Hec. inv Hpn.
      simpl in Hpop. inv Hpop; [by unfold pop_one_X in Hpop0; rewrite <- Heqnn1 in Hpop0|].
      inv Hstep.
      unfold returnUpdateLocals in H15.
      remember (getOperandValue TD value0 locals1 gl) as gc; destruct gc; [|done].
       exploit eq_check_value_prop_2; eauto.
      + by inv Hvmem; eauto.
      + simpl in *.
        rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new.
        by rewrite <- Heqgc.
      + intros [gvs2 [Hgvs2 Hinj]].
        eapply match_return_value; eauto.
        * by rewrite <- Heqnn1.
        * by rewrite <- Heqnn2.
        * by inv H4.
        * by rewrite <- hint_sem_aux.getOperandValue_equals_getOperandValueExt_new in Hgvs2.
    }
    { (* return void *)
      eapply match_return_void; eauto.
      + by rewrite <- Heqnn1.
      + by rewrite <- Heqnn2.
    }

    (* branch *)
    left. splits.
    { apply is_ordinary_cmd; auto.
      destruct term2; inv HeqHterm0; destruct term1; inv Hterm.
      by intros [_ ?].
      by intros [_ ?].
    }
    { apply is_ordinary_cmd; auto.
      destruct term2; inv HeqHterm0.
      by intros [_ ?].
      by intros [_ ?].
    }
    intros. destruct ecs2'; [by inv Hstep; destruct pst; inv Hstep0; inv H|].
    destruct e. destruct CurBB0.
    assert (Hedge: valid_edge bid l0).
    { inv Hstep. inv Hec. inv Hpn.
      inv Hpop; [by unfold pop_one_X in Hpop0; rewrite <- Heqnn2 in Hpop0|].
      inv Hctx. simpl in *.
      destruct term2; simpl in HeqHterm2; try done.
      + (* conditional branch *)
        inv Hstep0. subst.
        destruct (isGVZero TD c).
        * econstructor; eauto; subst; eauto.
          by right; left.
        * econstructor; eauto; subst; eauto.
          by left.
      + inv Hstep0. subst.
        econstructor; eauto; subst; eauto.
        by left.
    }

    exploit (Hvalid_edge bid l0); eauto.
    intros [nphis1 [ncmds1 [nterm1 [nphis2 [ncmds2 [nterm2 [Hnstmts1 [Hnstmts2 [nblock_hint [nhint [Hnblock_hint [Hnhint Himpl2]]]]]]]]]]]].

    exploit (Hvalid_phi bid l0); eauto.
    intros [hint' [hints'' [hint'' [Hhint' [Hhints'' [Hhint'' Himpl']]]]]].

    exploit (invariant_implies_preserves_hint_sem_fdef hint); eauto.
    clear Hinsn. intro Hinsn.

    assert (tr = E0); [|subst].
    { generalize Hstep. intro Hstep'.
      inv Hstep'. inv Hpn. inv Hec. simpl in *.
      inv Hpop; [by inv Hpop0; unfold pop_one_X in H0; rewrite <- Heqnn2 in H0|].
      by inv Hstep0.
    }

    exploit (logical_semantic_step_branch_inv cfg2); eauto; progress_tac; clean.

    assert (term'_branch = term' term1).
    { by destruct term1, term2. }
    exploit (logical_semantic_step_branch_inv cfg1); eauto; progress_tac; clean.

    inv H0. subst CurFunction0.

    generalize Hstep1. intro Hstep'. inv Hstep'. inv Hpn. inv Hec. simpl in *.
    inv Hpop; unfold pop_one_X in *; rewrite <- Heqnn1 in Hpop0; try done.
    inv Hnoop; [by inv Hnnn|]. clean.
    inv Hnnn; [simpl in Hret; destruct Hret as [_ Hret]; by destruct term1, term2|].
    rename Hbrc into Hbrc1. generalize Hbrc1. intro Hbrc'.
    destruct Hbrc' as [_ Hbrc1']. simpl in *.
    generalize Hstep. intro Hstep'. inv Hstep'. inv Hpn. inv Hec. simpl in *.
    inv Hpop; unfold pop_one_X in *; rewrite <- Heqnn2 in Hpop0; try done.
    inv Hnoop; [by inv Hnnn|]. clean.
    inv Hnnn; [simpl in Hret; destruct Hret as [_ Hret]; by destruct term2|].
    rename Hbrc into Hbrc2. generalize Hbrc2. intro Hbrc'.
    destruct Hbrc' as [_ Hbrc2']. simpl in *.
    inv H4. rewrite H3 in *.

    assert (Heq : l0 = x4 /\ l0 = bid0 /\ l0 = bid1); [|destruct Heq as [? [? ?]]; repeat subst].
    { destruct term1, term2; inv Hterm; try done.
      + infrule_tac.
        destruct Hbrc1' as [cond1 [c1 [Hcond1 [Hc1 Hbid1]]]].
        destruct Hbrc2' as [cond2 [c2 [Hcond2 [Hc2 Hbid2]]]].
        rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0.
        rewrite (destruct_cfg cfg2) in Hstep2. inv Hstep2.
        inv Hc1. inv Hc2. inv H32. inv H38.
        rewrite getOperandValue_compat in *.
        rewrite Hcond1 in H12. inv H12.
        rewrite Hcond2 in H13. inv H13.
        inv Hinsn. simpl in *. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
        exploit eq_check_value_prop. eauto. eauto. eauto. eauto. by inv Hvmem. eauto.
        rewrite <- getOperandValue_equals_getOperandValueExt_new. eauto.
        rewrite <- getOperandValue_equals_getOperandValueExt_new. eauto.
        intro Hinj. 
        exploit genericvalues_inject.simulation__isGVZero. eauto.
        instantiate (1 := CurTargetData cfg1). rewrite Htd. intro Hz.
        rewrite Htd, Hz in *.
        by destruct (isGVZero (CurTargetData cfg2) c0); subst.
      + infrule_tac.
        rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0.
        rewrite (destruct_cfg cfg2) in Hstep2. inv Hstep2.
        done.
    }

    rewrite <- Hnstmts1 in H2. inv H2.
    rewrite <- Hnstmts2 in H. inv H.
        
    eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists.
    split; [by eauto|].
    split; [by apply inject_incr'_refl|].
    econs; eauto.
    { by inv Hctx. }
    { by eapply logical_step_preservation; eauto. }
    { by eapply logical_step_preservation; eauto. }
    { unfold get_noop_by_fid_bb in *.
      inv Hfid. rewrite Hfid2.
      by apply Hhint''.
    }
    { eapply invariant_implies_preserves_hint_sem_fdef; eauto.
      eapply infrules_resolve_preserves_hint_sem_fdef; eauto; [by apply infrules_correct|].
      eapply invariant_proceed_preserves_hint_sem_fdef_branch; eauto.
      + destruct term1; inv H1; inv Hstep0; simpl in *.
        * rewrite H7. inv H22. by rewrite <- H23.
        * by rewrite <- Hnstmts1.
      + destruct term2; inv HeqHterm0; inv Hstep2; simpl in *.
        * rewrite H8. inv H23. by rewrite <- H24.
        * by rewrite <- Hnstmts2.
      + simpl. unfold pop_one_X. by rewrite <- Heqnn1.
      + simpl. unfold pop_one_X. by rewrite <- Heqnn2.
      + split; [done|]. simpl in *. apply H5.
    }

    (* nop/cmd/call *)
    exploit Hvalid_cmd; eauto.
    { unfold pop_one_X.
      instantiate (1 :=
        if noop_idx_zero_exists n2
          then (noop_idx_zero_remove n2)
          else (noop_idx_decrease n2)).
      instantiate (1 :=
        if noop_idx_zero_exists n2
          then cmds2
          else match cmds2 with
                 | nil => nil
                 | _::cs => cs
               end).
      instantiate
        (1 :=
          if noop_idx_zero_exists n2
            then merror
            else match cmds2 with
                   | c::_ => ret c
                   | _ => merror
                 end).
      unfold pop_one_X.
      destruct (noop_idx_zero_exists n2); [done|].
      by destruct cmds2.
    }
    intros [cmd_opt1 [cur1' [n1' [hint' [hint'' [Hpop [Hhint' [Hlookup Himpl]]]]]]]].
    remember
    (cmd' (if noop_idx_zero_exists n2
            then merror
            else match cmds2 with
                 | nil => merror
                 | c :: _ => ret c
                 end)) as Hiscall; destruct Hiscall.

    (* nop/cmd *)
    left.
    splits.
    { remember (stutter_num n1) as st1. destruct st1; [|by econs; eauto].
      exploit stutter_num_noop_idx_zero_exists'; eauto. intro Hn1.
      unfold pop_one_X in Hpop. rewrite Hn1 in *.
      destruct cmds1; [done|]. inv Hpop.
      destruct c; try by eapply is_ordinary_cmd; simpl in *; auto; intros [? _].
      exploit invariant_proceed_heap_eq_check; eauto. intro Hheap.
      remember (stutter_num n2) as st2. destruct st2.
      + exploit stutter_num_noop_idx_zero_exists'; eauto. intro Hn2. rewrite Hn2 in *.
        destruct cmds2; [done|].
        destruct c; inv Hheap; inv HeqHiscall.
      + exploit stutter_num_noop_idx_zero_exists; eauto. intro Hn2. rewrite Hn2 in *.
        inv Hheap.
    }
    { remember (stutter_num n2) as st. destruct st; [|by econs; eauto].
      exploit stutter_num_noop_idx_zero_exists'; eauto. intro Hn2. rewrite Hn2 in *.
      destruct cmds2; [done|].
      apply is_ordinary_cmd.
      + intros id Hid; destruct c; inv HeqHiscall; inv Hid.
      + intros id Hid; destruct c; inv HeqHiscall; inv Hid.
      + by intros [? ?]; destruct c; inv HeqHiscall.
    }
    intros.
    edestruct invariant_proceed_preserves_hint_sem_insn_normal; simpl; eauto; simpl.
    { by inv Hmatch. }
    { by inv Hmatch. }
    { by rewrite <- Hpop. }
    { unfold pop_one_X.
      destruct (noop_idx_zero_exists n2); [done|].
      by destruct cmds2.
    }
    { destruct (noop_idx_zero_exists n2); [done|].
      destruct cmds2 as [|cmd2 cmds2]; [done|].
      by destruct cmd2.
    }
    clear Hstep1 tr1.
    destruct H0 as [Hncall [alpha' [li1' [li2' [Hinj HH]]]]].
    eexists pbid. exists alpha'. exists li1'. eexists. eexists. eexists. eexists. eexists.
    repeat (split; [by eauto|]).
    exploit (logical_semantic_step_cmd_inv cfg1); eauto; progress_tac; clean.
    exploit (logical_semantic_step_cmd_inv cfg2).
    { by eauto. }
    { instantiate (3 := if noop_idx_zero_exists n2 then _ else _).
      instantiate (2 := if noop_idx_zero_exists n2 then _ else _).
      instantiate (1 := if noop_idx_zero_exists n2 then _ else _).
      unfold pop_one_X.
      remember (noop_idx_zero_exists n2) as nn2; destruct nn2; eauto.
      instantiate (3 := match cmds2 with nil => _ | _::_ => _ end).
      instantiate (2 := match cmds2 with nil => _ | _::_ => _ end).
      instantiate (1 := match cmds2 with nil => _ | _::_ => _ end).
      instantiate (2 := nil).
      instantiate (3 := nil).
      instantiate (4 := merror).
      by destruct cmds2.
    }
    { destruct (noop_idx_zero_exists n2); [done|].
      destruct cmds2; [done|].
      generalize dependent HeqHiscall.
      by destruct c; unfold cmd'.
    }
    progress_tac. clean.

    exploit infrules_resolve_preserves_hint_sem_fdef; eauto; [by apply infrules_correct|].
    clear Hinsn. intro Hinsn.
    exploit invariant_implies_preserves_hint_sem_fdef; eauto.
    clear Hinsn. intro Hinsn.
    econstructor; eauto.
    { by inv Hctx. }
    { by eapply logical_step_preservation; eauto. }
    { by eapply logical_step_preservation; eauto. }
    { eapply inject_incr__preserves__ftable_simulation; eauto.
      by inv Hinj.
    }
    { remember (noop_idx_zero_exists n2) as nn2; destruct nn2; eauto.
      by destruct cmds2.
    }

    (* call/excall *)
    right. left.
    remember (noop_idx_zero_exists n2) as nn2; destruct nn2; [done|].
    destruct cmds2; [done|].
    destruct c; inv HeqHiscall.
    exploit invariant_proceed_heap_eq_check; eauto. intro Hchk.
    destruct cmd_opt1 as [[]|]; inv Hchk. destruct_and.

    progress_tac.

    generalize Hstep1. intro Hstep'. inv Hstep'. inv Hec. inv Hpn.
    inv Hpop; unfold pop_one_X in *; rewrite <- Heqc in Hpop0; try done.
    inv Hnoop; [|inv Hnnn; [by inv Hret|by destruct cfg1; inv Hbrc]].
    simpl in *. inv Hpop0.

    generalize Hstep. intro Hstep'.
    rewrite (destruct_cfg cfg1) in Hstep'. inv Hstep'; simpl in *; clean.
    (* call *)
    generalize Hinsn. intro Hinsn'. inv Hinsn'. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
    exploit_eq_check_value; eauto; progress_tac; clean.
    { by inv Hvmem. }
    exploit_eq_check_params; eauto; progress_tac; clean.
    { by inv Hvmem. }
    destruct lb; inv H31.
    econstructor; eauto; progress_tac; simpl in *.
    { eapply is_same_call_call; eauto.
      + rewrite (destruct_cfg cfg1). simpl.
        eexists. eexists. eexists.
        by split; eauto.
      + rewrite (destruct_cfg cfg2). simpl in *.
        generalize dependent H30. unfold lookupFdefViaPtr. erewrite Hftable; eauto.
        exists x. exists x.
        remember (lookupFdefViaGVFromFunTable (FunTable cfg2) x) as fd. destruct fd; [|done]. simpl in *.
        edestruct Hvalid_products1_1; eauto.
        exists x1.
        repeat (split; [by eauto|]).
        exploit lookupFdefViaIDFromProducts_ideq. symmetry. eauto. intro. subst.
        exploit lookupFdefViaIDFromProducts_ideq; eauto.
    }
    { destruct (noret_dec noret0 noret5); [subst|done].
      intros. destruct noret5.
      + destruct Hnoret as [? ?]. subst.
        econstructor; eauto.
        * by inv Hctx.
        * eapply inject_incr__preserves__ftable_simulation; eauto.
          by inv Hincr.
        * eapply invariant_implies_preserves_hint_sem_fdef; eauto.
          eapply infrules_resolve_preserves_hint_sem_fdef; eauto; [by apply infrules_correct|].
          exploit invariant_proceed_preserves_hint_sem_insn_call'; simpl; eauto; simpl.
            by unfold pop_one_X; rewrite <- Heqc; eauto.
            by unfold pop_one_X; rewrite <- Heqnn2; eauto.
            by inv Hvmem.
            intro HH. apply HH; auto.
              intro Hrd1. apply Heqm1. by econs.
              intro Hrd2. apply Heqm2. by econs.
      + destruct Hnoret as [rv1 [rv2 [Hrv [? ?]]]]. subst.
        econstructor; eauto.
        * by inv Hctx.
        * eapply inject_incr__preserves__ftable_simulation; eauto.
          by inv Hincr.
        * eapply invariant_implies_preserves_hint_sem_fdef; eauto.
          eapply infrules_resolve_preserves_hint_sem_fdef; eauto; [by apply infrules_correct|].
          exploit invariant_proceed_preserves_hint_sem_insn_call; simpl; eauto; simpl.
            by unfold pop_one_X; rewrite <- Heqc; eauto.
            by unfold pop_one_X; rewrite <- Heqnn2; eauto.
            intros HH. apply HH; auto. by inv Hvmem.
              intro Hrd1. apply Heqm1. by econs.
              intro Hrd2. apply Heqm2. by econs.
    }

    (* excall *)
    generalize Hinsn. intro Hinsn'. inv Hinsn'. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
    exploit_eq_check_value; eauto; progress_tac; clean.
    { by inv Hvmem. }
    exploit_eq_check_params; eauto; progress_tac; clean.
    { by inv Hvmem. }
    econstructor; eauto; progress_tac.
    { eapply is_same_call_excall; eauto.
      + rewrite (destruct_cfg cfg1). simpl.
        eexists. eexists.
        by split; eauto.
      + rewrite (destruct_cfg cfg2). simpl in *.
        generalize dependent H30. unfold lookupExFdecViaPtr. erewrite Hftable; eauto.
        exists x. exists x. 
        remember (lookupFdefViaGVFromFunTable (FunTable cfg2) x) as fd; destruct fd; [|done]. simpl in *.
        repeat (split; [by auto|]).
        remember (lookupFdefViaIDFromProducts (CurProducts cfg2) i0) as gvf2; destruct gvf2 as [gvf2|].
        * edestruct Hvalid_products1_2; eauto.
          by rewrite <- H7 in H30.
        * destruct (lookupFdefViaIDFromProducts (CurProducts cfg1) i0); [done|].
          by rewrite <- Hvalid_products2, H30.
    }
    { destruct (noret_dec noret0 noret5); [subst|done].
      intros. destruct noret5.
      + destruct Hnoret as [? ?]. subst.
        econstructor; eauto.
        * by inv Hctx.
        * eapply inject_incr__preserves__ftable_simulation; eauto.
          by inv Hincr.
        * eapply invariant_implies_preserves_hint_sem_fdef; eauto.
          eapply infrules_resolve_preserves_hint_sem_fdef; eauto; [by apply infrules_correct|].
          exploit invariant_proceed_preserves_hint_sem_insn_call'; simpl; eauto; simpl.
            by unfold pop_one_X; rewrite <- Heqc; eauto.
            by unfold pop_one_X; rewrite <- Heqnn2; eauto.
            by inv Hvmem.
            intros HH. apply HH; auto.
              intro Hrd1. apply Heqm1. by econs.
              intro Hrd2. apply Heqm2. by econs.
      + destruct Hnoret as [rv1 [rv2 [Hrv [? ?]]]]. subst.
        econstructor; eauto.
        * by inv Hctx.
        * eapply inject_incr__preserves__ftable_simulation; eauto.
          by inv Hincr.
        * eapply invariant_implies_preserves_hint_sem_fdef; eauto.
          eapply infrules_resolve_preserves_hint_sem_fdef; eauto; [by apply infrules_correct|].
          exploit invariant_proceed_preserves_hint_sem_insn_call; simpl; eauto; simpl.
            by unfold pop_one_X; rewrite <- Heqc; eauto.
            by unfold pop_one_X; rewrite <- Heqnn2; eauto.
            intros HH. apply HH; auto. by inv Hvmem. 
              intro Hrd1. apply Heqm1. by econs.
              intro Hrd2. apply Heqm2. by econs.
    } *)
  Qed.

  Lemma hint_sem_F_progress_hint_sem
    pbid alpha li1 li2
    ecs1 mem1 ns1
    ecs2 mem2 ns2
    (Hsem: hint_sem pbid alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2) :
    F_progress ecs1 mem1 ns1 ecs2 mem2 ns2.
  Proof.
    inv Hsem. repeat intro.
    inv Hstep1. inv Hec. inv Hpn. simpl in *.
    remember (noop_idx_zero_exists n2) as nn2; destruct nn2.    
    { (* nop *) admit. (*
      eexists. eexists. eexists. eexists. eexists.
      econstructor; simpl; eauto; simpl.
      + eapply pop_one_cmd; eauto.
        by unfold pop_one_X; rewrite <- Heqnn2.
      + by repeat constructor.
      + by simpl; split; eauto. *)
    }

    exploit @OpsemPP.progress; eauto.
    intro Hprog; destruct Hprog as [Hprog|[Hprog|Hprog]].
    (* is final state *)
    exfalso.
    unfold s_isFinialState in Hprog.
    destruct cmds2; [|done].
    destruct term2; try done.
    { (* return value *)
      destruct pecs2; [|done].
      exploit Hvalid_term; eauto.
      + by unfold pop_one_X; rewrite <- Heqnn2.
      + intros [Hpop1 [Himpl Hargs]].
        destruct term1; auto.
        inv Hpop; rewrite Hpop0 in Hpop1; inv Hpop1.
        unfold pop_one_X in Hpop0.
        remember (noop_idx_zero_exists hpn) as nhpn; destruct nhpn; [done|].
        destruct cmds1; [|done]. admit. (*
        inv Hstep.
        by inv Hpecs. *)
    }
    { (* return void *)
      destruct pecs2; [|done].
      exploit Hvalid_term; eauto.
      + by unfold pop_one_X; rewrite <- Heqnn2.
      + intros [Hpop1 [Himpl Hargs]].
        destruct term1; auto.
        inv Hpop; rewrite Hpop0 in Hpop1; inv Hpop1.
        unfold pop_one_X in Hpop0.
        destruct (noop_idx_zero_exists hpn); [done|].
        destruct cmds1; [|done]. admit. (*
        inv Hstep.
        by inv Hpecs. *)
    }

    (* progress *)
    destruct Hprog as [st2' [tr2 Hsem]].
    destruct cmds2 as [|c cmds2].
    { (* progress, term *)
      destruct st2'.
      inv Hsem; progress_tac.
      { admit. (* eexists; eexists; eexists; eexists; eexists;
          econstructor; progress_tac. 
        * instantiate (2 := nil).
          eapply logical_semantic_step_noop_stk_term; eauto.
          by apply logical_semantic_step_noop_terminator_ret.
        * by constructor; eauto. *)
      }
      { admit. (* eexists; eexists; eexists; eexists; eexists;
          econstructor; progress_tac.
        * instantiate (2 := nil).
          eapply logical_semantic_step_noop_stk_term; eauto.
          by apply logical_semantic_step_noop_terminator_ret. *)
      }
      remember (isGVZero TD c) as cond; destruct cond.
      + admit. (* exploit @sBranch; eauto.
        { eauto. }
        { by rewrite <- Heqcond; eauto. }
        intro Hinsn'.
        eexists; eexists; eexists; eexists; eexists;
          econstructor; progress_tac.
        instantiate (2 := nil).
        eapply logical_semantic_step_noop_stk_term; eauto.
        eapply logical_semantic_step_noop_terminator_brc; eauto.
        constructor; simpl; auto.
        exists c. exists c. repeat split; auto.
        by rewrite <- Heqcond. *)
      + admit. (* exploit @sBranch; eauto.
        { eauto. }
        { by rewrite <- Heqcond; eauto. }
        intro Hinsn'.
        eexists; eexists; eexists; eexists; eexists;
          econstructor; progress_tac.
        instantiate (2 := nil).
        eapply logical_semantic_step_noop_stk_term; eauto.
        eapply logical_semantic_step_noop_terminator_brc; eauto.
        constructor; simpl; auto.
        exists c. exists c. repeat split; progress_tac.
        by rewrite <- Heqcond. *)
      + admit. (*eexists; eexists; eexists; eexists; eexists;
          econstructor; progress_tac.
        * instantiate (2 := nil).
          eapply logical_semantic_step_noop_stk_term; eauto.
          eapply logical_semantic_step_noop_terminator_brc; eauto.
          constructor; simpl; auto.
        * by constructor; eauto. *)
    }
    { (* progress, cmd *)
      destruct st2'.
      remember
      (match c with
         | insn_call _ _ _ _ _ _ _ => true
         | _ => false
       end) as iscall; destruct iscall.
      + destruct c; try done. admit. (*
        inv Hsem.
        * eexists. eexists. eexists. eexists. eexists.
          econstructor; simpl; eauto; simpl.
            eapply pop_one_cmd; eauto.
            by unfold pop_one_X; rewrite <- Heqnn2.

            apply logical_semantic_step_noop_stk_cmd; auto.
            eapply logical_semantic_step_noop_cmd_call; eauto.
            eexists. eexists. eexists. simpl. inv H19.
            by repeat split; eauto.

            simpl. generalize dependent H20. clear.
            unfold lookupFdefViaPtr.
            destruct (lookupFdefViaGVFromFunTable fs fptr); [|done].
            simpl. intro H.
            assert (i0 = fid0); [|by subst].
            generalize dependent H. induction Ps; [done|].
            simpl.
            remember (lookupFdefViaIDFromProduct a i0) as t; destruct t as [t|].
              intro H. inv H.
              destruct a; inv Heqt.
              destruct (getFdefID fdef5 == i0); [|done].
              by inv H0.
            intro H.
            by exploit IHPs; eauto.

          by econstructor; eauto.

        * eexists. eexists. eexists. eexists. eexists.
          econstructor; simpl; eauto; simpl.
            eapply pop_one_cmd; eauto.
            by unfold pop_one_X; rewrite <- Heqnn2.

            apply logical_semantic_step_noop_stk_cmd; auto.
            eapply logical_semantic_step_noop_cmd_excall; eauto.
            eexists. eexists. eexists. inv H19.
            split; [by eauto|].
            split; [done|].
            by apply H20.

            simpl.
            by eapply sExCall; eauto.
      + eexists. eexists. eexists. eexists. eexists.
        econstructor; simpl; eauto; simpl.
        * eapply pop_one_cmd; eauto.
          by unfold pop_one_X; rewrite <- Heqnn2.
        * apply logical_semantic_step_noop_stk_cmd; auto.
          eapply logical_semantic_step_noop_cmd_cmd; eauto.
          by destruct c.
        * by simpl; eauto. *)
      + admit.
     
    }

    (* undefined state *)
    exfalso.
    destruct cfg2; simpl in Hprog.

    Ltac exploit_cmd :=
      exploit Hvalid_cmd; eauto; repeat (progress_tac; intros).

    Ltac exploit_term :=
      exploit Hvalid_term; eauto; repeat (progress_tac; intros).
      
    destruct Hprog as [Hprog|[Hprog|[Hprog|[Hprog|[Hprog|[Hprog|Hprog]]]]]]; progress_tac.
    - exploit_term.
      exploit invariant_implies_preserves_hint_sem_fdef; eauto.
      clear Hinsn. intro Hinsn. inv Hinsn.
      destruct Hsem as [olc1 [olc2 [Hmd Hinv]]]. simpl in *.
      progress_tac_agr. admit. (*
      inv Hstep.
      unfold returnUpdateLocals in H17. simpl in *.
      remember (getOperandValue TD value0 locals1 gl) as gv0; destruct gv0 as [gv0|]; [|done].
      exploit_eq_check_value; progress_tac.
      { by inv Hvmem. }
      intros [gvs2 [Hgvs2 Hinj2]].
      destruct c'; inv H17.
      generalize dependent Hprog.
      assert (free_allocas TD mem1 allocas1 <> merror); [by rewrite H16|].
      clear -H1 Hvmem Hvals Haequiv.
      
      assert (Hf1: forall b,
        (forall (Hli1: In b li1) (Hallocas1: In b allocas1),
          let (l, h) := Mem.bounds mem1 b in Mem.free mem1 b l h <> merror)).
      { intros. inv Hvmem.
        by apply Hli1free.
      }
      assert (Hf2: forall b,
        (forall (Hli2: In b li2) (Hallocas1: In b allocas2),
          let (l, h) := Mem.bounds mem2 b in Mem.free mem2 b l h <> merror)).
      { intros. inv Hvmem.
        by apply Hli2free.
      }
      assert (Hnd1: NoDup allocas1); [by unfold valid_allocas in *; destruct_and|].
      assert (Hnd2: NoDup allocas2); [by unfold valid_allocas in *; destruct_and|].
      generalize dependent H1.
      generalize dependent Hnd2.
      generalize dependent Hnd1.
      generalize dependent Hf2.
      generalize dependent Hf1.
      inv Hvmem.
      generalize dependent Hli1none.
      generalize dependent Hli2none.
      generalize dependent Hmemi.
      generalize dependent Hwf.
      clear -Haequiv.
      generalize dependent mem2.
      generalize dependent mem1.
      by apply free_allocas_progress. *)
    - exploit_term.
      exploit invariant_implies_preserves_hint_sem_fdef; eauto.
      clear Hinsn. intro Hinsn. inv Hinsn.
      destruct Hsem as [olc1 [olc2 [Hmd Hinv]]]. simpl in *.
      progress_tac_agr. admit. (*
      inv Hstep. simpl in *.
      destruct Hprog.
      + assert (free_allocas TD mem1 allocas1 <> merror); [by rewrite H12|].
        clear -H1 H Hvmem Hvals Haequiv.
        assert (Hf1: forall b,
          (forall (Hli1: In b li1) (Hallocas1: In b allocas1),
            let (l, h) := Mem.bounds mem1 b in Mem.free mem1 b l h <> merror)).
        { intros. inv Hvmem.
          by apply Hli1free.
        }
        assert (Hf2: forall b,
          (forall (Hli2: In b li2) (Hallocas1: In b allocas2),
            let (l, h) := Mem.bounds mem2 b in Mem.free mem2 b l h <> merror)).
        { intros. inv Hvmem.
          by apply Hli2free.
        }
        assert (Hnd1: NoDup allocas1); [by unfold valid_allocas in *; destruct_and|].
        assert (Hnd2: NoDup allocas2); [by unfold valid_allocas in *; destruct_and|].
        generalize dependent H.
        generalize dependent H1.
        generalize dependent Hnd2.
        generalize dependent Hnd1.
        generalize dependent Hf2.
        generalize dependent Hf1.
        inv Hvmem.
        generalize dependent Hli1none.
        generalize dependent Hli2none.
        generalize dependent Hmemi.
        generalize dependent Hwf.
        clear -Haequiv.
        generalize dependent mem2.
        generalize dependent mem1.
        by apply free_allocas_progress.
      + destruct c; simpl in H; try by inv H.
        destruct noret5; [done|].
        inv Hpecs. simpl in *.
        progress_tac.
        by infrule_tac. *)
    - exploit_term. admit.
      (* by inv Hstep. *)
    - exploit_cmd. progress_tac_agr. infrule_tac. admit. (*
      inv Hstep.
      inv Hinsn. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
      exploit_eq_check_value; eauto; progress_tac.
      { by inv Hvmem. }
      intros [gvs2 [Hgvs2 Hinj]].
      rewrite Hgvs2 in Heqy. inv Heqy.
      
      unfold free.
      destruct mptr0 as [|[]], gvs2 as [|[]]; simpl in *; inv Hinj; try by intros.
      destruct v; try by intros.
      destruct mptr0; [|by intros].
      progress_tac_agr.
      destruct v0; inv H5.
      progress_tac_agr.
      inv Hvmem.
      exploit free_inv; eauto.
      intros [blk1 [ofs1 [hi1 [lo1 [Hf1 [Hf2 [Hf3 Hf4]]]]]]].
      exploit genericvalues_inject.mem_inj__free; eauto.
      by inv Hf1; eauto.
      intros [mem2' [Hmem2' [Hinj1 Hinj2]]].
      generalize dependent Heqy0.
      unfold free in *. simpl.
      inv Hwf.
      generalize (mi_range_block b b0 delta H7); intro; subst.
      rewrite Int.add_zero.
      inv Hf1.
      rewrite Hf2.
      progress_tac.
      erewrite <- mi_bounds; eauto.
      rewrite <- Hf3.
      assert (Hlo1: lo1 + 0 = lo1); [omega|rewrite Hlo1 in *].
      assert (Hhi1: hi1 + 0 = hi1); [omega|rewrite Hhi1 in *].
      by rewrite Hmem2'. *)
    - exploit_cmd. progress_tac_agr. infrule_tac. admit. (*
      inv Hstep.
      inv Hinsn. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
      exploit_eq_check_value; eauto; progress_tac.
      { by inv Hvmem. }
      intros [gvs2 [Hgvs2 Hinj]].
      rewrite Hgvs2 in Heqy. inv Heqy.

      inv Hvmem.
      exploit mload_inv; eauto.
      intros [blk1 [ofs1 [mhd [mtl [Hmhd [Hmtl Hmload]]]]]]; subst.
      inv Hinj. inv H8.
      exploit genericvalues_inject.simulation_mload_aux; eauto.
      intros [g2 [Hg2 Hinj]].
      generalize dependent Heqy0.
      unfold mload. simpl.
      inv Hwf.
      generalize (mi_range_block _ _ _ H6); intro; subst.
      rewrite Int.add_zero.
      inv H9.
      subst. simpl in Htd. inv Htd. rewrite Hmtl.
      assert (Hofs1: Int.signed 31 ofs1 + 0 = Int.signed 31 ofs1); [omega|rewrite Hofs1 in *].
      by rewrite Hg2.
    - exploit_cmd. progress_tac_agr. infrule_tac.
      inv Hstep.
      inv Hinsn. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
      exploit_eq_check_value; eauto; progress_tac.
      { by inv Hvmem. }
      intros [gvs2 [Hgvs2 Hinj2]].
      rewrite Hgvs2 in Heqy0. inv Heqy0.
      exploit_eq_check_value; eauto; progress_tac.
      { by inv Hvmem. }
      intros [gvs3 [Hgvs3 Hinj3]].

      inv Hvmem.
      exploit store_inv; eauto.
      intros [blk1 [ofs1 [mc [Hmc [Hfl Hmstore]]]]]; subst.
      destruct mp2 as [|[]]; inv Hmc.
      destruct v; inv H4.
      destruct mp2; inv H6.
      inv Hinj2. inv H8. inv H9.

      exploit genericvalues_inject.mem_inj_mstore_aux; eauto.
      intros [g2 [Hg2 [Hwf' Hinj]]].
      generalize dependent Heqy1.
      unfold mstore. simpl.
      simpl in Htd. inv Htd. rewrite Hfl.
      inv Hwf.
      generalize (mi_range_block _ _ _ H6); intro; subst.
      rewrite Int.add_zero.
      assert (Hofs1: Int.signed 31 ofs1 + 0 = Int.signed 31 ofs1); [omega|rewrite Hofs1 in *].
      rewrite Hgvs3 in Heqy; inv Heqy.
      by rewrite Hg2.
    - exploit_cmd. progress_tac_agr. infrule_tac.
      inv Hnoop; try done.
      inv Hnnn; try by simpl in *.
      + (* is_call *)
        simpl in *.
        destruct cfg1, Hcall as [fptrs1 [fptr1 [fd1 [Hfptrs1 [Hfptr1 [Hfdef1 Hfd1]]]]]].
        inv Hinsn. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
        exploit_eq_check_value; eauto; progress_tac.
        { by inv Hvmem. }
        intros [gvs2 [Hgvs2 Hinj2]].
        simpl in *. rewrite Hgvs2 in Heqy. inv Heqy.
        generalize Heqy0.
        generalize Hfdef1.
        clear -Hinj2 Hvalid_products1_1 Hftable.
        unfold lookupFdefViaPtr.
        unfold ftable_simulation in Hftable.
        erewrite Hftable; eauto.
        destruct (lookupFdefViaGVFromFunTable FunTable0 gvs2); [simpl|done].
        intros. edestruct Hvalid_products1_1; eauto.
        by rewrite <- H in Heqy0.
      + (* is_excall *)
        simpl in *.
        destruct cfg1, Hexcall as [fptrs1 [fptr1 [fd1 [Hfptrs1 [Hfptr1 Hfdef1]]]]].
        inv Hfptr1. simpl in *.
        inv Hinsn. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
        exploit_eq_check_value; eauto; progress_tac.
        { by inv Hvmem. }
        intros [gvs2 [Hgvs2 Hinj2]]. simpl in *.
        rewrite Hgvs2 in Heqy. inv Heqy.
        unfold ftable_simulation in Hftable.
        unfold lookupFdefViaPtr in *.
        unfold lookupExFdecViaPtr in *.
        unfold ftable_simulation in Hftable.
        erewrite Hftable in Hfdef1; eauto.
        remember (lookupFdefViaGVFromFunTable FunTable0 gvs2) as gv2fdef; destruct gv2fdef as [gv2fdef|]; [simpl in *|done].
        rewrite <- Heqy0 in H0.
        rewrite Hvalid_products2 in Hfdef1.
        remember (lookupFdefViaIDFromProducts CurProducts1 gv2fdef) as gv2fdef'; destruct gv2fdef' as [gv2fdef'|]; [done|].
        rewrite Hfdef1 in H0.
        destruct fd1. destruct fheader5.
        remember (params2GVs CurTargetData1 params5 locals2 Globals0) as params; destruct params as [params|]; [|done].
        destruct H0 as [gvs4 [Hgvs4 H0]].
        apply dos_in_list_gvs_inv in Hgvs4; subst.
        inv Hstep.
        { inv H28.
          rewrite Hfptrs1 in H27. inv H27.
          unfold lookupFdefViaPtr in *.
          erewrite Hftable in H29; eauto.
          rewrite <- Heqgv2fdef in H29. simpl in H29.
          by rewrite <- Heqgv2fdef' in H29.
        }
        exploit_eq_check_params; eauto.
        { by inv Hvmem; eauto. }
        intros [args2 [Hargs2 Hinj2a]]. simpl in *.
        inv H28. apply dos_in_list_gvs_inv in H31. subst.        
        rewrite <- Hargs2 in Heqparams. inv Heqparams.
        rewrite Hfptrs1 in H27. inv H27.
        unfold lookupExFdecViaPtr in H29.
        erewrite Hftable in H29; eauto.
        rewrite <- Heqgv2fdef in H29. simpl in H29.
        rewrite <- Heqgv2fdef' in H29.
        rewrite Hvalid_products2 in H29.
        rewrite Hfdef1 in H29. inv H29.
        exploit callExternalOrIntrinsics_prop_2; eauto.
        { by inv Hvmem; eauto. }
        intros [result2 [b2 [Hresult2 [Hvmem' [Halc' Hinjr]]]]].
        remember (callExternalOrIntrinsics CurTargetData1 Globals0 mem2 fid0 rt (args2Typs la) dck args2) as result; destruct result as [[[result a] b]|]; [|done].
        remember (exCallUpdateLocals CurTargetData1 typ5 noret5 id5 result locals2) as result1; destruct result1 as [result1|]; [done|].
        unfold exCallUpdateLocals in *.
        destruct noret5; [done|].
        destruct oresult; [|done].
        remember (fit_gv CurTargetData1 typ5 g) as fitgv1; destruct fitgv1 as [fitgv1|]; [|done].
        inv Hresult2.
        destruct (Hinjr g eq_refl) as [result2 [Hresult2 Hinjrr]]. clear Hinjr.
        exploit genericvalues_inject.simulation__fit_gv; eauto.
        { by inv Hvmem; eauto. }
        intros [fitgv2 [Hfitgv2 Hinjf]].
        rewrite <- Hresult2 in Heqresult. inv Heqresult.
        by rewrite Hfitgv2 in Heqresult1. *)
      - admit. - admit.
  Qed.

  Theorem hint_sem_F_hint_sem
    pbid alpha li1 li2
    ecs1 mem1 ns1
    ecs2 mem2 ns2
    (Hsem: hint_sem pbid alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2) :
    F hint_sem pbid alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2.
  Proof.
    split. (*admit. admit.*)
    - by eapply hint_sem_F_progress_hint_sem; eauto.
    - by eapply hint_sem_F_step_hint_sem; eauto.
  Qed.
End Relation.
