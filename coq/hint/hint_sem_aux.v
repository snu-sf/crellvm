Require Import sflib.

Require Import vellvm.
Require Import hint_sem.
Require Import validator_aux.
Require Import vars_aux.
Require Import syntax_ext.

Require Import FSets.
Require Import FSets.FSetInterface.

Import Opsem.

Ltac destruct_step_tac :=
  repeat match goal with
           | [H1: ret_pop_cmd (ret _) _ _ = pop_one_X (CurCmds ?ec) ?hpn,
             H2: sInsn _ {| ECS := ?ec :: _; Mem := _ |}
             {| ECS := ?ec' :: _; Mem := _ |} _ |- _] =>
           destruct ec, ec'; simpl in *; unfold pop_one_X in H1;
             destruct (noop_idx_zero_exists hpn); try done
           | [H: ret_pop_cmd (ret _) _ _ =
             match ?CurCmds with
               | nil => ret_pop_terminator
               | _ :: _ => ret_pop_cmd _ _ _ end |- _] =>
           destruct CurCmds; try done; inv H
         end;
  try ((repeat match goal with
                 | [H: sInsn _ _ _ _ |- _] => inv H; done
               end); fail).

Definition is_alloca_or_malloc ocmd :=
  match ocmd with
    | Some (insn_alloca _ _ _ _) => true
    | Some (insn_malloc _ _ _ _) => true
    | _ => false
  end.

Definition is_free_or_store ocmd :=
  match ocmd with
    | Some (insn_free _ _ _) => true
    | Some (insn_store _ _ _ _ _) => true
    | _ => false
  end.

Lemma not_undef_implies_cgv2gvs_same:
  forall gvs t (Hn: not_undef gvs), (GenericValueHelper.cgv2gvs gvs t) = gvs.
Proof.
  intros; unfold not_undef in Hn.
  Local Transparent GenericValueHelper.cgv2gvs.
  unfold GenericValueHelper.cgv2gvs; simpl; unfold GenericValueHelper.cgv2gvs, cgv2gv.
  destruct gvs; [done|].
  destruct p; destruct v; try done.
  destruct gvs; done.
Qed.

Lemma def_cmd_inl_implies_locals_update:
  forall cmd l n ec ec' ecs ecs' hpn cfg mem mem' tr i
    (Heqpop: ret_pop_cmd (ret cmd) l n = pop_one_X (CurCmds ec) hpn)
    (Hncall: forall rid : id, state_props.is_general_call (ret cmd) rid -> False)
    (Hstep: sInsn cfg {| EC := ec; ECS := ecs; Mem := mem |}
      {| EC := ec'; ECS := ecs'; Mem := mem' |} tr)
    (Heqcmdid: inl i = vars_aux.def_cmd cmd),
    exists igv, Locals ec' = updateAddAL _ (Locals ec) i igv.
Proof. admit.
  (*intros.
  destruct cmd0; destruct_step_tac;
    try (by inv Hstep; inv Heqcmdid; eexists; reflexivity).

  Case "select".
  inv Hstep; inv Heqcmdid.
  destruct (isGVZero TD c); eexists; done.

  Case "call".
  by elim (Hncall id5).*)
Admitted.

Lemma def_cmd_inl_not_malloc_implies_memory_same:
  forall cmd l n ec ec' ecs ecs' hpn cfg mem mem' tr i
    (Heqpop: ret_pop_cmd (ret cmd) l n = pop_one_X (CurCmds ec) hpn)
    (Hnalloc: false = is_alloca_or_malloc (ret cmd))
    (Hncall: forall rid : id, state_props.is_general_call (ret cmd) rid -> False)
    (Hstep: sInsn cfg {| EC := ec; ECS := ecs; Mem := mem |}
      {| EC := ec'; ECS := ecs'; Mem := mem' |} tr)
    (Heqcmdid: inl i = vars_aux.def_cmd cmd),
    mem' = mem.
Proof. admit.
  (*intros.
  destruct cmd0; destruct_step_tac.
  by elim (Hncall id5).*)
Admitted.

Lemma getOperandValue_implies_getOperandValueExt_new:
  forall td v olc lc gl rv
    (Hget: getOperandValue td v lc gl = rv),
    getOperandValueExt td (vars_aux.add_ntag_value v) olc lc gl = rv.
Proof. by destruct v. Qed.

Lemma getOperandValue_equals_getOperandValueExt_new:
  forall td v olc lc gl,
    getOperandValue td v lc gl =
    getOperandValueExt td (vars_aux.add_ntag_value v) olc lc gl.
Proof. by destruct v. Qed.

Lemma values2GVs_implies_values2GenericValueExt_new:
  forall td lsv olc lc gl rv
    (Hv2gvs: values2GVs td lsv lc gl = rv),
    values2GenericValueExt td (vars_aux.add_ntag_lsv lsv) olc lc gl = rv.
Proof.
  induction lsv; [done|]; i; s.
  rewrite <- getOperandValue_equals_getOperandValueExt_new.
  destruct a; unfold values2GVs in Hv2gvs; s.
  destruct (getOperandValue td v lc gl); [|done].
  hexploit (IHlsv olc lc gl (values2GVs td lsv lc gl)); eauto; intro Heq.
  rewrite Heq; done.
Qed.

Ltac ext_imp_tac :=
  (by i; try unfold BOPEXT, FBOPEXT, TRUNCEXT, EXTEXT, CASTEXT, ICMPEXT, FCMPEXT;
    repeat rewrite <- getOperandValue_equals_getOperandValueExt_new).

Lemma BOP_implies_BOPEXT_new:
  forall td olc lc gl op bsz v1 v2 rv
    (Hbop: BOP td lc gl op bsz v1 v2 = rv),
    BOPEXT td olc lc gl op bsz
    (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = rv.
Proof. ext_imp_tac. Qed.

Lemma FBOP_implies_FBOPEXT_new:
  forall td olc lc gl op bsz v1 v2 rv
    (Hfbop: FBOP td lc gl op bsz v1 v2 = rv),
    FBOPEXT td olc lc gl op bsz
    (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = rv.
Proof. ext_imp_tac. Qed.

Lemma TRUNC_implies_TRUNCEXT_new:
  forall td olc lc gl op t1 v t2 rv
    (Htrunc: TRUNC td lc gl op t1 v t2 = rv),
    TRUNCEXT td olc lc gl op t1 (vars_aux.add_ntag_value v) t2 = rv.
Proof. ext_imp_tac. Qed.

Lemma EXT_implies_EXTEXT_new:
  forall td olc lc gl op t1 v t2 rv
    (Hext: EXT td lc gl op t1 v t2 = rv),
    EXTEXT td olc lc gl op t1 (vars_aux.add_ntag_value v) t2 = rv.
Proof. ext_imp_tac. Qed.

Lemma CAST_implies_CASTEXT_new:
  forall td olc lc gl op t1 v t2 rv
    (Hcast: CAST td lc gl op t1 v t2 = rv),
    CASTEXT td olc lc gl op t1 (vars_aux.add_ntag_value v) t2 = rv.
Proof. ext_imp_tac. Qed.

Lemma ICMP_implies_ICMPEXT_new:
  forall td olc lc gl c t v1 v2 rv
    (Hicmp: ICMP td lc gl c t v1 v2 = rv),
    ICMPEXT td olc lc gl c t
    (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = rv.
Proof. ext_imp_tac. Qed.

Lemma FCMP_implies_FCMPEXT_new:
  forall td olc lc gl c t v1 v2 rv
    (Hfcmp: FCMP td lc gl c t v1 v2 = rv),
    FCMPEXT td olc lc gl c t
    (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = rv.
Proof. ext_imp_tac. Qed.

Lemma eqs_eq_reg_sem_set_add:
  forall cfg olc lc m gmax e x r
    (Hsem_old: eqs_eq_reg_sem cfg olc lc m gmax e)
    (Hsem_new: eq_reg_sem cfg olc lc m gmax x r),
    eqs_eq_reg_sem cfg olc lc m gmax (EqRegSetImpl.add (x, r) e).
Proof.
  rr; i.
  rewrite EqRegSetFacts.add_b in H.
  apply orb_true_iff in H; destruct H as [Heq|Hind].
  - unfold EqRegSetFacts.eqb in Heq.
    destruct (EqRegSetFacts.eq_dec (x, r) (x0, r0)); try done.
    inversion e0; subst; done.
  - eapply Hsem_old; eauto.
Qed.

Lemma eqs_eq_heap_sem_set_add:
  forall cfg olc lc m e p t a v
    (Hsem_old: eqs_eq_heap_sem cfg olc lc m e)
    (Hsem_new: eq_heap_sem cfg olc lc m p t a v),
    eqs_eq_heap_sem cfg olc lc m (EqHeapSetImpl.add (p, t, a, v) e).
Proof.
  unfold eqs_eq_heap_sem; i.
  rewrite EqHeapSetFacts.add_b in H.
  apply orb_true_iff in H; destruct H as [Heq|Hind].
  - unfold EqHeapSetFacts.eqb in Heq.
    destruct (EqHeapSetFacts.eq_dec (p, t, a, v) (p0, t0, a0, v0)); try done.
    inversion e0; subst; done.
  - eapply Hsem_old; eauto.
Qed.

Lemma mstore_gv_chunks_match_typ td mem mp t gv a mem'
  (H: mstore td mem mp t gv a = ret mem') :
  gv_chunks_match_typ td gv t.
Proof.
  exploit mstore_inversion; eauto.
  clear H; intros [b [ofs [cm [mc [Hmp [Hmc H]]]]]]; subst.
  unfold gv_chunks_match_typ; rewrite Hmc; clear Hmc.
  generalize dependent (Int.signed 31 ofs).
  generalize dependent mem'.
  generalize dependent mem.
  generalize dependent gv.
  induction mc; destruct gv; intros; inv H; auto.
  destruct p.
  match goal with
    | [H: context[if ?c then _ else _] |- _] =>
      remember c as cc; destruct cc; [|done]
  end.
  remember (Mem.store m mem0 b z v) as mm; destruct mm; [|done].
  symmetry in Heqcc; rewrite andb_true_iff in Heqcc; destruct Heqcc.
  apply memory_chunk_eq_prop in H; subst.
  apply has_chunk_eq_prop in H0; subst.
  constructor.
  - by split; [done|].
  - by eapply (IHmc gv m0); eauto.
Qed.

Lemma mload__matches_chunks : forall t TD gv a ptr M,
  mload TD M ptr t a = Some gv ->
  gv_chunks_match_typ TD gv t.
Proof.
  intros.
  apply mload_inv in H.
  destruct H as [b [ofs [m [mc [J1 [J2 J3]]]]]]; subst.
  unfold gv_chunks_match_typ, vm_matches_typ, gv_has_chunk.
  fill_ctxhole.
  generalize dependent (Int.signed 31 ofs).
  generalize dependent gv.
  clear.
  induction mc; intros; inv J3; auto.
    inv_mbind. symmetry_ctx.
    apply IHmc in HeqR0.
    constructor; eauto using Mem.load_chunk.
Qed.

Lemma mload_after_mstore_get_same_value:
  forall td mem mem' mp t a gv1 rv
    (Hstore: mstore td mem mp t gv1 a = ret mem')
    (Hload: mload td mem' mp t a = rv),
    exists gv2, rv = ret gv2 /\ eq_gvs gv2 gv1.
Proof.
  intros.
  exists gv1; split; [|done].
  rewrite <- Hload; clear Hload rv.
  exploit memory_props.MemProps.mstore_mload_same; eauto.
  by eapply mstore_gv_chunks_match_typ; eauto.
Qed.

Lemma update_preserves_maydiff_sem_left:
  forall lc1 lc2 olc1 olc2 alpha' md i v
    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md),
    maydiff_sem (updateAddAL GVs lc1 i v) lc2 alpha' 
    match (lookupAL GVs lc1 i) with
      | ret xv => updateAddAL GVs olc1 i xv
      | _ => deleteAL _ olc1 i
    end
    olc2
    (IdExtSetImpl.add (vars_aux.add_otag i)
      (IdExtSetImpl.add (vars_aux.add_ntag i) md)).
Proof.
  intros.
  unfold maydiff_sem in *; intros x Hx.
  rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx; destruct Hx as [Hno Hx].
  rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx; destruct Hx as [Hnn Hx].
  remember (Hmd _ Hx) as Hbrd; clear HeqHbrd Hmd.
  unfold variable_equivalent in *.
  destruct x as [x [|]]; simpl in *.
  - destruct (id_dec i0 x);
    [by subst; unfold add_otag, IdExtSetFacts.eqb in Hno;
      destruct (IdExtSetFacts.eq_dec (x, ntag_old) (x, ntag_old))|].
    destruct (lookupAL GVs lc1 i0);
      [by rewrite <- lookupAL_updateAddAL_neq; eauto|
        by rewrite lookupAL_deleteAL_neq; eauto].
  - destruct (id_dec i0 x);
    [by subst; unfold add_ntag, IdExtSetFacts.eqb in Hnn;
      destruct (IdExtSetFacts.eq_dec (x, ntag_new) (x, ntag_new))|].
    by rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma update_preserves_maydiff_sem_right:
  forall lc1 lc2 olc1 olc2 alpha' md i v
    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md),
    maydiff_sem lc1 (updateAddAL GVs lc2 i v) alpha' olc1 
    match (lookupAL GVs lc2 i) with
      | ret xv => updateAddAL GVs olc2 i xv
      | _ => deleteAL _ olc2 i
    end
    (IdExtSetImpl.add (vars_aux.add_otag i)
      (IdExtSetImpl.add (vars_aux.add_ntag i) md)).
Proof.    
  intros.
  unfold maydiff_sem in *; intros x Hx.
  rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx; destruct Hx as [Hno Hx].
  rewrite IdExtSetFacts.add_b in Hx; apply orb_false_iff in Hx; destruct Hx as [Hnn Hx].
  remember (Hmd _ Hx) as Hbrd; clear HeqHbrd Hmd.
  unfold variable_equivalent in *.
  destruct x as [x [|]]; simpl in *.
  - destruct (id_dec i0 x);
    [by subst; unfold add_otag, IdExtSetFacts.eqb in Hno;
      destruct (IdExtSetFacts.eq_dec (x, ntag_old) (x, ntag_old))|].
    destruct (lookupAL GVs lc2 i0);
      [by rewrite <- lookupAL_updateAddAL_neq; eauto|
        by rewrite lookupAL_deleteAL_neq; eauto].
  - destruct (id_dec i0 x);
    [by subst; unfold add_ntag, IdExtSetFacts.eqb in Hnn;
      destruct (IdExtSetFacts.eq_dec (x, ntag_new) (x, ntag_new))|].
    by rewrite <- lookupAL_updateAddAL_neq; eauto.
Qed.

Lemma oldnew_preserves_lookup:
  forall i0 olc lc lc' vgvs ie gvs
    (Hec': lc' = (updateAddAL GVs lc i0 gvs))
    (Hnot: IdExtSetImpl.mem (add_otag i0)
      (used_locals_in_value (value_ext_id ie)) = false)
    (Hov: logical_step.lookupALExt olc lc ie = ret vgvs),
    logical_step.lookupALExt
    match lookupAL GVs lc i0 with
      | ret xv => updateAddAL GVs olc i0 xv
      | merror => deleteAL GVs olc i0
    end lc' (new_to_old_local_in_id i0 ie) = 
    ret vgvs.
Proof.
  intros; simpl in *.
  rewrite IdExtSetFacts.singleton_b in Hnot.
  unfold IdExtSetFacts.eqb in Hnot.
  destruct (IdExtSetFacts.eq_dec ie (add_otag i0)) as [|Hnoteq]; [done|]; clear Hnot.

  destruct ie as [i [|]]; simpl in *.
  - destruct (id_dec i0 i); [by subst; elim Hnoteq|]; simpl.
    destruct (lookupAL GVs lc i0).
    + rewrite <- lookupAL_updateAddAL_neq; eauto.
    + rewrite lookupAL_deleteAL_neq; eauto.
  - destruct (id_dec i0 i); subst; simpl; 
    [by rewrite Hov, lookupAL_updateAddAL_eq |
      by rewrite <- lookupAL_updateAddAL_neq; eauto].
Qed.

Lemma oldnew_preserves_getOperandValueExt:
  forall i0 cfg v olc lc lc' vgvs gvs
    (Hec': lc' = (updateAddAL GVs lc i0 gvs))
    (Hnot: IdExtSetImpl.mem (add_otag i0) (used_locals_in_value v) = false)
    (Hov: getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg)
      = ret vgvs),
    getOperandValueExt (CurTargetData cfg) (new_to_old_local_in_value i0 v)
    match lookupAL GVs lc i0 with
      | ret xv => updateAddAL GVs olc i0 xv
      | merror => deleteAL GVs olc i0
    end lc' (Globals cfg) = ret vgvs.
Proof.
  intros; destruct v as [ie|cst];
  [by simpl; eapply oldnew_preserves_lookup; eauto|done].
Qed.

Ltac mem_destruct_tac :=
  repeat match goal with
           | [H: negb _ = true |- _] => apply negb_true_iff in H
           | [H: _ || _ = false |- _] => rewrite orb_false_iff in H; inv H
           | [H: IdExtSetImpl.mem _ (IdExtSetImpl.add _ _) = false |- _] =>
             rewrite IdExtSetFacts.add_b in H
           | [H: IdExtSetImpl.mem _ (IdExtSetImpl.union _ _) = false |- _] =>
             rewrite IdExtSetFacts.union_b in H
         end.

Lemma oldnew_preserves_eq_reg_sem:
  forall i0 y r cfg lc lc' olc mem gmax igvs
    (Hec': lc' = (updateAddAL GVs lc i0 igvs))
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

  { Case "1. normal value".
  eapply eq_reg_sem_value; eauto; simpl in *.
  - destruct y as [y [|]]; simpl in *.
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
      * rewrite <- lookupAL_updateAddAL_neq; eauto.

  - destruct r; try (inv Hrhs; fail); simpl in Hnot; mem_destruct_tac.

    (* BOP *)
    + inv Hrhs; econstructor.
      unfold BOPEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      remember (getOperandValueExt (CurTargetData cfg) w olc lc (Globals cfg))
      as wov; destruct wov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt in Heqvov; eauto.
      symmetry in Heqwov; eapply oldnew_preserves_getOperandValueExt in Heqwov; eauto.
      rewrite Heqvov, Heqwov.
      done.

    (* FBOP *)
    + inv Hrhs; econstructor; unfold FBOPEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      remember (getOperandValueExt (CurTargetData cfg) w olc lc (Globals cfg))
      as wov; destruct wov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt in Heqvov; eauto.
      symmetry in Heqwov; eapply oldnew_preserves_getOperandValueExt in Heqwov; eauto.
      by rewrite Heqvov, Heqwov.

    (* ExtractValue *)
    + inv Hrhs; apply rhs_ext_extractvalue_sem with (gvs:=gvs0); [|done].
      eapply oldnew_preserves_getOperandValueExt; eauto.

    (* InsertValue *)
    + inv Hrhs; apply rhs_ext_insertvalue_sem with (gvs:=gvs0) (gvs':=gvs'0);
      [| |done]; eapply oldnew_preserves_getOperandValueExt; eauto.

    (* GEP *)
    + inv Hrhs; eapply rhs_ext_gep_sem; eauto.
      * eapply oldnew_preserves_getOperandValueExt; eauto.
      * clear Hlookup Heqgvs H11 H10 gvs gvs'. (* for simple induction *)
        generalize dependent vidxss.
        induction lsv as [|[sa va] lsv]; [done|].
        intros; simpl.
        unfold used_locals_in_lsv in H2; simpl in H2.
        mem_destruct_tac.
        inv H9.
        remember (getOperandValueExt (CurTargetData cfg) va olc
          lc (Globals cfg)) as vaov; destruct vaov; [|done].
        symmetry in Heqvaov; eapply oldnew_preserves_getOperandValueExt in Heqvaov;
          eauto.
        rewrite Heqvaov.
        destruct (values2GenericValueExt (CurTargetData cfg) lsv olc lc (Globals cfg));
          try done.
        hexploit IHlsv; try done.
        by intros Hind; rewrite Hind.

    (* TRUNC *)
    + inv Hrhs; econstructor; unfold TRUNCEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt in Heqvov; eauto.
      by rewrite Heqvov.

    (* EXT *)
    + inv Hrhs; econstructor; unfold EXTEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt in Heqvov; eauto.
      by rewrite Heqvov.

    (* CAST *)
    + inv Hrhs; econstructor; unfold CASTEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt in Heqvov; eauto.
      by rewrite Heqvov.

    (* ICMP *)
    + inv Hrhs; econstructor; unfold ICMPEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      remember (getOperandValueExt (CurTargetData cfg) w olc lc (Globals cfg))
      as wov; destruct wov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt in Heqvov; eauto.
      symmetry in Heqwov; eapply oldnew_preserves_getOperandValueExt in Heqwov; eauto.
      by rewrite Heqvov, Heqwov.

    (* FCMP *)
    + inv Hrhs; econstructor; unfold FCMPEXT in *.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      remember (getOperandValueExt (CurTargetData cfg) w olc lc (Globals cfg))
      as wov; destruct wov; [|done].
      symmetry in Heqvov; eapply oldnew_preserves_getOperandValueExt in Heqvov; eauto.
      symmetry in Heqwov; eapply oldnew_preserves_getOperandValueExt in Heqwov; eauto.
      by rewrite Heqvov, Heqwov.

    (* SELECT *)
    + inv Hrhs; [eapply rhs_ext_select_true_sem|eapply rhs_ext_select_false_sem]; eauto;
      eapply oldnew_preserves_getOperandValueExt; eauto.

    (* Value *)
    + inv Hrhs; eapply rhs_ext_value__sem.
      eapply oldnew_preserves_getOperandValueExt; eauto.
  }

  { Case "2. old_alloca_old".
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
    + by rewrite <- lookupAL_updateAddAL_neq; eauto.
  }
Qed.

Lemma oldnew_preserves_eq_heap_sem:
  forall i p t a v cfg lc lc' olc mem igvs
    (Hec': lc' = (updateAddAL GVs lc i igvs))
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
  symmetry in Heqpove; eapply oldnew_preserves_getOperandValueExt in Heqpove; eauto.
  symmetry in Heqvove; eapply oldnew_preserves_getOperandValueExt in Heqvove; eauto.
  by rewrite Heqpove, Heqvove.
Qed.

Lemma oldnew_preserves_neq_reg_sem:
  forall i ii lg cfg lc lc' olc igvs
    (Hec': lc' = (updateAddAL GVs lc i igvs))
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
  symmetry in Heqvii; eapply oldnew_preserves_lookup in Heqvii; eauto;
    [|by simpl; rewrite IdExtSetFacts.singleton_b; apply H].
  rewrite Heqvii.

  destruct lg as [i|gi]; [|done]; simpl.
  remember (logical_step.lookupALExt olc lc i) as vi; destruct vi; [|done].
  symmetry in Heqvi; eapply oldnew_preserves_lookup in Heqvi; eauto.
  by rewrite Heqvi.
Qed.
