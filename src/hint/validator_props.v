Require Import vgtac.

Require Import vellvm.
Require Import genericvalues_inject.

Require Import logical_step.
Require Import validator_aux.
Require Import syntax_ext.
Require Import hint_sem.
Require Import set_facts2.
Require Import decs.
Require Import memory_sim.
Require Import basic_const_inject.

Import Opsem.
Import hints.
Import syntax_ext.

Lemma eq_gvs_implies_setoid_eq:
  forall gvs1 gvs2
    (Heq: eq_gvs gvs1 gvs2),
    gvs1 = gvs2.
Proof.
  intros; unfold eq_gvs in Heq.
  hexploit (Heq gvs1); intros [Heqins _].
  exploit Heqins; done.
Qed.

Lemma eq_gvs_refl : forall gvs, eq_gvs gvs gvs.
Proof. done. Qed.

Lemma lift_op1_prop f a t :
  lift_op1 DGVs f a t = f a.
Proof.
  by transitivity (MDGVs.lift_op1 f a t).
Qed.

Lemma lift_op2_prop f a b t :
  lift_op2 DGVs f a b t = f a b.
Proof.
  by transitivity (MDGVs.lift_op2 f a b t).
Qed.

Ltac infrule_microtac :=
  unfold vgtac.is_true in *;
  match goal with
    | [H: true = true |- _] => clear H
    | [H: true = _ |- _] => symmetry in H
    | [H: _ && _ = true |- _] => apply andb_true_iff in H
    | [H: _ || _ = true |- _] =>  apply orb_true_iff in H
    | [H: _ /\ _ |- _] => destruct H
    | [H: negb _ = false |- _] => rewrite negb_false_iff in H
    | [H: negb _ = true |- _] => apply negb_true_iff in H
    | [H: ?c = false |- context[?c]] => by rewrite H
    | [|- context[_ && _ = false]] => rewrite andb_false_iff
    | [H: (_, _) = (_, _) |- _] => inv H
    | [H: eq_gvs _ _ |- _] => apply eq_gvs_implies_setoid_eq in H; subst
    | [H: rhs_ext_value_sem _ _ _ (rhs_ext_value _) _ |- _] => inv H

    | [H: match ?x with
            | ret _ => _
            | merror => merror
          end = ret _ |- _] =>
    let y := fresh "y" in
      remember x as y;
      destruct y; [|done]
    | [H: context[lift_op1 _ _ _ _] |- _] =>
      rewrite lift_op1_prop in H
    | [|- context[lift_op1 _ _ _ _]] =>
      rewrite lift_op1_prop
    | [H: context[lift_op2 _ _ _ _ _] |- _] =>
      rewrite lift_op2_prop in H
    | [|- context[lift_op2 _ _ _ _ _]] =>
      rewrite lift_op2_prop

    | [H: proj_sumbool (id_ext_dec _ _) = true |- _] =>
      apply id_ext_dec_r in H
    | [H: proj_sumbool (value_ext_dec _ _) = true |- _] =>
      apply value_ext_dec_r in H
    | [H: proj_sumbool (bop_dec _ _) = true |- _] =>
      apply bop_dec_r in H
    | [H: proj_sumbool (fbop_dec _ _) = true |- _] =>
      apply fbop_dec_r in H
    | [H: proj_sumbool (extop_dec _ _) = true |- _] =>
      apply extop_dec_r in H
    | [H: proj_sumbool (castop_dec _ _) = true |- _] =>
      apply castop_dec_r in H
    | [H: proj_sumbool (cond_dec _ _) = true |- _] =>
      apply cond_dec_r in H
    | [H: proj_sumbool (fcond_dec _ _) = true |- _] =>
      apply fcond_dec_r in H
    | [H: proj_sumbool (floating_point_dec _ _) = true |- _] =>
      apply floating_point_dec_r in H
    | [H: proj_sumbool (sz_dec _ _) = true |- _] =>
      apply sz_dec_r in H
    | [H: proj_sumbool (const_dec _ _) = true |- _] =>
      apply const_dec_r in H
    | [H: proj_sumbool (list_const_dec _ _) = true |- _] =>
      apply list_const_dec_r in H
    | [H: proj_sumbool (typ_dec _ _) = true |- _] =>
      apply typ_dec_r in H
    | [H: proj_sumbool (attributes_dec _ _) = true |- _] =>
      apply attributes_dec_r in H
    | [H: proj_sumbool (noret_dec _ _) = true |- _] =>
      apply noret_dec_r in H
    | [H: proj_sumbool (clattrs_dec _ _) = true |- _] =>
      apply clattrs_dec_r in H
    | [H: proj_sumbool (varg_dec _ _) = true |- _] =>
      apply varg_dec_r in H
    | [H: proj_sumbool (l_dec _ _) = true |- _] =>
      apply l_dec_r in H

    | [H: IdExtSetFacts.eqb ?a ?b = true |- _] =>
      unfold IdExtSetFacts.eqb in H;
        destruct (IdExtSetFacts.eq_dec a b); [|done];
        subst
    | [|- context[IdExtSetImpl.mem _ (IdExtSetImpl.remove _ _)]] =>
      rewrite IdExtSetFacts.remove_b
    | [H: EqRegSetFacts.eqb _ _ = true |- _] =>
      apply EqRegSetFacts2.eqb_prop1 in H
    | [H: EqHeapSetFacts.eqb _ _ = true |- _] =>
      apply EqHeapSetFacts2.eqb_prop1 in H
    | [H: NeqRegSetFacts.eqb _ _ = true |- _] =>
      apply NeqRegSetFacts2.eqb_prop1 in H
    | [H: EqRegSetImpl.mem _ (EqRegSetImpl.add _ _) = true |- _] =>
      rewrite EqRegSetFacts.add_b in H
    | [H: EqHeapSetImpl.mem _ (EqHeapSetImpl.add _ _) = true |- _] =>
      rewrite EqHeapSetFacts.add_b in H
    | [H: NeqRegSetImpl.mem _ (NeqRegSetImpl.add _ _) = true |- _] =>
      rewrite NeqRegSetFacts.add_b in H
    | [H1: eqs_eq_reg_sem _ _ _ _ _ (eqs_eq_reg (invariant_original (hint_invariant ?h))),
           H2: mem_eq_reg_orig (_, _) ?h = true |- _] =>
      generalize (H1 _ _ H2); clear H2; intro H2
    | [H1: eqs_eq_reg_sem _ _ _ _ _ (eqs_eq_reg (invariant_original (hint_invariant ?h))),
           H2: mem_eq_reg_orig (_, _) ?h = true |- _] =>
      generalize (H1 _ _ H2); clear H2; intro H2
    | [H1: eqs_eq_reg_sem _ _ _ _ _ (eqs_eq_reg (invariant_optimized (hint_invariant ?h))),
           H2: mem_eq_reg_opt (_, _) ?h = true |- _] =>
      generalize (H1 _ _ H2); clear H2; intro H2
    | [H1: eqs_eq_heap_sem _ _ _ _ (eqs_eq_heap (invariant_original (hint_invariant ?h))),
           H2: mem_eq_heap_orig (_, _) ?h = true |- _] =>
      generalize (H1 _ _ _ _ H2); clear H2; intro H2
    | [H1: eqs_eq_heap_sem _ _ _ _ (eqs_eq_heap (invariant_optimized (hint_invariant ?h))),
           H2: mem_eq_heap_opt (_, _) ?h = true |- _] =>
      generalize (H1 _ _ _ _ H2); clear H2; intro H2
    | [H: hint_sem _ _ _ _ _ _ _ _ _ _ _ |- _] =>
      let olc1 := fresh "olc1" in
      let olc2 := fresh "olc2" in
      let Hmd := fresh "Hmd" in
      let Hinvl_r := fresh "Hinvl_r" in
      let Hinvl_h := fresh "Hinvl_h" in
      let Hinvl_ne := fresh "Hinvl_ne" in
      let Hinvr_r := fresh "Hinvr_r" in
      let Hinvr_h := fresh "Hinvr_h" in
      let Hinvr_ne := fresh "Hinvr_ne" in
      let Hisol := fresh "Hisol" in
      let Hisor := fresh "Hisor" in
      destruct H as [olc1 [olc2 [Hmd [[Hinvl_r [Hinvl_h Hinvl_ne]] [[Hinvr_r [Hinvr_h Hinvr_ne]] [Hisol Hisor]]]]]]
  end.

Ltac infrule_tac :=
  simpl;
  try match goal with
    | [H: hint_sem _ _ _ _ _ _ _ _ _ _ ?h |- hint_sem _ _ _ _ _ _ _ _ _ _ (if ?c then _ else ?h)] =>
      let c' := fresh "c" in
      remember c as c'; destruct c'; [|done]
      end;
  repeat
    ((try done);
     (try infrule_microtac);
     simpl;
     subst;
     auto;
     (try (split; [by infrule_tac|]));
     (try (split; [|by infrule_tac]))).

Lemma eq_check_value_prop
  cfg1 cfg2 lc1 lc2 olc1 olc2 mem1 mem2 
  md inv alpha gmax li1 li2
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2 inv)
  v1 v2 gvs1 gvs2
  (Heq: eq_check_value md (invariant_original inv) (invariant_optimized inv) v1 v2)
  (Htd: CurTargetData cfg1 = CurTargetData cfg2)
  (Hwfm: wf_sb_mi gmax alpha mem1 mem2)
  (Hgl: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))
  (H1: getOperandValueExt (CurTargetData cfg1) v1 olc1 lc1 (Globals cfg1) = ret gvs1)
  (H2: getOperandValueExt (CurTargetData cfg2) v2 olc2 lc2 (Globals cfg2) = ret gvs2) :
  genericvalues_inject.gv_inject alpha gvs1 gvs2.
Proof.
  inv Hinv.
  inv H; infrule_tac.
  inv H0; infrule_tac.
  destruct v1, v2; inv Heq; simpl in H1; simpl in H2; infrule_tac.
  - repeat
    (match goal with
       | [H: _ \/ _ |- _] => destruct H; infrule_tac
     end).
    + generalize dependent (Hmd x0 H10); clear H10; intro H10.
      unfold variable_equivalent in H10.
      by rewrite H1, H2 in H10.
    + generalize dependent (Hmd x H9); clear H9; intro H9.
      generalize dependent (H7 _ _ H10); clear H10; intro H10.
      inv H10; infrule_tac; simpl in *.
      rewrite H2 in H11; inv H11.
      unfold variable_equivalent in H9.
      by rewrite H1, Hlookup in H9.
    + generalize dependent (Hmd x H9); clear H9; intro H9.
      generalize dependent (H7 _ _ H10); clear H10; intro H10.
      inv H10; infrule_tac; simpl in *.
      unfold variable_equivalent in H9.
      rewrite H1, H11 in H9.
      by rewrite Hlookup in H2; inv H2.
    + generalize dependent (Hmd x0 H9); clear H9; intro H9.
      generalize dependent (H3 _ _ H10); clear H10; intro H10.
      inv H10; infrule_tac; simpl in *.
      rewrite Hlookup in H1; inv H1.
      unfold variable_equivalent in H9.
      by rewrite H11, H2 in H9.
    + generalize dependent (Hmd x0 H9); clear H9; intro H9.
      generalize dependent (H3 _ _ H10); clear H10; intro H10.
      inv H10; infrule_tac; simpl in *.
      rewrite H1 in H11; inv H11.
      unfold variable_equivalent in H9.
      by rewrite Hlookup, H2 in H9.
  - generalize (H3 _ _ H10); clear H10; intro H10.
    inv H10; infrule_tac.
    rewrite Hlookup in H1; inv H1.
    simpl in H10.
    inv Hgl.
    rewrite Htd, Hgl2 in H10; rewrite H2 in H10; inv H10.
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    rewrite Hgl2; apply H2.
  - generalize (H7 _ _ H10); clear H10; intro H10.
    inv H10; infrule_tac.
    rewrite Hlookup in H2; inv H2.
    simpl in H10.
    inv Hgl.
    rewrite Htd, Hgl2 in H1; rewrite H1 in H10; inv H10.
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    rewrite Hgl2; apply H1.
  - inv Hgl.
    rewrite Htd, Hgl2 in H1; rewrite H1 in H2; inv H2.
    eapply LLVMtyping_rules.const2GV_refl; eauto.
    rewrite Hgl2; apply H1.
Qed.  

Lemma eq_check_lsv_prop
  cfg1 cfg2 lc1 lc2 olc1 olc2 mem1 mem2 
  md inv alpha gmax li1 li2
  (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
  (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2 inv) :
  forall v1 v2 gvs1 gvs2
  (Heq: eq_check_lsv md (invariant_original inv) (invariant_optimized inv) v1 v2)
  (Htd: CurTargetData cfg1 = CurTargetData cfg2)
  (Hwfm: wf_sb_mi gmax alpha mem1 mem2)
  (Hgl: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))
  (H1: values2GVsExt (CurTargetData cfg1) v1 olc1 lc1 (Globals cfg1) = ret gvs1)
  (H2: values2GVsExt (CurTargetData cfg2) v2 olc2 lc2 (Globals cfg2) = ret gvs2),
  list_forall2 (genericvalues_inject.gv_inject alpha) gvs1 gvs2.
Proof.
  intros v1; induction v1; intros [|v2_hd v2_tl] gvs1 gvs2 Heq Htd Hwfm Hgl H1 H2;
    inv Heq.
  - inv H1; inv H2.
    by constructor.
  - infrule_tac.
    unfold eq_check_sv in H.
    destruct a, v2_hd; infrule_tac.
    inv H1; inv H2.
    remember (getOperandValueExt (CurTargetData cfg1) v olc1 lc1 (Globals cfg1)) as g1; destruct g1; [|done].
    remember (getOperandValueExt (CurTargetData cfg2) v0 olc2 lc2 (Globals cfg2)) as g2; destruct g2; [|done].
    remember (values2GVsExt (CurTargetData cfg1) v1 olc1 lc1 (Globals cfg1)) as gs1; destruct gs1; [|done].
    remember (values2GVsExt (CurTargetData cfg2) v2_tl olc2 lc2 (Globals cfg2)) as gs2; destruct gs2; [|done].
    inv H1; inv H4.
    exploit eq_check_value_prop; eauto.
    constructor; auto.
    by eapply IHv1; eauto.
Qed.

(* A base lemma for all self_use_check preservations. *)
Lemma self_use_check_preserves_getOperandValue:
  forall i v td lc gl gvs rv
    (Hsu: negb (AtomSetImpl.mem i (vars_aux.used_locals_in_value' v)) = true)
    (Hget: getOperandValue td v lc gl = rv),
    getOperandValue td v (updateAddAL GVs lc i gvs) gl = rv.
Proof.
  intros.
  destruct v as [i|]; try done; simpl in *.
  rewrite AtomSetFacts.singleton_b in Hsu.
  apply negb_true_iff in Hsu.
  unfold AtomSetFacts.eqb in Hsu.
  remember (KeySetFacts.eq_dec i i0) as eqi; destruct eqi in Hsu; [done|].
  hexploit lookupAL_updateAddAL_neq; eauto; intro Hleq; rewrite <- Hleq; done.
Qed.

Ltac self_use_check_tac :=
  i; unfold BOP, FBOP, TRUNC, EXT, CAST, ICMP, FCMP in *;
    repeat match goal with
             | [ H: negb (AtomSetImpl.mem _ (union _ _)) = true |- _] =>
               rewrite AtomSetFacts.union_b in H
             | [ H: negb (_ || _) = true |- _] =>
               rewrite negb_orb in H
             | [ H: _ && _ = true |- _] =>
               let Hb1 := fresh "Hb1" in
                 let Hb2 := fresh "Hb2" in
                   (apply andb_prop in H; destruct H as [Hb1 Hb2])
             | [ H: self_use_check _ = true |- _] =>
               unfold self_use_check in H
             | [ H: self_use_check' _ = true |- _] =>
               (unfold self_use_check' in H; simpl in H)
             | [ H: negb (AtomSetImpl.mem _ (vars_aux.used_locals_in_value' ?v))
               = true |- getOperandValue _ ?v _ _ = getOperandValue _ ?v _ _] =>
             (hexploit self_use_check_preserves_getOperandValue;
               try eapply H; eauto)
             | [ H1: negb (AtomSetImpl.mem _ (vars_aux.used_locals_in_value' ?v))
               = true, H2: getOperandValue _ ?v _ _ = _ |-
                 getOperandValue _ ?v _ _ = _] =>
             (eapply self_use_check_preserves_getOperandValue; eauto)
             | [ H: negb (AtomSetImpl.mem _ (vars_aux.used_locals_in_value' ?v))
               = true |- context[ getOperandValue _ ?v _ _ ] ] =>
             let Hveq := fresh "Hveq" in
               (hexploit self_use_check_preserves_getOperandValue; try eapply H; eauto;
                 intro Hveq; rewrite Hveq; try done)
           end.

Lemma self_use_check_preserves_select_getOperandValue_1:
  forall i cv t v1 v2 td lc gl gvs
    (Hsu: self_use_check (ret insn_select i cv t v1 v2) = true),
    getOperandValue td cv lc gl =
    getOperandValue td cv (updateAddAL GVs lc i gvs) gl.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_select_getOperandValue_2:
  forall i cv t v1 v2 td lc gl gvs
    (Hsu: self_use_check (ret insn_select i cv t v1 v2) = true),
    getOperandValue td v1 lc gl =
    getOperandValue td v1 (updateAddAL GVs lc i gvs) gl.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_select_getOperandValue_3:
  forall i cv t v1 v2 td lc gl gvs
    (Hsu: self_use_check (ret insn_select i cv t v1 v2) = true),
    getOperandValue td v2 lc gl =
    getOperandValue td v2 (updateAddAL GVs lc i gvs) gl.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_load_getOperandValue:
  forall i t v a td lc gl gvs
    (Hsu: self_use_check (ret insn_load i t v a) = true),
    getOperandValue td v lc gl =
    getOperandValue td v (updateAddAL GVs lc i gvs) gl.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_extractValue_getOperandValue:
  forall i t v lconst ta td lc gl gvs rv
    (Hsu: self_use_check (ret insn_extractvalue i t v lconst ta) = true)
    (Hget: getOperandValue td v lc gl = rv),
    getOperandValue td v (updateAddAL GVs lc i gvs) gl = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_insertValue_getOperandValue_1:
  forall i t1 v1 t2 v2 lconst td lc gl gvs rv
    (Hsu: self_use_check (ret insn_insertvalue i t1 v1 t2 v2 lconst) = true)
    (Hget: getOperandValue td v1 lc gl = rv),
    getOperandValue td v1 (updateAddAL GVs lc i gvs) gl = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_insertValue_getOperandValue_2:
  forall i t1 v1 t2 v2 lconst td lc gl gvs rv
    (Hsu: self_use_check (ret insn_insertvalue i t1 v1 t2 v2 lconst) = true)
    (Hget: getOperandValue td v2 lc gl = rv),
    getOperandValue td v2 (updateAddAL GVs lc i gvs) gl = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_gep_getOperandValue_1:
  forall i inb t1 v lsv t2 td lc gl gvs rv
    (Hsu: self_use_check (ret insn_gep i inb t1 v lsv t2) = true)
    (Hget: getOperandValue td v lc gl = rv),
    getOperandValue td v (updateAddAL GVs lc i gvs) gl = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_gep_getOperandValue_2:
  forall i inb t1 v lsv t2 td lc gl gvs rv
    (Hsu: self_use_check (ret insn_gep i inb t1 v lsv t2) = true)
    (Hget: values2GVs td lsv lc gl = rv),
    values2GVs td lsv (updateAddAL GVs lc i gvs) gl = rv.
Proof.
  self_use_check_tac.
  generalize dependent rv; induction lsv; [done|]; intros.
  simpl in Hb2.
  apply negb_true_iff in Hb2.
  rewrite AtomSetFacts.union_b in Hb2.
  apply orb_false_iff in Hb2; destruct Hb2 as [Ha Hlsv].
  destruct a; simpl in *.

  assert (Haeq: getOperandValue td v0 lc gl =
    getOperandValue td v0 (updateAddAL GVs lc i0 gvs) gl)
  by (apply negb_true_iff in Ha; self_use_check_tac).
  rewrite <- Haeq.
  destruct (getOperandValue td v0 lc gl); [|done].
  apply negb_true_iff in Hlsv.
  hexploit IHlsv; eauto; intro Hind.
  by rewrite Hind.
Qed.

Lemma self_use_check_preserves_BOP:
  forall i b sz value1 value2 lc gl gvs td rv
    (Hsu: self_use_check (ret insn_bop i b sz value1 value2) = true)
    (Hbop: BOP td lc gl b sz value1 value2 = rv),
    BOP td (updateAddAL GVs lc i gvs) gl b sz value1 value2 = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_FBOP:
  forall i b sz value1 value2 lc gl gvs td rv
    (Hsu: self_use_check (ret insn_fbop i b sz value1 value2) = true)
    (Hfbop: FBOP td lc gl b sz value1 value2 = rv),
    FBOP td (updateAddAL GVs lc i gvs) gl b sz value1 value2 = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_TRUNC:
  forall i tcop t v ta td lc gl gvs rv
    (Hsu: self_use_check (ret insn_trunc i tcop t v ta) = true)
    (Htrunc: TRUNC td lc gl tcop t v ta = rv),
    TRUNC td (updateAddAL GVs lc i gvs) gl tcop t v ta = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_EXT:
  forall i op t1 v t2 td lc gl gvs rv
    (Hsu: self_use_check (ret insn_ext i op t1 v t2) = true)
    (Htrunc: EXT td lc gl op t1 v t2 = rv),
    EXT td (updateAddAL GVs lc i gvs) gl op t1 v t2 = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_CAST:
  forall i op t1 v t2 td lc gl gvs rv
    (Hsu: self_use_check (ret insn_cast i op t1 v t2) = true)
    (Hcast: CAST td lc gl op t1 v t2 = rv),
    CAST td (updateAddAL GVs lc i gvs) gl op t1 v t2 = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_ICMP:
  forall i c t v1 v2 td lc gl gvs rv
    (Hsu: self_use_check (ret insn_icmp i c t v1 v2) = true)
    (Hicmp: ICMP td lc gl c t v1 v2 = rv),
    ICMP td (updateAddAL GVs lc i gvs) gl c t v1 v2 = rv.
Proof. self_use_check_tac. Qed.

Lemma self_use_check_preserves_FCMP:
  forall i c t v1 v2 td lc gl gvs rv
    (Hsu: self_use_check (ret insn_fcmp i c t v1 v2) = true)
    (Hfcmp: FCMP td lc gl c t v1 v2 = rv),
    FCMP td (updateAddAL GVs lc i gvs) gl c t v1 v2 = rv.
Proof. self_use_check_tac. Qed.

Lemma not_in_maydiff_implies_gv_inject:
  forall ii md lc1 lc2 i0 igvs1 igvs2 alpha olc1 olc2
    (Hninmd: negb (IdExtSetImpl.mem (vars_aux.add_ntag ii) md) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i0 igvs1)
      (updateAddAL GVs lc2 i0 igvs2) alpha olc1 olc2
      (IdExtSetImpl.add (vars_aux.add_ntag i0)
        (IdExtSetImpl.add (vars_aux.add_ntag i0) md)))
    (Hneqi1 : i0 <> ii),
    (lookupAL GVs lc1 ii = None /\ lookupAL GVs lc2 ii = None) \/
    (exists gvs1, exists gvs2,
      lookupAL GVs lc1 ii = Some gvs1 /\ lookupAL GVs lc2 ii = Some gvs2 /\
      gv_inject alpha gvs1 gvs2).
Proof.
  intros.
  unfold maydiff_sem in Hmdsem.
  hexploit (Hmdsem (vars_aux.add_ntag ii)).
  repeat (rewrite IdExtSetFacts.add_neq_b;
    [|by intro Hf; elim Hneqi1; inversion Hf]).
  eapply negb_true_iff; done.
  intro Hveq.
  unfold variable_equivalent in Hveq; simpl in Hveq.
  rewrite <- lookupAL_updateAddAL_neq in Hveq; [|by intro Hf; symmetry in Hf].
  rewrite <- lookupAL_updateAddAL_neq in Hveq; [|by intro Hf; symmetry in Hf].
  destruct (lookupAL GVs lc1 ii), (lookupAL GVs lc2 ii); try done.
  - right; exists g; exists g0; done.
  - left; done.
Qed.

Lemma getOperandValue_eq_check_value_implies_injection:
  forall md inv1 inv2 iso1 iso2 v1 v2 lc1 lc2 alpha gmax li1 li2 olc1 olc2 gvs1 gvs2
    mem1 mem2 cfg1 cfg2 i igvs1 igvs2
    (Hnot1: (AtomSetImpl.mem i (vars_aux.used_locals_in_value' v1)) = false)
    (Hnot2: (AtomSetImpl.mem i (vars_aux.used_locals_in_value' v2)) = false)
    (Heql: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hbop1: getOperandValue (CurTargetData cfg1) v1 lc1 (Globals cfg1) = ret gvs1)
    (Hbop2: getOperandValue (CurTargetData cfg2) v2 lc2 (Globals cfg2) = ret gvs2),
    gv_inject alpha gvs1 gvs2.

Proof.
  intros.
  destruct v1, v2; simpl in Hnot1, Hnot2, Hbop1, Hbop2.
  - destruct (id_dec i0 id5) as [|Hneqi1];
    try by subst; rewrite AtomSetFacts.singleton_b in Hnot1;
      unfold AtomSetFacts.eqb in Hnot1; destruct (KeySetFacts.eq_dec id5 id5).
    destruct (id_dec i0 id0) as [|Hneqi2];
    try by subst; rewrite AtomSetFacts.singleton_b in Hnot2;
      unfold AtomSetFacts.eqb in Hnot2; destruct (KeySetFacts.eq_dec id0 id0).
    clear Hnot1 Hnot2.
    unfold eq_check_value in Heql.
    unfold vars_aux.add_ntag_value in Heql.

    repeat rewrite orb_true_iff in Heql; destruct Heql as [[Hbysame|Hbyinv2]|Hbyinv1].

    (* x | x, x \notin md *)
    + apply andb_true_iff in Hbysame; destruct Hbysame as [Heqid Hninmd].
      unfold vars_aux.add_ntag in Heqid.
      destruct (id_ext_dec (id5, ntag_new) (id0, ntag_new)) as [Heqid'|]; [|done];
        clear Heqid; inversion Heqid'; subst; clear Heqid'.
      exploit not_in_maydiff_implies_gv_inject; eauto; intros [[_ Hcontr]|Hisome].
      * rewrite Hbop2 in Hcontr; done.
      * inversion Hisome as [gvs1' [gvs2' [Hret1 [Hret2 Hinj]]]]; clear Hisome.
        rewrite Hbop2 in Hret2; inversion Hret2; subst.
        rewrite Hbop1 in Hret1; inversion Hret1; subst.
        done.

    + apply andb_true_iff in Hbyinv2; destruct Hbyinv2 as [Hninmd Hininv2].
      rewrite orb_true_iff in Hininv2; destruct Hininv2 as [Hininv2|Hininv2].

      * exploit not_in_maydiff_implies_gv_inject; eauto; intros [[Hcontr _]|Hisome];
        try by rewrite Hbop1 in Hcontr.
        inversion Hisome as [gvs1' [gvs2' [Hret1 [Hret2 Hinj]]]]; clear Hisome.
        rewrite Hbop1 in Hret1; inversion Hret1; subst; clear Hret1.

        destruct inv2 as [inv_reg2 inv_heap2 inv_nreg2]; simpl in *.
        destruct Hinvsem as [_ [[Hregssem _] _]]; simpl in Hregssem.
        unfold eqs_eq_reg_sem in Hregssem.
        hexploit Hregssem; try eapply Hininv2; intro Hregsem; clear Hregssem.
        inversion Hregsem; subst; clear Hregsem.
        simpl in Hlookup.
        rewrite <- lookupAL_updateAddAL_neq in Hlookup; [|by intro Hf; symmetry in Hf].

        inv Hrhs.
        simpl in H0.
        rewrite <- lookupAL_updateAddAL_neq in H0; try eauto.
        apply eq_gvs_implies_setoid_eq in Heqgvs; subst.
        rewrite Hret2 in Hlookup; inv Hlookup.
        rewrite H0 in Hbop2; inv Hbop2.
        done.

      * exploit not_in_maydiff_implies_gv_inject; eauto; intros [[Hcontr _]|Hisome];
        try by rewrite Hbop1 in Hcontr.
        inversion Hisome as [gvs1' [gvs2' [Hret1 [Hret2 Hinj]]]]; clear Hisome.
        rewrite Hbop1 in Hret1; inversion Hret1; subst; clear Hret1.

        destruct inv2 as [inv_reg2 inv_heap2 inv_nreg2]; simpl in *.
        destruct Hinvsem as [_ [[Hregssem _] _]]; simpl in Hregssem.
        unfold eqs_eq_reg_sem in Hregssem.
        hexploit Hregssem; try eapply Hininv2; intro Hregsem; clear Hregssem.
        inversion Hregsem; subst; clear Hregsem.
        simpl in Hlookup.
        rewrite <- lookupAL_updateAddAL_neq in Hlookup; [|by intro Hf; symmetry in Hf].

        inv Hrhs.
        simpl in H0.
        rewrite <- lookupAL_updateAddAL_neq in H0; try eauto.
        apply eq_gvs_implies_setoid_eq in Heqgvs; subst.
        rewrite H0 in Hret2; inv Hret2.
        rewrite Hlookup in Hbop2; inv Hbop2.
        done.

    + apply andb_true_iff in Hbyinv1; destruct Hbyinv1 as [Hninmd Hininv1].
      rewrite orb_true_iff in Hininv1; destruct Hininv1 as [Hininv1|Hininv1].

      * exploit not_in_maydiff_implies_gv_inject; eauto; intros [[_ Hcontr]|Hisome];
        try by rewrite Hbop2 in Hcontr.
        inversion Hisome as [gvs1' [gvs2' [Hret1 [Hret2 Hinj]]]]; clear Hisome.
        rewrite Hbop2 in Hret2; inversion Hret2; subst; clear Hret2.

        destruct inv1 as [inv_reg1 inv_heap1 inv_nreg1]; simpl in *.
        destruct Hinvsem as [[Hregssem _] _]; simpl in Hregssem.
        unfold eqs_eq_reg_sem in Hregssem.
        hexploit Hregssem; try eapply Hininv1; intro Hregsem; clear Hregssem.
        inversion Hregsem; subst; clear Hregsem.
        simpl in Hlookup.
        rewrite <- lookupAL_updateAddAL_neq in Hlookup; [|by intro Hf; symmetry in Hf].

        inv Hrhs.
        simpl in H0.
        rewrite <- lookupAL_updateAddAL_neq in H0; try eauto.
        apply eq_gvs_implies_setoid_eq in Heqgvs; subst.
        rewrite Hlookup in Hbop1; inv Hbop1.
        rewrite H0 in Hret1; inv Hret1.
        done.

      * exploit not_in_maydiff_implies_gv_inject; eauto; intros [[_ Hcontr]|Hisome];
        try by rewrite Hbop2 in Hcontr.
        inversion Hisome as [gvs1' [gvs2' [Hret1 [Hret2 Hinj]]]]; clear Hisome.
        rewrite Hbop2 in Hret2; inversion Hret2; subst; clear Hret2.

        destruct inv1 as [inv_reg1 inv_heap1 inv_nreg1]; simpl in *.
        destruct Hinvsem as [[Hregssem _] _]; simpl in Hregssem.
        unfold eqs_eq_reg_sem in Hregssem.
        hexploit Hregssem; try eapply Hininv1; intro Hregsem; clear Hregssem.
        inversion Hregsem; subst; clear Hregsem.
        simpl in Hlookup.
        rewrite <- lookupAL_updateAddAL_neq in Hlookup; [|by intro Hf; symmetry in Hf].

        inv Hrhs.
        simpl in H0.
        rewrite <- lookupAL_updateAddAL_neq in H0; try eauto.
        apply eq_gvs_implies_setoid_eq in Heqgvs; subst.
        rewrite H0 in Hbop1; inv Hbop1.
        rewrite Hlookup in Hret1; inv Hret1.
        done.

  - destruct (id_dec i0 id5) as [|Hneqi1];
    try by subst; rewrite AtomSetFacts.singleton_b in Hnot1;
      unfold AtomSetFacts.eqb in Hnot1; destruct (KeySetFacts.eq_dec id5 id5).
    clear Hnot1 Hnot2.
    unfold eq_check_value, vars_aux.add_ntag_value in Heql.

    destruct inv1 as [inv_reg1 inv_heap1 inv_nreg1]; simpl in *.
    destruct Hinvsem as [[Hregssem _] _]; simpl in Hregssem.
    unfold eqs_eq_reg_sem in Hregssem.
    hexploit Hregssem; try eapply Heql; intro Hregsem; clear Hregssem.
    inversion Hregsem; subst; clear Hregsem.

    simpl in Hlookup; rewrite <- lookupAL_updateAddAL_neq in Hlookup; eauto.
    rewrite Hbop1 in Hlookup; inv Hlookup.
    apply eq_gvs_implies_setoid_eq in Heqgvs; subst gvs.
    inv Hrhs.
    simpl in H0.
    inv Hgequiv.
    rewrite <- Hgl2, <- Htd in Hbop2.
    rewrite H0 in Hbop2; inv Hbop2.
    eapply LLVMtyping_rules.const2GV_refl; eauto.

  - destruct (id_dec i0 id5) as [|Hneqi1];
    try by subst; rewrite AtomSetFacts.singleton_b in Hnot2;
      unfold AtomSetFacts.eqb in Hnot2; destruct (KeySetFacts.eq_dec id5 id5).
    clear Hnot1 Hnot2.
    unfold eq_check_value, vars_aux.add_ntag_value in Heql.

    destruct inv2 as [inv_reg2 inv_heap2 inv_nreg2]; simpl in *.
    destruct Hinvsem as [_ [[Hregssem _] _]]; simpl in Hregssem.
    unfold eqs_eq_reg_sem in Hregssem.
    hexploit Hregssem; try eapply Heql; intro Hregsem; clear Hregssem.
    inversion Hregsem; subst; clear Hregsem.

    simpl in Hlookup; rewrite <- lookupAL_updateAddAL_neq in Hlookup; eauto.
    rewrite Hbop2 in Hlookup; inv Hlookup.
    apply eq_gvs_implies_setoid_eq in Heqgvs; subst gvs.
    inv Hrhs.
    simpl in H0.
    inv Hgequiv.
    rewrite <- Hgl2, <- Htd in H0.
    rewrite H0 in Hbop1; inv Hbop1.
    eapply LLVMtyping_rules.const2GV_refl; eauto.

  - simpl in Heql; unfold eq_check_value in Heql.
    repeat rewrite orb_false_r in Heql.
    destruct (const_dec const5 const0); [|done]; subst; simpl in *.
    inv Hgequiv.
    rewrite <- Hgl2, <- Htd in Hbop2.
    rewrite Hbop1 in Hbop2; inv Hbop2.
    eapply LLVMtyping_rules.const2GV_refl; eauto.
Qed.

Ltac eq_check_value_tac :=
  intros; unfold BOP, FBOP, TRUNC, EXT, CAST, ICMP, FCMP in *;
    repeat match goal with
             | [H: context[match getOperandValue ?td ?lv ?lc ?gl with
                             | ret _ => _
                             | merror => _
                           end] |- _] =>
             let ov := fresh "ov" in
               remember (getOperandValue td lv lc gl) as ov; destruct ov; try done
             | [H: self_use_check _ = true |- _] =>
               let Hnilv := fresh "Hniv" in
                 let Hnirv := fresh "Hniv" in
                   unfold self_use_check, self_use_check' in H; simpl in H;
                     try rewrite AtomSetFacts.union_b in H;
                       apply negb_true_iff in H;
                         try (apply orb_false_iff in H; inversion H as [Hnilv Hnirv];
                           clear H)
           end.

Lemma values2GVs_eq_check_value_implies_injection:
  forall md inv1 inv2 lsv1 lsv2 lc1 lc2 alpha gmax li1 li2 olc1 olc2 gvs1 gvs2
    mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hnot1: (AtomSetImpl.mem i (vars_aux.used_locals_in_lsv' lsv1)) = false)
    (Hnot2: (AtomSetImpl.mem i (vars_aux.used_locals_in_lsv' lsv2)) = false)
    (Heql: eq_check_lsv md inv1 inv2
      (vars_aux.add_ntag_lsv lsv1) (vars_aux.add_ntag_lsv lsv2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hlsv1: values2GVs (CurTargetData cfg1) lsv1 lc1 (Globals cfg1) = ret gvs1)
    (Hlsv1: values2GVs (CurTargetData cfg2) lsv2 lc2 (Globals cfg2) = ret gvs2),
    gvs_inject alpha gvs1 gvs2.
Proof.
  intros md inv1 inv2.
  induction lsv1; intros.

  Case "induction: nil-case".
  destruct lsv2; [|done].
  by simpl in Hlsv0, Hlsv1; inv Hlsv0; inv Hlsv1.

  Case "induction: cons-case".
  destruct lsv2; [done|].
  simpl in Hnot1, Hnot2.
  rewrite AtomSetFacts.union_b in Hnot1, Hnot2.
  apply orb_false_iff in Hnot1; apply orb_false_iff in Hnot2.
  destruct Hnot1 as [Hnv1 Hnlsv1], Hnot2 as [Hnv2 Hnlsv2].

  destruct a as [sz1 v1], p as [sz2 v2].
  simpl in Hnv1, Hnv2, Heql.
  apply andb_true_iff in Heql; destruct Heql as [Heql Helsv].
  apply andb_true_iff in Heql; destruct Heql as [Hesz Hev].
  destruct (sz_dec sz1 sz2); [|done]; subst; clear Hesz.

  simpl in Hlsv0, Hlsv1.
  remember (getOperandValue (CurTargetData cfg1) v1 lc1 (Globals cfg1)) as ov1.
  destruct ov1; [|done].
  remember (getOperandValue (CurTargetData cfg2) v2 lc2 (Globals cfg2)) as ov2.
  destruct ov2; [|done].
  exploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hnv1. - apply Hnv2. - apply Hev. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  - intros Hvinj.

  remember (values2GVs (CurTargetData cfg1) lsv1 lc1 (Globals cfg1)) as olsv1.
  destruct olsv1; [|done].
  remember (values2GVs (CurTargetData cfg2) lsv2 lc2 (Globals cfg2)) as olsv2.
  destruct olsv2; [|done].
  inv Hlsv1; inv Hlsv0.

  simpl; split; [done|].
  eapply IHlsv1; eauto.
Qed.

Lemma malloc_preserves_isolated_sem_2:
  forall td iso olc lc mem mem' li tsz gn aln mb i
    (Hli: Forall (fun b => b < Mem.nextblock mem) li)
    (Hiniso: IdExtSetImpl.mem (i, ntag_new) iso = true)
    (Hiso: isolated_sem td olc lc li iso)
    (Hmalloc: malloc td mem tsz gn aln = ret (mem', mb)),
    isolated_sem td olc (updateAddAL GVs lc i (blk2GV td mb)) (mb::li) iso.
Proof.
  intros.
  exploit memory_props.MemProps.malloc_result; eauto; intro Hmb.
  exploit memory_props.MemProps.nextblock_malloc; eauto; intro Hn.
  unfold isolated_sem, IdExtSetImpl.For_all in *; intros.
  exploit Hiso; eauto; intro Hbrd; clear Hiso.

  destruct (id_ext_dec (i0, ntag_new) x).

  - subst x; clear Hbrd. right.
    exists (blk2GV td mb); split; [by simpl; rewrite lookupAL_updateAddAL_eq; eauto|].
    by left.

  - destruct Hbrd as [Hndef|Hdef].
    + left; simpl.
      destruct x as [x [|]]; simpl in *; [done|].
      rewrite <-lookupAL_updateAddAL_neq; eauto.
      intro Hcontr; subst; elim n; done.
    + right; destruct Hdef as [gvp [Hlookup Hptr]].
      exists gvp; split.
      * destruct x as [x [|]]; simpl in *; [done|].
        rewrite <-lookupAL_updateAddAL_neq; eauto.
        intro Hcontr; subst; elim n; done.
      * remember (GV2ptr td (getPointerSize td) gvp) as gvpp; destruct gvpp; try done.
        destruct v; try done.
        by right.
Qed.

Lemma malloc_left_preserves_valid_allocas:
  forall td mem1 mem2 mem1' als1 als2 tsz gn1 aln mb1
    (Hmalloc1: malloc td mem1 tsz gn1 aln = ret (mem1', mb1))
    (Hvals: valid_allocas mem1 mem2 als1 als2),
    valid_allocas mem1' mem2 (mb1::als1) als2.
Proof.
  intros.
  exploit memory_props.MemProps.malloc_result;
  try eapply Hmalloc1; eauto; intro Hmb.
  exploit memory_props.MemProps.nextblock_malloc;
  try eapply Hmalloc1; eauto; intro Hn.
  destruct Hvals as [Hvl [Hvr [Hndl Hndr]]]; rr; splits; try done.
  - econstructor.
    + subst; rewrite <- Hn; omega.
    + eapply Forall_impl; try eapply Hvl.
      intros a Hprev; simpl; simpl in Hprev.
      rewrite <- Hn; omega.
  - econstructor; [|done].
    intro Hcontr; rewrite Hmb in Hcontr; clear -Hcontr Hvl.
    induction als1; [done|].
    simpl in Hcontr; destruct Hcontr.
    + subst; inv Hvl; omega.
    + eapply IHals1; eauto.
      inv Hvl; done.
Qed.

Lemma malloc_right_preserves_valid_allocas:
  forall td mem1 mem2 mem2' als1 als2 tsz gn1 aln mb2
    (Hmalloc2: malloc td mem2 tsz gn1 aln = ret (mem2', mb2))
    (Hvals: valid_allocas mem1 mem2 als1 als2),
    valid_allocas mem1 mem2' als1 (mb2::als2).
Proof.
  intros.
  exploit memory_props.MemProps.malloc_result; try eapply Hmalloc2; eauto; intro Hmb.
  exploit memory_props.MemProps.nextblock_malloc; try eapply Hmalloc2; eauto; intro Hn.
  destruct Hvals as [Hvl [Hvr [Hndl Hndr]]]; rr; splits; try done.
  - apply Forall_forall; intros; destruct H.
    + subst; omega.
    + rewrite <-Hn; rewrite Forall_forall in Hvr.
      exploit Hvr; eauto; omega.
  - econstructor; [|done].
    intro Hcontr; rewrite Forall_forall in Hvr; exploit Hvr; eauto.
    rewrite Hmb; omega.
Qed.

Lemma malloc_preserves_valid_allocas_1:
  forall td mem1 mem2 mem1' mem2' als1 als2 tsz gn1 gn2 aln mb1 mb2 alpha
    (Hmalloc1: malloc td mem1 tsz gn1 aln = ret (mem1', mb1))
    (Hmalloc2: malloc td mem2 tsz gn2 aln = ret (mem2', mb2))
    (Hgn: gv_inject alpha gn1 gn2)
    (Hvals: valid_allocas mem1 mem2 als1 als2),
    valid_allocas mem1' mem2' als1 als2.
Proof.
  intros; destruct Hvals as [Hvl [Hvr [Hndl Hndr]]]; rr; splits; try done.
  - eapply Forall_impl; try eapply Hvl.
    intros a Hprev; simpl; simpl in Hprev.
    exploit memory_props.MemProps.nextblock_malloc; try eapply Hmalloc1; eauto;
      intro Hn.
    rewrite <- Hn; omega.
  - eapply Forall_impl; try eapply Hvr.
    intros a Hprev; simpl; simpl in Hprev.
    exploit memory_props.MemProps.nextblock_malloc; try eapply Hmalloc2; eauto;
      intro Hn.
    rewrite <- Hn; omega.
Qed.

Lemma malloc_preserves_valid_allocas_2:
  forall td mem1 mem2 mem1' mem2' als1 als2 tsz gn1 gn2 aln mb1 mb2 alpha
    (Hmalloc1: malloc td mem1 tsz gn1 aln = ret (mem1', mb1))
    (Hmalloc2: malloc td mem2 tsz gn2 aln = ret (mem2', mb2))
    (Hgn: gv_inject alpha gn1 gn2)
    (Hvals: valid_allocas mem1 mem2 als1 als2),
    valid_allocas mem1' mem2' (mb1::als1) (mb2::als2).
Proof.
  intros.
  eapply malloc_left_preserves_valid_allocas; eauto.
  exploit memory_props.MemProps.malloc_result;
  try eapply Hmalloc2; eauto; intro Hmb.
  exploit memory_props.MemProps.nextblock_malloc;
  try eapply Hmalloc2; eauto; intro Hn.

  destruct Hvals as [Hvl [Hvr [Hndl Hndr]]]; rr; splits; try done.
  - econstructor.
    + subst; rewrite <- Hn; omega.
    + eapply Forall_impl; try eapply Hvr.
      intros a Hprev; simpl; simpl in Hprev.
      rewrite <- Hn; omega.
  - econstructor; [|done].
    intro Hcontr; rewrite Forall_forall in Hvr; exploit Hvr; eauto.
    rewrite Hmb; omega.
Qed.

Lemma malloc_preserves_isolated_heap_freeable:
  forall mem mem' b mb sz ii
    (Hbii: In b ii)
    (Hiifact: Forall (fun b => b < Mem.nextblock mem) ii)
    (Hfree: let (l, h) := Mem.bounds mem b in Mem.free mem b l h <> merror)
    (Hmalloc: Mem.alloc mem 0 sz = (mem', mb)),
    let (l, h) := Mem.bounds mem' b in Mem.free mem' b l h <> merror.
Proof.
  intros.
  exploit Mem.alloc_result; eauto; intro Hmb; subst mb.
  assert (Hneq: b <> Mem.nextblock mem0).
  { rewrite Forall_forall in Hiifact; exploit Hiifact; eauto; intro Hres.
    intro Hcontr; subst; omega.
  }
  exploit Mem.bounds_alloc_other; eauto.
  intro Hbounds; rewrite Hbounds; clear Hbounds.

  destruct (Mem.bounds mem0 b).
  intro Hcontr; elim Hfree; clear Hfree.
  Local Transparent Mem.free.
  unfold Mem.free in *.
  remember (Mem.range_perm_dec mem' b z z0 Freeable) as perm';
    destruct perm'; [done|]; clear Hcontr.

  assert (Hperm: ~ Mem.range_perm mem0 b z z0 Freeable).
  { clear Heqperm'.
    intro Hcontr; elim n; clear n.
    unfold Mem.range_perm in *; intros.
    exploit Hcontr; eauto; intro Hperm.
    eapply Mem.perm_alloc_1; eauto.
  }

  destruct (Mem.range_perm_dec mem0 b z z0); done.
  Global Opaque Mem.free.

Qed.

Lemma malloc_implies_freeable:
  forall mem mem' mb sz
    (Hmalloc: Mem.alloc mem 0 sz = (mem', mb)),
    let (l, h) := Mem.bounds mem' mb in Mem.free mem' mb l h <> merror.
Proof.
  intros.
  exploit Mem.bounds_alloc_same; eauto; intro Hbounds; rewrite Hbounds.
  Local Transparent Mem.free.
  unfold Mem.free in *.

  assert (Hperm: Mem.range_perm mem' mb 0 sz0 Freeable).
  { unfold Mem.range_perm; intros.
    eapply Mem.perm_alloc_2; eauto.
  }
  destruct (Mem.range_perm_dec mem' mb 0 sz0 Freeable); done.
  Global Opaque Mem.free.
Qed.

Lemma malloc_preserves_valid_memories:
  forall td mem1 mem2 mem1' mem2' tsz gn1 gn2 aln mb1 mb2 li1 pi1 li2 pi2 alpha gmax
    (Hmalloc1: malloc td mem1 tsz gn1 aln = ret (mem1', mb1))
    (Hmalloc2: malloc td mem2 tsz gn2 aln = ret (mem2', mb2))
    (Hgn: gv_inject alpha gn1 gn2)
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2),
    exists alpha',
      (inject_incr' alpha alpha' li1 pi1 li2 pi2) /\
      (alpha_incr_both alpha' mem1 mem2) /\
      (valid_memories alpha' gmax mem1' mem2' li1 pi1 li2 pi2).
Proof.
  intros; inv Hvmem; inv Hwf.
  exploit memory_props.MemProps.malloc_result; try eapply Hmalloc1; eauto.
  exploit memory_props.MemProps.malloc_result; try eapply Hmalloc2; eauto.
  exploit memory_props.MemProps.nextblock_malloc; try eapply Hmalloc1; eauto.
  exploit memory_props.MemProps.nextblock_malloc; try eapply Hmalloc2; eauto.
  intros Hn2 Hn1 Hmb2 Hmb1.

  remember (fun blk => if (Z_eq_dec blk mb1) then ret (mb2, 0%Z) else alpha blk)
  as alpha'.
  exists alpha'.
  assert (Hincr: inject_incr' alpha alpha' li1 pi1 li2 pi2).
  { rewrite Heqalpha' in *; unfold inject_incr'; splits.
    + unfold inject_incr; intros b b' dt Hab.
      rewrite <- Hab.
      destruct (Z_eq_dec b mb1); [|done].
      elimtype False; subst.
      exploit Hmap1; try by instantiate (1:=Mem.nextblock mem1); omega.
      subst; rewrite Hab; done.
    + intros.
      destruct (Z_eq_dec b mb1); [|done].
      elimtype False; subst.
      rewrite Forall_forall in Hvli1.
      pose (Hvli1 _ H); omega.
    + intros.
      destruct (Z_eq_dec b mb1); [|done].
      elimtype False; subst.
      rewrite Forall_forall in Hvpi1.
      pose (Hvpi1 _ H); omega.
    + intros.
      destruct (Z_eq_dec sb mb1); [|by eapply Hli2none].
      intro Hcontr; inv Hcontr.
      rewrite Forall_forall in Hvli0.
      pose (Hvli0 _ H); rewrite H2 in *; omega.
    + intros.
      destruct (Z_eq_dec sb mb1); [|by eapply Hpi2none].
      intro Hcontr; inv Hcontr.
      rewrite Forall_forall in Hvpi0.
      pose (Hvpi0 _ H); rewrite H2 in *; omega.
  }

  splits; try done.
  Case "1. alpha_incr_both".
  subst; unfold alpha_incr_both.
  by destruct (Z_eq_dec (Mem.nextblock mem1) (Mem.nextblock mem1)).

  Case "2. valid_memories".
  unfold malloc in Hmalloc1, Hmalloc2.
  apply malloc_inv in Hmalloc1. apply malloc_inv in Hmalloc2.

  exploit simulation__eq__GV2int; eauto. intro Hzeq.
  erewrite Hzeq in Hmalloc1.
  remember (match GV2int td Size.ThirtyTwo gn2 with
              | ret n => Size.to_Z tsz * n
              | merror => 0
            end) as z.
  econs; try done.

  (* assert (HeqR1: Mem.alloc mem1 0 (Size.to_Z tsz * z) = (mem1', mb1)) *)

  (* remember (GV2int td Size.ThirtyTwo gn1) as gn1i; destruct gn1i; [|done]. *)
  (* remember (GV2int td Size.ThirtyTwo gn2) as gn2i; destruct gn2i; [|done]. *)
  (* destruct (zlt 0 (Size.to_Z tsz * z)); [|done]. *)
  (* destruct (zlt 0 (Size.to_Z tsz * z0)); [|done]. *)

  (* assert (Hzeq: z = z0). *)
  (* - assert (Hrzeq: ret z = ret z0). *)
  (*   + rewrite Heqgn1i, Heqgn2i. *)
  (*     eapply simulation__eq__GV2int; eauto. *)
  (*   by inv Hrzeq. *)
  (* subst z0. *)
  (* assert (HeqR1: Mem.alloc mem1 0 (Size.to_Z tsz * z) = (mem1', mb1)). *)
  (* - by remember (mem1', mb1) as mm1; inv Hmalloc1. *)
  (* assert (HeqR2: Mem.alloc mem2 0 (Size.to_Z tsz * z) = (mem2', mb2)). *)
  (* - by remember (mem2', mb2) as mm2; inv Hmalloc2. *)
  (* clear Hmalloc1 Hmalloc2. *)

  (* econstructor; try done. *)

  (* copied Vellvm's proof in genericvalues_inject.v *)
  SCase "2.1. mem_inj".
  inversion Hmemi; econstructor.

  SSCase "2.1.1. valid_access".
  intros b1 b2 d c ofs p J1 J2. 
  rewrite Heqalpha' in J1; simpl in J1.
  destruct (Z_eq_dec b1 mb1) as [Hbeq|].

  - rewrite Hbeq in *; clear Hbeq; inversion J1 as [Hbeq]; rewrite <- Hbeq.
    destruct J2 as [J21 J22].
    assert (Hineq: 0 <= ofs /\ ofs + size_chunk c <= z).
    + destruct (Z_le_dec 0 ofs).
      * destruct (Z_le_dec (ofs + size_chunk c) z); auto.
        apply Mem.perm_alloc_3 with (ofs:=ofs+size_chunk c-1) (p:=p) in
          Hmalloc1; auto with zarith.
        unfold Mem.range_perm in J21.
        assert (ofs <= ofs + size_chunk c - 1 < ofs + size_chunk c) as J.
          assert (J':=@Memdata.size_chunk_pos c).
          auto with zarith.
        apply J21 in J.
        contradict J; auto.
        apply Mem.perm_alloc_3 with (ofs:=ofs) (p:=p) in Hmalloc1;
          auto with zarith.
        unfold Mem.range_perm in J21.
        assert (ofs <= ofs < ofs + size_chunk c) as J.
          assert (J':=@Memdata.size_chunk_pos c).
          auto with zarith.
        apply J21 in J.
        contradict J; auto.

      * apply Mem.valid_access_alloc_same with (chunk:=c)(ofs:=ofs+0) in Hmalloc2;
          auto with zarith.
        eapply Mem.valid_access_implies; eauto using perm_F_any.

  - eapply Mem.valid_access_alloc_other; eauto.
    eapply mi_access; eauto.
    exploit Mem.valid_access_alloc_inv; try eapply Hmalloc1; try eapply J2.
    unfold eq_block, zeq.
    destruct (Z_eq_dec b1 mb1); done.

  SSCase "2.1.2. mem_contents".
  intros b1 ofs b2 d J1 J2.
  rewrite Heqalpha' in *.

  Transparent Mem.alloc.
  symmetry in Hmalloc1; injection Hmalloc1; intros NEXT MEM.
  symmetry in Hmalloc2; injection Hmalloc2. intros NEXT2 MEM2.
  destruct mem2. destruct mem2'. destruct mem1. destruct mem1'.
  inv MEM. inv MEM2. clear Hmalloc1 Hmalloc2.
  simpl in *.
  unfold Mem.perm in *. simpl in *.
  clear maxaddress_pos0 conversion_props0 maxaddress_pos2 conversion_props2.
  unfold update; destruct (zeq b1 nextblock1); subst; inv J1.

  SSSCase "2.1.2.1. b1 = nextblock1".
  destruct (Z_eq_dec nextblock1 nextblock1); [|done]; inv H0; clear e.
  destruct (zeq b2 b2) as [e|n]; [|done].
  apply MoreMem.memval_inject_undef.

  SSSCase "b1<>mb".
  destruct (zeq b2 nextblock); subst.
  - simpl in *.
    destruct (Z_eq_dec b1 nextblock1); [done|].
    apply Hmap2 in H0.
    contradict H0; auto with zarith.
  - destruct (Z_eq_dec b1 nextblock1); [done|].
    destruct Hincr as [Hincr He].
    apply MoreMem.memval_inject_incr with (f:=alpha); auto.
    apply mi_memval; auto.
    clear - J2 n.
    unfold update in J2.
    by destruct (zeq b1 nextblock1).

  SCase "2.2. wf_sb_mi".
  rewrite Heqalpha' in *.
  econstructor; intros.

  SSCase "2.2.1. no_overlap".
  clear -Hno_overlap Hmalloc2 Hmap2.
  unfold MoreMem.meminj_no_overlap in *.
  intros.
  destruct (Z_eq_dec b1 mb1); destruct (Z_eq_dec b2 mb1); subst.
  - by elim H.
  - inv H0; apply Hmap2 in H1.
    apply Mem.alloc_result in Hmalloc2; subst; intro Hcontr.
    rewrite Hcontr in H1; zauto.
  - inv H1; apply Hmap2 in H0.
    apply Mem.alloc_result in Hmalloc2; subst; intro Hcontr.
    rewrite Hcontr in H0; zauto.
  - eapply Hno_overlap; [apply H|apply H0|apply H1].

  SSCase "2.2.2. nullptr".
  destruct (Z_eq_dec Mem.nullptr mb1); [|done]; subst.
  apply Mem.alloc_result in Hmalloc1.
  hexploit Mem.nextblock_pos.
  instantiate (1:=mem1); intro Hcontr.
  rewrite <- e in Hcontr; unfold Mem.nullptr in Hcontr.
  contradict Hcontr; zauto.

  SSCase "2.2.3. map1".
  pose Hmalloc1 as J'.
  apply Mem.alloc_result in J'.
  apply Mem.nextblock_alloc in Hmalloc1.
  rewrite Hmalloc1 in H.
  destruct (Z_eq_dec b mb1); subst; zeauto.
  contradict H; zauto.

  SSCase "2.2.4. map2".
  pose Hmalloc2 as J'.
  apply Mem.nextblock_alloc in J'; rewrite J'.
  destruct (Z_eq_dec b1 mb1); subst; zeauto.
  inv H; zauto.

  SSCase "2.2.5. freeblocks".
  destruct (Z_eq_dec b mb1); subst.
  - apply Mem.valid_new_block in Hmalloc1.
    contradict Hmalloc1; auto.
  - apply mi_freeblocks; intro Hcontr; apply H.
    eapply Mem.valid_block_alloc; eauto.

  SSCase "2.2.6. mappedblocks".
  destruct (Z_eq_dec b mb1); subst.
  - inv H; apply Mem.valid_new_block in Hmalloc2; auto.
  - eapply Mem.valid_block_alloc; eauto.

  SSCase "2.2.7. range_block".
  rr; intros; destruct (Z_eq_dec b mb1); subst.
  - inv H; done.
  - eapply mi_range_block; eauto.

  SSCase "2.2.8. bounds".
  erewrite Mem.bounds_alloc; eauto.
  erewrite Mem.bounds_alloc with (m2:=mem2'); eauto.
  unfold eq_block, zeq.
  destruct (Z_eq_dec b mb1); subst.
  - inv H; destruct (Z_eq_dec (Mem.nextblock mem2) (Mem.nextblock mem2)); subst; auto.
    contradict n; auto.
  - destruct (Z_eq_dec b' (Mem.nextblock mem2)); subst; eauto.
    apply Hmap2 in H.
    contradict H; zauto.

  SSCase "2.2.9. globals".
  destruct (Z_eq_dec b mb1); subst; eauto.
  pose H as J'.
  apply mi_globals in J'.
  destruct (Mem.valid_block_dec mem1 (Mem.nextblock mem1)).
  - apply Mem.fresh_block_alloc in Hmalloc1.
    contradict Hmalloc1; auto.
  - apply mi_freeblocks in n.
    rewrite n in J'; done.

  SCase "2.3. li1 constraint".
  unfold inject_incr' in Hincr; destruct Hincr as [_ [Hli Hpi]].
  intros; pose (Hli1none _ H) as Hbrd.
  eapply Hli; eauto.

  SCase "2.4. li2 constraint".
  unfold inject_incr' in Hincr; destruct Hincr as [_ [_ [_ [Hli _]]]].
  intros; hexploit Hli; eauto.

  SCase "2.5. pi1 constraint".
  unfold inject_incr' in Hincr; destruct Hincr as [_ [Hli Hpi]].
  intros; pose (Hpi1none _ H) as Hbrd.
  eapply Hpi; eauto.

  SCase "2.6. pi2 constraint".
  unfold inject_incr' in Hincr; destruct Hincr as [_ [_ [_ [_ Hpi]]]].
  intros; hexploit Hpi; eauto.

  SCase "2.7. li1 constraint II".
  intros; exploit Hli1free; eauto; intro Hres.
  eapply malloc_preserves_isolated_heap_freeable; eauto.

  SCase "2.8. li2 constraint II".
  intros; exploit Hli2free; eauto; intro Hres.
  eapply malloc_preserves_isolated_heap_freeable; eauto.

  SCase "2.9. pi1 constraint II".
  intros; exploit Hpi1free; eauto; intro Hres.
  eapply malloc_preserves_isolated_heap_freeable; eauto.

  SCase "2.10. pi2 constraint II".
  intros; exploit Hpi2free; eauto; intro Hres.
  eapply malloc_preserves_isolated_heap_freeable; eauto.

  SCase "2.11. li1 constraint III".
  eapply Forall_impl; try eapply Hvli1; intros a Hprev.
  simpl in Hprev; rewrite <- Hn1; omega.

  SCase" 2.12. pi1 constraint III".
  eapply Forall_impl; try eapply Hvpi1; intros a Hprev.
  simpl in Hprev; rewrite <- Hn1; omega.

  SCase "2.13. li2 constraint III".
  eapply Forall_impl; try eapply Hvli0; intros a Hprev.
  simpl in Hprev; rewrite <- Hn2; omega.

  SCase "2.14. pi2 constraint III".
  eapply Forall_impl; try eapply Hvpi0; intros a Hprev.
  simpl in Hprev; rewrite <- Hn2; omega.

  auto.
  auto.
Qed.

Lemma malloc_left_preserves_valid_memories:
  forall td mem1 mem2 mem1' tsz gn1 aln mb1 li1 pi1 li2 pi2 alpha gmax
    (Hmalloc1: malloc td mem1 tsz gn1 aln = ret (mem1', mb1))
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2),
    exists alpha',
      (inject_incr' alpha alpha' li1 pi1 li2 pi2) /\
      (valid_memories alpha' gmax mem1' mem2 (mb1::li1) pi1 li2 pi2).
Proof.
  intros; inv Hvmem; inv Hwf.
  exploit memory_props.MemProps.malloc_result; try eapply Hmalloc1; eauto.
  exploit memory_props.MemProps.nextblock_malloc; try eapply Hmalloc1; eauto.
  intros Hn1 Hmb1.

  exists alpha.
  assert (Hincr: inject_incr' alpha alpha li1 pi1 li2 pi2)
    by (unfold inject_incr'; splits; done).

  splits; try done.

  Case "valid_memories".
  unfold malloc in Hmalloc1.
  apply malloc_inv in Hmalloc1.
  remember (match GV2int td Size.ThirtyTwo gn1 with
              | ret n => Size.to_Z tsz * n
              | merror => 0
            end) as z.
  (* remember (GV2int td Size.ThirtyTwo gn1) as gn1i; destruct gn1i; [|done]. *)
  (* destruct (zlt 0 z); [|done].   *)
  (* assert (Hmalloc1: Mem.alloc mem1 0 z = (mem1', mb1)). *)
  (* - by remember (mem1', mb1) as mm1; inv Hmalloc1. *)

  econstructor; try done.

  SCase "1. mem_inj".
  inversion Hmemi; econstructor.

  SSCase "1.1. valid_access".
  intros; eapply mi_access; eauto.
  exploit Mem.valid_access_alloc_inv; eauto.
  unfold eq_block, zeq.
  destruct (Z_eq_dec b1 mb1); [|done].
  elimtype False; subst b1.
  exploit Hmap1.
  instantiate (1:=Mem.nextblock mem1); zauto.
  intro Hcontr; rewrite Hmb1 in H; rewrite H in Hcontr; done.

  SSCase "1.2. mem_contents".
  intros.
  erewrite <- Mem.alloc_mem_contents; eauto; unfold update, zeq.
  exploit Mem.perm_alloc_inv; eauto; rewrite Hmb1; unfold zeq.
  destruct (Z_eq_dec b1 (Mem.nextblock mem1)).
  - rewrite e in H.
    exploit Hmap1. instantiate (1:=Mem.nextblock mem1); zauto. intro Hcontr.
    rewrite H in Hcontr; done.
  - eapply mi_memval; eauto.

  SCase "2. wf_sb_mi".
  econstructor; try done; intros.

  SSCase "2.1. map1".
  eapply Hmap1; eauto; rewrite <- Hn1 in H; zauto.

  SSCase "2.2. freeblocks".
  eapply mi_freeblocks; eauto.
  unfold Mem.valid_block in *; intro Hcontr; elim H.
  rewrite <- Hn1; zauto.

  SSCase "2.3. bounds".
  erewrite <- mi_bounds; eauto.
  exploit Mem.bounds_alloc; eauto.
  instantiate (1:=b); intro Hb.
  unfold eq_block, zeq in Hb.
  destruct (Z_eq_dec b mb1); [|done].
  elimtype False; subst b.
  exploit Hmap1.
  instantiate (1:=Mem.nextblock mem1); zauto.
  intro Hcontr; rewrite Hmb1 in H; rewrite H in Hcontr; done.

  SCase "3. li1 constraint".
  intros; inv H.
  - rewrite <- H0; apply Hmap1; zauto.
  - eapply Hli1none; eauto.

  SCase "4. li1 freeable".
  intros b Hbin; simpl in Hbin.
  destruct Hbin as [Hbeq|Hbin].

  - subst; rewrite Hbeq in Hmalloc1.
    eapply malloc_implies_freeable; eauto.
  - intros; exploit Hli1free; eauto; intro Hres.
    eapply malloc_preserves_isolated_heap_freeable; eauto.

  SCase "5. pi1 freeable".
  intros; exploit Hpi1free; eauto; intro Hres.
  eapply malloc_preserves_isolated_heap_freeable; eauto.

  SCase "6. li1-pi1 disjointness".
  unfold list_disjoint; intros; inv H.
  - rewrite <- H1; intro Hcontr; rewrite <- Hcontr in *.
    rewrite Forall_forall in Hvpi1.
    pose (Hvpi1 _ H0); zauto.
  - eapply Hlipidisj1; eauto.

  SCase "6. li1 constraint II".
  rewrite Forall_forall in Hvli1; apply Forall_forall; intros; inv H.
  - rewrite <- H0; rewrite <- Hn1; zauto.
  - exploit Hvli1; eauto; rewrite <- Hn1; zauto.

  SCase" 7. pi1 constraint II".
  rewrite Forall_forall in Hvpi1; apply Forall_forall; intros.
  exploit Hvpi1; eauto; rewrite <- Hn1; zauto.

  auto.
Qed.

Lemma malloc_right_preserves_valid_memories:
  forall td mem1 mem2 mem2' tsz gn1 aln mb2 li1 pi1 li2 pi2 alpha gmax
    (Hmalloc2: malloc td mem2 tsz gn1 aln = ret (mem2', mb2))
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2),
    exists alpha',
      (inject_incr' alpha alpha' li1 pi1 li2 pi2) /\
      (valid_memories alpha' gmax mem1 mem2' li1 pi1 (mb2::li2) pi2).
Proof.
  intros; inv Hvmem; inv Hwf.
  exploit memory_props.MemProps.malloc_result; try eapply Hmalloc2; eauto.
  exploit memory_props.MemProps.nextblock_malloc; try eapply Hmalloc2; eauto.
  intros Hn2 Hmb2.

  exists alpha.
  assert (Hincr: inject_incr' alpha alpha li1 pi1 li2 pi2)
    by (unfold inject_incr'; splits; done).

  splits; try done.

  Case "valid_memories".
  unfold malloc in Hmalloc2.
  apply malloc_inv in Hmalloc2.
  (* remember (GV2int td Size.ThirtyTwo gn1) as gn1i; destruct gn1i; [|done]. *)
  (* destruct (zlt 0 z); [|done]. *)
  (* assert (Hmalloc2: Mem.alloc mem2 0 z = (mem2', mb2)). *)
  (* - by remember (mem2', mb2) as mm2; inv Hmalloc2. *)

  econstructor; try done.

  SCase "1. mem_inj".
  inversion Hmemi; econstructor.

  SSCase "1.1. valid_access".
  intros.
  exploit mi_access; eauto; intro Hva.
  eapply Mem.valid_access_alloc_other; eauto.

  SSCase "1.2. mem_contents".
  intros.
  exploit mi_memval; eauto; intro Hmi.
  assert (Hceq: Mem.mem_contents mem2 b2 (ofs + delta) =
    Mem.mem_contents mem2' b2 (ofs + delta)).
  - exploit Mem.alloc_mem_contents; eauto; intro Hbrd.
    rewrite <- Hbrd; unfold update, zeq.
    destruct (Z_eq_dec b2 (Mem.nextblock mem2)); [|done].
    rewrite e in H.
    exploit Hmap2; eauto; intro Hcontr.
    contradict Hcontr; zauto.
  rewrite <- Hceq; done.

  SCase "2. wf_sb_mi".
  econstructor; try done.

  SSCase "2.1. map2".
  intros.
  by exploit Hmap2; eauto; intros; rewrite <- Hn2; zauto.

  SSCase "2.2. mappedblocks".
  intros.
  exploit mi_mappedblocks; eauto; intros;
    unfold Mem.valid_block in *; rewrite <- Hn2; zauto.

  SSCase "2.3. bounds".
  intros.
  exploit mi_bounds; eauto; intros; rewrite H0; clear H0.
  exploit Mem.bounds_alloc; eauto.
  instantiate (1:=b'); intro Hb.
  unfold eq_block, zeq in Hb.
  destruct (Z_eq_dec b' mb2); [|done].
  elimtype False; subst b'.
  exploit Hmap2; eauto; intro Hcontr.
  rewrite Hmb2 in Hcontr; zauto.

  SCase "3. li2 constraint".
  intros; inv H.
  - rewrite <- H0; intro Hcontr.
    apply Hmap2 in Hcontr; zauto.
  - eapply Hli2none; eauto.

  SCase "4. li2 freeable".
  intros b Hbin; simpl in Hbin.
  destruct Hbin as [Hbeq|Hbin].

  - subst; rewrite Hbeq in Hmalloc2.
    eapply malloc_implies_freeable; eauto.
  - intros; exploit Hli2free; eauto; intro Hres.
    eapply malloc_preserves_isolated_heap_freeable; eauto.

  SCase "5. pi2 freeable".
  intros; exploit Hpi2free; eauto; intro Hres.
  eapply malloc_preserves_isolated_heap_freeable; eauto.

  SCase "6. li2-pi2 disjointness".
  unfold list_disjoint; intros; inv H.
  - rewrite <- H1; intro Hcontr; rewrite <- Hcontr in *.
    rewrite Forall_forall in Hvpi0.
    pose (Hvpi0 _ H0); zauto.
  - eapply Hlipidisj2; eauto.

  SCase "7. li2 constraint II".
  rewrite Forall_forall in Hvli0; apply Forall_forall; intros; inv H.
  - rewrite <- H0; rewrite <- Hn2; zauto.
  - exploit Hvli0; eauto; rewrite <- Hn2; zauto.

  SCase "8. pi2 constraint II".
  rewrite Forall_forall in Hvpi0; apply Forall_forall; intros.
  exploit Hvpi0; eauto; rewrite <- Hn2; zauto.

  auto.
Qed.

Lemma free_preserves_isolated_heap_freeable_1:
  forall alpha (b1 b2 b: Values.block) li mem mem' (delta: Z) l h
    (Halpha: alpha b1 = ret (b2, delta))
    (Hbin: In b li)
    (Hli: forall b, In b li -> alpha b = merror)
    (Hfree: Mem.free mem b1 l h = ret mem')
    (Hfreea: let (l, h) := Mem.bounds mem b in Mem.free mem b l h <> merror),
    let (l, h) := Mem.bounds mem' b in Mem.free mem' b l h <> merror.
Proof.
  intros.
  exploit Mem.bounds_free; eauto.
  instantiate (1:=b); intro Hbound; rewrite Hbound; clear Hbound.
  destruct (Mem.bounds mem0 b).
  assert (Hneq: b1 <> b).
  - intro Hcontr1; subst. exploit Hli; eauto; intro Hcontr.
    rewrite Hcontr in Halpha; done.
  intro Hcontr; elim Hfreea; clear Hfreea.

  Local Transparent Mem.free.
  unfold Mem.free; unfold Mem.free in Hcontr.
  destruct (Mem.range_perm_dec mem' b z z0 Freeable); [done|].
  assert (Hperm: ~ Mem.range_perm mem0 b z z0 Freeable).
  - intro Hcontrp; elim n; clear n.
    unfold Mem.range_perm in *; intros.
    exploit Hcontrp; eauto; intro Hperm.
    eapply Mem.perm_free_1; eauto.

  destruct (Mem.range_perm_dec mem0 b z z0 Freeable); done.
  Global Opaque Mem.free.

Qed.

Lemma free_preserves_isolated_heap_freeable_2:
  forall alpha (b1 b2 b: Values.block) li mem mem' (delta: Z) l h
    (Halpha: alpha b1 = ret (b2, 0))
    (Hbin: In b li)
    (Hli: forall b, In b li -> forall sb, alpha sb <> ret (b, 0))
    (Hfree: Mem.free mem b2 l h = ret mem')
    (Hfreea: let (l, h) := Mem.bounds mem b in Mem.free mem b l h <> merror),
    let (l, h) := Mem.bounds mem' b in Mem.free mem' b l h <> merror.
Proof.
  intros.
  exploit Mem.bounds_free; eauto.
  instantiate (1:=b); intro Hbound; rewrite Hbound; clear Hbound.
  destruct (Mem.bounds mem0 b).
  assert (Hneq: b2 <> b).
  - intro Hcontr1; subst; exploit Hli; eauto.
  intro Hcontr; elim Hfreea; clear Hfreea.

  Local Transparent Mem.free.
  unfold Mem.free; unfold Mem.free in Hcontr.
  destruct (Mem.range_perm_dec mem' b z z0 Freeable); [done|].
  assert (Hperm: ~ Mem.range_perm mem0 b z z0 Freeable).
  - intro Hcontrp; elim n; clear n.
    unfold Mem.range_perm in *; intros.
    exploit Hcontrp; eauto; intro Hperm.
    eapply Mem.perm_free_1; eauto.

  destruct (Mem.range_perm_dec mem0 b z z0 Freeable); done.
  Global Opaque Mem.free.

Qed.

Lemma free_preserves_valid_memories:
  forall alpha gmax td mem1 mem2 mem1' mem2' li1 pi1 li2 pi2 p1 p2
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2)
    (Hinj: gv_inject alpha p1 p2)
    (Hfree1: free td mem1 p1 = ret mem1')
    (Hfree2: free td mem2 p2 = ret mem2'),
    valid_memories alpha gmax mem1' mem2' li1 pi1 li2 pi2.
Proof.
  intros.
  inv Hvmem.

  (* utilities *)
  exploit free_inv; try eapply Hfree1; eauto;
    intros [blk1 [ofs1 [hi1 [lo1 [Hp1 [Hofs1 [Hb1 Hfree1']]]]]]].
  exploit free_inv; try eapply Hfree2; eauto;
    intros [blk2 [ofs2 [hi2 [lo2 [Hp2 [Hofs2 [Hb2 Hfree2']]]]]]].
  exploit Mem.nextblock_free; try eapply Hfree1'; eauto; intro Hfeq1.
  exploit Mem.nextblock_free; try eapply Hfree2'; eauto; intro Hfeq2.

  unfold GV2ptr in *.
  destruct p1 as [|[[]][]]; inv Hp1.
  inv Hinj; inv H4; inv H3.

  exploit mem_inj__free; eauto. intros [mem2'' [Hfree2'' [Hwfm2' Hminj2']]].
  inv Hp2.
  assert (Hmeq2: ret mem2' = ret mem2'').
  - assert (Hdz: delta = 0) by (inv Hwf; eapply mi_range_block; eauto); subst.
    rewrite <- Hfree2', <- Hfree2''.
    inv Hwf.
    exploit mi_bounds; try apply H1; eauto; intro Hbeq.
    rewrite <- Hb1, <- Hb2 in Hbeq; inv Hbeq.
    f_equal; zauto.
  inv Hmeq2.

  econstructor; try done; try (by rewrite Hfeq1); try (by rewrite Hfeq2).
  - intros b Hbin. exploit Hli1free; eauto; intro Hres.
    eapply free_preserves_isolated_heap_freeable_1; eauto.
  - intros b Hbin. exploit Hli2free; eauto; intro Hres.
    assert (Hd: delta = 0) by (inv Hwf; exploit mi_range_block; eauto).
    subst delta; eapply free_preserves_isolated_heap_freeable_2; eauto.
  - intros b Hbin. exploit Hpi1free; eauto; intro Hres.
    eapply free_preserves_isolated_heap_freeable_1; eauto.
  - intros b Hbin. exploit Hpi2free; eauto; intro Hres.
    assert (Hd: delta = 0) by (inv Hwf; exploit mi_range_block; eauto).
    subst delta; eapply free_preserves_isolated_heap_freeable_2; eauto.

Qed.

Lemma mstore_aux_preserves_freeable:
  forall mem mem' mc gv b1 ofs b
    (Hstore: mstore_aux mem mc gv b1 ofs = ret mem')
    (Hfree: let (l, h) := Mem.bounds mem b in Mem.free mem b l h <> merror),
    let (l, h) := Mem.bounds mem' b in Mem.free mem' b l h <> merror.
Proof.
  intros.

  assert (Hbound: Mem.bounds mem0 b = Mem.bounds mem' b).
  - clear -Hstore.
    generalize dependent mem0; generalize dependent mem';
    generalize dependent gv; generalize dependent ofs.
    induction mc; intros;
      [by simpl in Hstore; destruct gv; [|done]; inv Hstore|].
    simpl in Hstore.
    destruct gv; [done|].
    destruct p.
    destruct (AST.memory_chunk_eq a m && has_chunk_eq v m); [|done].
    remember (Mem.store m mem0 b1 ofs v) as nm; destruct nm; [|done].
    exploit IHmc; eauto; intro Hbrd; rewrite <-Hbrd.
    exploit Mem.bounds_store; eauto.
  rewrite <-Hbound.
  destruct (Mem.bounds mem0 b); clear Hbound.
  intro Hcontr; elim Hfree; clear Hfree.

  Local Transparent Mem.free.
  unfold Mem.free in *.
  remember (Mem.range_perm_dec mem' b z z0 Freeable) as perm';
    destruct perm'; [done|]; clear Hcontr.

  assert (Hperm: ~ Mem.range_perm mem0 b z z0 Freeable).
  - clear -n Hstore.
    intro Hcontr; elim n; clear n.
    generalize dependent mem0; generalize dependent mem';
    generalize dependent gv; generalize dependent ofs.
    induction mc; intros;
      [by simpl in Hstore; destruct gv; [|done]; inv Hstore|].
    simpl in Hstore.
    destruct gv; [done|].
    destruct p.
    destruct (AST.memory_chunk_eq a m && has_chunk_eq v m); [|done].
    remember (Mem.store m mem0 b1 ofs v) as nm; destruct nm; [|done].
    hexploit IHmc; eauto.
    unfold Mem.range_perm in *; intros.
    exploit Hcontr; eauto; intro Hperm.
    eapply Mem.perm_store_1; eauto.

  destruct (Mem.range_perm_dec mem0 b z z0); done.
  Global Opaque Mem.free.

Qed.

Lemma mstore_preserves_valid_memories:
  forall alpha gmax td mem1 mem2 mem1' mem2' li1 pi1 li2 pi2 typ p1 p2 gv1 gv2 aln
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2)
    (Hvinj: gv_inject alpha gv1 gv2)
    (Hpinj: gv_inject alpha p1 p2)
    (Hstore1: mstore td mem1 p1 typ gv1 aln = ret mem1')
    (Hstore2: mstore td mem2 p2 typ gv2 aln = ret mem2'),
    valid_memories alpha gmax mem1' mem2' li1 pi1 li2 pi2.
Proof.
  intros.
  inv Hvmem.

  (* utilities *)
  exploit store_inv; try eapply Hstore1; eauto;
    intros [blk1 [ofs1 [mc1 [Hp1 [Hstore1' Hstore1'']]]]].
  exploit store_inv; try eapply Hstore2; eauto;
    intros [blk2 [ofs2 [mc2 [Hp2 [Hstore2' Hstore2'']]]]].
  exploit memory_props.MemProps.nextblock_mstore_aux; try eapply Hstore1'';
    eauto; intro Hfeq1.
  exploit memory_props.MemProps.nextblock_mstore_aux; try eapply Hstore2'';
    eauto; intro Hfeq2.
  rewrite Hstore1' in Hstore2'; inv Hstore2'.

  unfold GV2ptr in *.
  destruct p1 as [|[[]][]]; inv Hp1.
  inv Hpinj; inv H4; inv H3.

  exploit mem_inj_mstore_aux; eauto. intros [mem2'' [Hstore2''' [Hwfm2'' Hminj2']]].
  inv Hp2.
  assert (Hmeq2: ret mem2' = ret mem2'').
  - assert (Hdz: delta = 0) by (inv Hwf; eapply mi_range_block; eauto); subst.
    rewrite <- Hstore2'', <- Hstore2'''.
    f_equal.
    rewrite Int.add_zero; zauto.
  inv Hmeq2.

  econstructor; try done; try (by rewrite <- Hfeq1); try (by rewrite <- Hfeq2).
  - intros b Hbin. exploit Hli1free; eauto; intro Hres.
    eapply mstore_aux_preserves_freeable; eauto.
  - intros b Hbin. exploit Hli2free; eauto; intro Hres.
    eapply mstore_aux_preserves_freeable; eauto.
  - intros b Hbin. exploit Hpi1free; eauto; intro Hres.
    eapply mstore_aux_preserves_freeable; eauto.
  - intros b Hbin. exploit Hpi2free; eauto; intro Hres.
    eapply mstore_aux_preserves_freeable; eauto.

Qed.

Lemma mstore_left_preserves_valid_memories:
  forall alpha gmax td gl mem1 mem2 mem1' olc1 olc2 lc1 lc2 li1 pi1 li2 pi2
    typ p1 gv1 pval aln iso1 iso2
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2)
    (Hisosem1: isolated_sem td olc1 lc1 li1 iso1)
    (Hisosem2: isolated_sem td olc2 lc2 li2 iso2)
    (Hiso: is_isolated iso1 (vars_aux.add_ntag_value pval))
    (Hpov: getOperandValue td pval lc1 gl = ret p1)
    (Hstore1: mstore td mem1 p1 typ gv1 aln = ret mem1'),
    valid_memories alpha gmax mem1' mem2 li1 pi1 li2 pi2.
Proof.
  intros.
  inv Hvmem.

  (* utilities *)
  exploit store_inv; try eapply Hstore1; eauto;
    intros [blk1 [ofs1 [mc1 [Hp1 [Hstore1' Hstore1'']]]]].
  exploit memory_props.MemProps.nextblock_mstore_aux; eauto; intro Hfeq1.
  clear Hstore1.

  econstructor; try done; try (by rewrite <- Hfeq1).

  Case "1. mem_inj".
  inv Hmemi; econstructor.

  SCase "1.1. valid_access".
  intros; eapply mi_access; eauto.
  clear -Hstore1'' H0.
  remember (Int.signed 31 ofs1) as o1; clear Heqo1.
  generalize dependent mem1; generalize dependent mem1';
  generalize dependent o1; generalize dependent gv1.
  induction mc1; intros.
  - by simpl in Hstore1''; destruct gv1; [|done]; inv Hstore1''.
  - simpl in Hstore1''.
    destruct gv1; [done|]; destruct p0 as [v c].
    destruct (AST.memory_chunk_eq a c && has_chunk_eq v c); [|done].
    remember (Mem.store c mem1 blk1 o1 v) as sstore.
    destruct sstore; [|done].
    exploit IHmc1.
    + apply H0.
    + apply Hstore1''.
    intro Hbrd.
    eapply Mem.store_valid_access_2; eauto.

  SCase "1.2. mem_contents".
  intros; unfold is_isolated in Hiso.
  remember (vars_aux.add_ntag_value pval) as npval.
  destruct npval; [|done].
  unfold vars_aux.add_ntag_value in Heqnpval.
  destruct pval; [|done]; inv Heqnpval.
  simpl in Hpov.
  unfold isolated_sem in Hisosem1.
  apply IdExtSetFacts.mem_iff in Hiso.
  unfold AtomSetImpl.For_all in Hisosem1.
  pose (Hisosem1 _ Hiso) as Hii. 
  simpl in Hii; inv Hii; [by rewrite H1 in Hpov|].
  destruct H1 as [gvp [Hlookup Hptr]].
  rewrite Hlookup in Hpov; inv Hpov.
  rewrite Hp1 in Hptr.
  assert (Hnbeq: b1 <> blk1) by
    (intro Hcontr; subst; rewrite (Hli1none _ Hptr) in H; done).

  assert (Hceq: Mem.mem_contents mem1' b1 ofs = Mem.mem_contents mem1 b1 ofs).
  - clear -Hstore1'' Hnbeq.
    remember (Int.signed 31 ofs1) as o1; clear Heqo1.
    generalize dependent mem1; generalize dependent mem1';
    generalize dependent o1; generalize dependent gv1.
    induction mc1; intros;
      [by simpl in Hstore1''; destruct gv1; [|done]; inv Hstore1''|].
    simpl in Hstore1''.
    destruct gv1; [done|]; destruct p as [v c].
    destruct (AST.memory_chunk_eq a c && has_chunk_eq v c); [|done].
    remember (Mem.store c mem1 blk1 o1 v) as sstore.
    destruct sstore; [|done].
    exploit IHmc1; try apply Hstore1''; intro Hbrd; rewrite Hbrd.
    symmetry in Heqsstore.
    pose (Mem.store_getN_out _ _ _ _ _ _ Heqsstore _ ofs 1 Hnbeq) as Hres.
    by simpl in Hres; inv Hres.
  rewrite Hceq.

  assert (Hpeq: Mem.perm mem1 b1 ofs Nonempty).
  - clear -Hstore1'' H0.
    remember (Int.signed 31 ofs1) as o1; clear Heqo1.
    generalize dependent mem1; generalize dependent mem1';
    generalize dependent o1; generalize dependent gv1.
    induction mc1; intros;
      [by simpl in Hstore1''; destruct gv1; [|done]; inv Hstore1''|].
    simpl in Hstore1''.
    destruct gv1; [done|]; destruct p as [v c].
    destruct (AST.memory_chunk_eq a c && has_chunk_eq v c); [|done].
    remember (Mem.store c mem1 blk1 o1 v) as sstore.
    destruct sstore; [|done].
    exploit IHmc1; eauto; intro Hbrd.
    eapply Mem.perm_store_2; eauto.

  eapply mi_memval; eauto.

  Case "2. wf_sb_mi".
  inv Hwf; econstructor; try done; try (by rewrite <- Hfeq1); intros.

  SCase "2.1. map1".
  unfold Mem.valid_block in H; rewrite <- Hfeq1 in H; eapply Hmap1; eauto.

  SCase "2.2. bounds".
  exploit memory_props.MemProps.bounds_mstore_aux; eauto.
  instantiate (1:=b); intro Hbeq.
  rewrite <- Hbeq.
  eapply mi_bounds; eauto.

  - intros b Hbin. exploit Hli1free; eauto; intro Hres.
    eapply mstore_aux_preserves_freeable; eauto.
  - intros b Hbin. exploit Hpi1free; eauto; intro Hres.
    eapply mstore_aux_preserves_freeable; eauto.

Qed.

Lemma BOP_eq_check_value_implies_injection:
  forall md inv1 inv2 lv1 lv2 rv1 rv2 lc1 lc2 alpha gmax li1 li2 olc1 olc2 gvs1 gvs2
    sz b mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hsu1: self_use_check (ret insn_bop i b sz lv1 rv1) = true)
    (Hsu2: self_use_check (ret insn_bop i b sz lv2 rv2) = true)
    (Heql: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value lv1) (vars_aux.add_ntag_value lv2) = true)
    (Heqr: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value rv1) (vars_aux.add_ntag_value rv2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hbop1: BOP (CurTargetData cfg1) lc1 (Globals cfg1) b sz lv1 rv1 = ret gvs1)
    (Hbop2: BOP (CurTargetData cfg2) lc2 (Globals cfg2) b sz lv2 rv2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.

Proof.
  eq_check_value_tac.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv1. - apply Hniv. - apply Heql. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjl.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv2. - apply Hniv0. - apply Heqr. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjr.

  assert (mbop (CurTargetData cfg1) b sz0 g1 g2 = ret gvs1) as Hbop1' by apply Hbop1.
  assert (mbop (CurTargetData cfg2) b sz0 g g0 = ret gvs2) as Hbop2' by apply Hbop2.

  exploit simulation__mbop.
  - apply Hgvinjl. - apply Hgvinjr. - apply Hbop1'.
  intros [gvs2' [Hbop2'' Hinj]].
  rewrite Htd in *; rewrite Hbop2' in Hbop2''.
  inversion Hbop2''; subst.
  done.
Qed.

Lemma FBOP_eq_check_value_implies_injection:
  forall md inv1 inv2 lv1 lv2 rv1 rv2 lc1 lc2 alpha gmax li1 li2 olc1 olc2 gvs1 gvs2
     sz fb mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hsu1: self_use_check (ret insn_fbop i fb sz lv1 rv1) = true)
    (Hsu2: self_use_check (ret insn_fbop i fb sz lv2 rv2) = true)
    (Heql: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value lv1) (vars_aux.add_ntag_value lv2) = true)
    (Heqr: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value rv1) (vars_aux.add_ntag_value rv2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hfbop1: FBOP (CurTargetData cfg1) lc1 (Globals cfg1) fb sz lv1 rv1 = ret gvs1)
    (Hfbop2: FBOP (CurTargetData cfg2) lc2 (Globals cfg2) fb sz lv2 rv2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.

Proof.
  eq_check_value_tac.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv1. - apply Hniv. - apply Heql. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjl.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv2. - apply Hniv0. - apply Heqr. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjr.

  assert (mfbop (CurTargetData cfg1) fb sz0 g1 g2 = ret gvs1) as Hfbop1'
    by apply Hfbop1.
  assert (mfbop (CurTargetData cfg2) fb sz0 g g0 = ret gvs2) as Hfbop2'
    by apply Hfbop2.

  exploit simulation__mfbop.
  - apply Hgvinjl. - apply Hgvinjr. - apply Hfbop1'.
  intros [gvs2' [Hfbop2'' Hinj]].
  rewrite Htd in *; rewrite Hfbop2' in Hfbop2''.
  inversion Hfbop2''; subst.
  done.
Qed.

Lemma EXTRACTVALUE_eq_check_value_implies_injection:
  forall md inv1 inv2 v1 v2 lc1 lc2 alpha gmax li1 li2 olc1 olc2 gvs1 gvs2 gvs1' gvs2'
    t1 t2 lc mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hsu1: self_use_check (ret insn_extractvalue i t1 v1 lc t2) = true)
    (Hsu2: self_use_check (ret insn_extractvalue i t1 v2 lc t2) = true)
    (Heq: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hov1: getOperandValue (CurTargetData cfg1) v1 lc1 (Globals cfg1) = ret gvs1')
    (Hov2: getOperandValue (CurTargetData cfg2) v2 lc2 (Globals cfg2) = ret gvs2')
    (Hev1: extractGenericValue (CurTargetData cfg1) t1 gvs1' lc = ret gvs1)
    (Hev2: extractGenericValue (CurTargetData cfg2) t1 gvs2' lc = ret gvs2),
    gv_inject alpha gvs1 gvs2.

Proof.
  eq_check_value_tac.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hsu1. - apply Hsu2. - apply Heq. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinj.

  exploit simulation__extractGenericValue; eauto.
  intros [gv' [Hev2' Hinj]].
  rewrite Htd in *.
  assert (ret gv' = ret gvs2) as Hgveq by (rewrite <- Hev2; rewrite <- Hev2'; done).
  inversion Hgveq; subst; done.
Qed.

Lemma INSERTVALUE_eq_check_value_implies_injection:
  forall md inv1 inv2 lt rt lv1 lv2 rv1 rv2 lc1 lc2 alpha gmax li1 li2
    olc1 olc2 gvs1 gvs2 lgvs1 rgvs1 lgvs2 rgvs2 lc iso1 iso2
     mem1 mem2 cfg1 cfg2 i igvs1 igvs2 
    (Hsu1: self_use_check (ret insn_insertvalue i lt lv1 rt rv1 lc) = true)
    (Hsu2: self_use_check (ret insn_insertvalue i lt lv2 rt rv2 lc) = true)
    (Heql: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value lv1) (vars_aux.add_ntag_value lv2) = true)
    (Heqr: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value rv1) (vars_aux.add_ntag_value rv2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hlov1: getOperandValue (CurTargetData cfg1) lv1 lc1 (Globals cfg1) = ret lgvs1)
    (Hrov1: getOperandValue (CurTargetData cfg1) rv1 lc1 (Globals cfg1) = ret rgvs1)
    (Hlov2: getOperandValue (CurTargetData cfg2) lv2 lc2 (Globals cfg2) = ret lgvs2)
    (Hrov2: getOperandValue (CurTargetData cfg2) rv2 lc2 (Globals cfg2) = ret rgvs2)
    (Higv1: insertGenericValue (CurTargetData cfg1) lt lgvs1 lc rt rgvs1 = ret gvs1)
    (Higv2: insertGenericValue (CurTargetData cfg2) lt lgvs2 lc rt rgvs2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.

Proof.
  eq_check_value_tac.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv1. - apply Hniv. - apply Heql. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjl.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv2. - apply Hniv0. - apply Heqr. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjr.

  exploit simulation__insertGenericValue.
  - apply Hgvinjl. - apply Hgvinjr. - apply Higv1.
  intros [gvs2' [Higv2' Hinj]].
  rewrite Htd in *.
  assert (ret gvs2 = ret gvs2') as Hgveq
    by (rewrite <- Higv2; rewrite <- Higv2'; done).
  inversion Hgveq; done.
Qed.

Lemma LOAD_eq_check_value_implies_injection:
  forall md inv1 inv2 t v1 v2 aln lc1 lc2 alpha gmax olc1 olc2 gvs1 gvs2
    gvs1' gvs2' mem1 mem2 cfg1 cfg2 i igvs1 igvs2 li1 pi1 li2 pi2 iso1 iso2
    (Hsu1: self_use_check (ret insn_load i t v1 aln) = true)
    (Hsu2: self_use_check (ret insn_load i t v2 aln) = true)
    (Heq: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hov1: getOperandValue (CurTargetData cfg1) v1 lc1 (Globals cfg1) = ret gvs1')
    (Hov2: getOperandValue (CurTargetData cfg2) v2 lc2 (Globals cfg2) = ret gvs2')
    (Hload1: mload (CurTargetData cfg1) mem1 gvs1' t aln = ret gvs1)
    (Hload2: mload (CurTargetData cfg2) mem2 gvs2' t aln = ret gvs2),
    gv_inject alpha gvs1 gvs2.
Proof.
  eq_check_value_tac.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hsu1. - apply Hsu2. - apply Heq. - inv Hvmem; apply Hwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinj.

  rewrite Htd in *.
  unfold mload in *.
  remember (GV2ptr (CurTargetData cfg2) (getPointerSize (CurTargetData cfg2)) gvs1')
  as ptr1';
    destruct ptr1'; try done; destruct v; try done;
      destruct (flatten_typ (CurTargetData cfg2) t); try done.
  remember (GV2ptr (CurTargetData cfg2) (getPointerSize (CurTargetData cfg2)) gvs2')
  as ptr2';
    destruct ptr2'; try done; destruct v; try done.

  inv Hvmem.

  unfold GV2ptr in Heqptr1'; destruct gvs1'; [done|].
  destruct p; destruct v; try done.
  destruct gvs1'; [|done]; inv Heqptr1'.
  unfold GV2ptr in Heqptr2'; destruct gvs2'; [done|].
  destruct p; destruct v; try done.
  destruct gvs2'; [|done]; inv Heqptr2'.
  inv Hgvinj; inv H1.
  inversion Hwf; exploit mi_range_block; try eapply H3; eauto; intro Hd.
  subst.

  exploit simulation_mload_aux; eauto.
  intros [gv2 [Hload2' Hinj2']].
  assert (Hgeq: ret gv2 = ret gvs2).
  - rewrite <- Hload2, <- Hload2'; f_equal; eauto.
    rewrite Int.add_zero; omega.
  inv Hgeq; done.
Qed.

Lemma GEP_eq_check_value_implies_injection:
  forall md inv1 inv2 t1 t2 v1 v2 lsv1 lsv2 inb lc1 lc2 alpha gmax li1 li2
    olc1 olc2 gvs1 gvs2
    gvs1' gvs2' lsv1' lsv2' mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hsu1: self_use_check (ret insn_gep i inb t1 v1 lsv1 t2) = true)
    (Hsu2: self_use_check (ret insn_gep i inb t1 v2 lsv2 t2) = true)
    (Heq: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = true)
    (Heqlsv: eq_check_lsv md inv1 inv2
      (vars_aux.add_ntag_lsv lsv1) (vars_aux.add_ntag_lsv lsv2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hov1: getOperandValue (CurTargetData cfg1) v1 lc1 (Globals cfg1) = ret gvs1')
    (Hov2: getOperandValue (CurTargetData cfg2) v2 lc2 (Globals cfg2) = ret gvs2')
    (Hlsv1: values2GVs (CurTargetData cfg1) lsv1 lc1 (Globals cfg1) = ret lsv1')
    (Hlsv2: values2GVs (CurTargetData cfg2) lsv2 lc2 (Globals cfg2) = ret lsv2')
    (Hgep1: GEP (CurTargetData cfg1) t1 gvs1' lsv1' inb t2 = ret gvs1)
    (Hgep2: GEP (CurTargetData cfg2) t1 gvs2' lsv2' inb t2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.
Proof.
  eq_check_value_tac.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv1. - apply Hniv. - apply Heq. - apply Hvwf. - apply Htd.
  - eauto. - eauto.
  intro Hgvinj.

  hexploit values2GVs_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv2. - apply Hniv0. - apply Heqlsv. - apply Hvwf. - apply Htd.
  - eauto. - eauto.
  intro Hgvsinj.

  exploit simulation__GEP; eauto.
  intros [gv2 [Hgep2' Hinj2']].
  rewrite Htd in *.
  assert (Hgeq: ret gv2 = ret gvs2).
  - rewrite <- Hgep2, <- Hgep2'; f_equal; eauto.
  inv Hgeq; done.
Qed.

Lemma TRUNC_eq_check_value_implies_injection:
  forall md inv1 inv2 t1 t2 v1 v2 trc lc1 lc2 alpha gmax li1 li2 olc1 olc2 gvs1 gvs2
     mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hsu1: self_use_check (ret insn_trunc i trc t1 v1 t2) = true)
    (Hsu2: self_use_check (ret insn_trunc i trc t1 v2 t2) = true)
    (Heq: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Htrunc1: TRUNC (CurTargetData cfg1) lc1 (Globals cfg1) trc t1 v1 t2 = ret gvs1)
    (Htrunc2: TRUNC (CurTargetData cfg2) lc2 (Globals cfg2) trc t1 v2 t2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.
Proof.
  eq_check_value_tac.
  rewrite lift_op1_prop in Htrunc1.
  rewrite lift_op1_prop in Htrunc2.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hsu1. - apply Hsu2. - apply Heq. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinj.

  exploit simulation__mtrunc; eauto.
  intros [gv2 [Htrunc2' Hinj2']].
  rewrite Htd in *.

  rewrite Htrunc2' in Htrunc2.
  by inv Htrunc2.
Qed.

Lemma EXT_eq_check_value_implies_injection:
  forall md inv1 inv2 t1 t2 v1 v2 ext lc1 lc2 alpha gmax li1 li2 olc1 olc2 gvs1 gvs2
     mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hsu1: self_use_check (ret insn_ext i ext t1 v1 t2) = true)
    (Hsu2: self_use_check (ret insn_ext i ext t1 v2 t2) = true)
    (Heq: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hext1: EXT (CurTargetData cfg1) lc1 (Globals cfg1) ext t1 v1 t2 = ret gvs1)
    (Hext2: EXT (CurTargetData cfg2) lc2 (Globals cfg2) ext t1 v2 t2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.
Proof.
  eq_check_value_tac.
  rewrite lift_op1_prop in Hext1.
  rewrite lift_op1_prop in Hext2.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hsu1. - apply Hsu2. - apply Heq. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinj.

  exploit simulation__mext; eauto.
  intros [gv2 [Hext2' Hinj2']].
  rewrite Htd in *.

  rewrite Hext2' in Hext2.
  by inv Hext2.
Qed.

Lemma CAST_eq_check_value_implies_injection:
  forall md inv1 inv2 t1 t2 v1 v2 cop lc1 lc2 alpha gmax li1 li2 olc1 olc2 gvs1 gvs2
     mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hsu1: self_use_check (ret insn_cast i cop t1 v1 t2) = true)
    (Hsu2: self_use_check (ret insn_cast i cop t1 v2 t2) = true)
    (Heq: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value v1) (vars_aux.add_ntag_value v2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hcast1: CAST (CurTargetData cfg1) lc1 (Globals cfg1) cop t1 v1 t2 = ret gvs1)
    (Hcast2: CAST (CurTargetData cfg2) lc2 (Globals cfg2) cop t1 v2 t2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.
Proof.
  eq_check_value_tac.
  rewrite lift_op1_prop in Hcast1.
  rewrite lift_op1_prop in Hcast2.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hsu1. - apply Hsu2. - apply Heq. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinj.

  exploit simulation__mcast; eauto.
  intros [gv2 [Hcast2' Hinj2']].
  rewrite Htd in *.

  rewrite Hcast2' in Hcast2.
  by inv Hcast2.
Qed.

Lemma ICMP_eq_check_value_implies_injection:
  forall md inv1 inv2 t lv1 rv1 lv2 rv2 cond lc1 lc2 alpha gmax li1 li2
    olc1 olc2 gvs1 gvs2 mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2 
    (Hsu1: self_use_check (ret insn_icmp i cond t lv1 rv1) = true)
    (Hsu2: self_use_check (ret insn_icmp i cond t lv2 rv2) = true)
    (Heql: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value lv1) (vars_aux.add_ntag_value lv2) = true)
    (Heqr: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value rv1) (vars_aux.add_ntag_value rv2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hicmp1: ICMP (CurTargetData cfg1) lc1 (Globals cfg1) cond t lv1 rv1 = ret gvs1)
    (Hicmp2: ICMP (CurTargetData cfg2) lc2 (Globals cfg2) cond t lv2 rv2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.
Proof.
  eq_check_value_tac.
  rewrite lift_op2_prop in Hicmp1.
  rewrite lift_op2_prop in Hicmp2.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv1. - apply Hniv. - apply Heql. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjl.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv2. - apply Hniv0. - apply Heqr. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjr.

  exploit simulation__micmp; try eapply Hicmp1; eauto.
  intros [gv2 [Hicmp2' Hinj2']].
  rewrite Htd in *.

  rewrite Hicmp2' in Hicmp2.
  by inv Hicmp2.
Qed.

Lemma FCMP_eq_check_value_implies_injection:
  forall md inv1 inv2 t lv1 rv1 lv2 rv2 fcond lc1 lc2 alpha gmax li1 li2
    olc1 olc2 gvs1 gvs2
    mem1 mem2 cfg1 cfg2 i igvs1 igvs2 iso1 iso2
    (Hsu1: self_use_check (ret insn_fcmp i fcond t lv1 rv1) = true)
    (Hsu2: self_use_check (ret insn_fcmp i fcond t lv2 rv2) = true)
    (Heql: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value lv1) (vars_aux.add_ntag_value lv2) = true)
    (Heqr: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value rv1) (vars_aux.add_ntag_value rv2) = true)
    (Hmdsem: maydiff_sem (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (updateAddAL GVs lc1 i igvs1) (updateAddAL GVs lc2 i igvs2) mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hfcmp1: FCMP (CurTargetData cfg1) lc1 (Globals cfg1) fcond t lv1 rv1 = ret gvs1)
    (Hfcmp2: FCMP (CurTargetData cfg2) lc2 (Globals cfg2) fcond t lv2 rv2 = ret gvs2),
    gv_inject alpha gvs1 gvs2.
Proof.
  eq_check_value_tac.
  rewrite lift_op2_prop in Hfcmp1.
  rewrite lift_op2_prop in Hfcmp2.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv1. - apply Hniv. - apply Heql. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjl.

  hexploit getOperandValue_eq_check_value_implies_injection;
  try eapply Hmdsem; try eapply Hinvsem; try eapply Hgequiv.
  - apply Hniv2. - apply Hniv0. - apply Heqr. - apply Hvwf. - apply Htd.
  - symmetry; eauto. - symmetry; eauto.
  intro Hgvinjr.

  exploit simulation__mfcmp; try eapply Hfcmp1; eauto.
  intros [gv2 [Hfcmp2' Hinj2']].
  rewrite Htd in *.

  rewrite Hfcmp2' in Hfcmp2.
  by inv Hfcmp2.
Qed.

Lemma injection_implies_isGVZero_equal:
  forall td alpha gvs1 gvs2
    (Hinj: gv_inject alpha gvs1 gvs2),
    isGVZero td gvs1 = isGVZero td gvs2.
Proof.
  intros.
  unfold isGVZero, GV2int.
  destruct gvs1, gvs2; try (by inv Hinj).
  destruct p, p0; destruct v, v0; try done;
  try ( 
  (repeat
    match goal with
      | [H: gv_inject _ (_ :: _) (_ :: _) |- _] => inv H
      | [H: MoreMem.val_inject _ _ _ |- _] => inv H
    end
  ); fail).

  inv Hinj; destruct gvs1, gvs2; try (by inv H6).
  inv H1; destruct (eq_nat_dec (wz0 + 1) (Size.to_nat Size.One)); [|done].
  apply EqDec.inj_right_pair in H2.
  apply EqDec.inj_right_pair in H4.
  subst; done.
Qed.

Lemma SELECT_eq_check_value_implies_injection:
  forall md inv1 inv2 t cv1 lv1 rv1 cv2 lv2 rv2 lc1 lc2 alpha gmax li1 li2 olc1 olc2
    cgvs1 lgvs1 rgvs1 cgvs2 lgvs2 rgvs2 iso1 iso2
     mem1 mem2 cfg1 cfg2 i 
    (Hsu1: self_use_check (ret insn_select i cv1 t lv1 rv1) = true)
    (Hsu2: self_use_check (ret insn_select i cv2 t lv2 rv2) = true)
    (Heqc: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value cv1) (vars_aux.add_ntag_value cv2) = true)
    (Heql: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value lv1) (vars_aux.add_ntag_value lv2) = true)
    (Heqr: eq_check_value md inv1 inv2
      (vars_aux.add_ntag_value rv1) (vars_aux.add_ntag_value rv2) = true)
    (Hmdsem: maydiff_sem
      (if isGVZero (CurTargetData cfg1) cgvs1
        then updateAddAL GVs lc1 i rgvs1
        else updateAddAL GVs lc1 i lgvs1)
      (if isGVZero (CurTargetData cfg2) cgvs2
        then updateAddAL GVs lc2 i rgvs2
        else updateAddAL GVs lc2 i lgvs2)
      alpha olc1 olc2 
      (IdExtSetImpl.add (vars_aux.add_ntag i)
        (IdExtSetImpl.add (vars_aux.add_ntag i) md)))
    (Hinvsem: invariant_sem cfg1 cfg2
      (if isGVZero (CurTargetData cfg1) cgvs1
        then updateAddAL GVs lc1 i rgvs1
        else updateAddAL GVs lc1 i lgvs1)
      (if isGVZero (CurTargetData cfg2) cgvs2
        then updateAddAL GVs lc2 i rgvs2
        else updateAddAL GVs lc2 i lgvs2)
      mem1 mem2
      olc1 olc2 gmax li1 li2 (mkInvariant inv1 inv2 iso1 iso2))
    (Hvwf: wf_sb_mi gmax alpha mem1 mem2)
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))

    (Hcov1: getOperandValue (CurTargetData cfg1) cv1 lc1 (Globals cfg1) = ret cgvs1)
    (Hlov1: getOperandValue (CurTargetData cfg1) lv1 lc1 (Globals cfg1) = ret lgvs1)
    (Hrov1: getOperandValue (CurTargetData cfg1) rv1 lc1 (Globals cfg1) = ret rgvs1)
    (Hcov2: getOperandValue (CurTargetData cfg2) cv2 lc2 (Globals cfg2) = ret cgvs2)
    (Hlov2: getOperandValue (CurTargetData cfg2) lv2 lc2 (Globals cfg2) = ret lgvs2)
    (Hrov2: getOperandValue (CurTargetData cfg2) rv2 lc2 (Globals cfg2) = ret rgvs2),
    match
      lookupAL GVs
      (if isGVZero (CurTargetData cfg1) cgvs1
        then updateAddAL GVs lc1 i rgvs1
        else updateAddAL GVs lc1 i lgvs1) i
      with
      | ret lrgvs1 =>
        match
          lookupAL GVs
          (if isGVZero (CurTargetData cfg2) cgvs2
            then updateAddAL GVs lc2 i rgvs2
            else updateAddAL GVs lc2 i lgvs2) i
          with
          | ret lrgvs2 => gv_inject alpha lrgvs1 lrgvs2
          | merror => False
        end
      | merror =>
        match
          lookupAL GVs
          (if isGVZero (CurTargetData cfg2) cgvs2
            then updateAddAL GVs lc2 i rgvs2
            else updateAddAL GVs lc2 i lgvs2) i
          with
          | ret _ => False
          | merror => True
        end
    end.
Proof.
  eq_check_value_tac.
  rewrite AtomSetFacts.union_b in Hniv; apply orb_false_iff in Hniv;
    inversion Hniv as [Hnicv2 Hnilv2]; clear Hniv.
  rewrite AtomSetFacts.union_b in Hniv1; apply orb_false_iff in Hniv1;
    inversion Hniv1 as [Hnicv1 Hnilv1]; clear Hniv1.

  remember (isGVZero (CurTargetData cfg1) cgvs1) as iz1.
  remember (isGVZero (CurTargetData cfg2) cgvs2) as iz2.
  destruct iz1, iz2; repeat rewrite lookupAL_updateAddAL_eq.

  - eapply getOperandValue_eq_check_value_implies_injection.
    + apply Hniv2. + apply Hniv0. + apply Heqr.
    + apply Hmdsem. + apply Hinvsem. + apply Hvwf. + apply Htd. + apply Hgequiv.
    + eauto. + eauto.

  - hexploit getOperandValue_eq_check_value_implies_injection.
    + apply Hnicv1. + apply Hnicv2. + apply Heqc.
    + apply Hmdsem. + apply Hinvsem. + apply Hvwf. + apply Htd. + apply Hgequiv.
    + eauto. + eauto.
    intro Hcinj.
    hexploit injection_implies_isGVZero_equal; eauto.
    instantiate (1:=(CurTargetData cfg1)).
    intro Hcontr; rewrite Htd in *.
    rewrite <- Heqiz1, <- Heqiz2 in Hcontr; done.

  - hexploit getOperandValue_eq_check_value_implies_injection.
    + apply Hnicv1. + apply Hnicv2. + apply Heqc.
    + apply Hmdsem. + apply Hinvsem. + apply Hvwf. + apply Htd. + apply Hgequiv.
    + eauto. + eauto.
    intro Hcinj.
    hexploit injection_implies_isGVZero_equal; eauto.
    instantiate (1:=(CurTargetData cfg1)).
    intro Hcontr; rewrite Htd in *.
    rewrite <- Heqiz1, <- Heqiz2 in Hcontr; done.

  - eapply getOperandValue_eq_check_value_implies_injection.
    + apply Hnilv1. + apply Hnilv2. + apply Heql.
    + apply Hmdsem. + apply Hinvsem. + apply Hvwf. + apply Htd. + apply Hgequiv.
    + eauto. + eauto.
Qed.

Lemma is_defined_same_id_false_implies_inter_empty:
  forall nd ocmd1 ocmd2
    (Hnd: nd = AtomSetImpl.inter (vars_aux.def_cmd_opt ocmd1)
      (vars_aux.def_cmd_opt ocmd2))
    (Heqbsame: false = vars_aux.is_defined_same_id ocmd1 ocmd2),
    nd[=]empty.
Proof.
  intros; clear -Hnd Heqbsame.
  destruct ocmd1 as [cmd1|]; destruct ocmd2 as [cmd2|].
  - unfold vars_aux.is_defined_same_id in Heqbsame; simpl in *.
  destruct (vars_aux.def_cmd cmd1), (vars_aux.def_cmd cmd2).
  + by rewrite Hnd; apply AtomSetFacts2.inter_singleton_2.
  + hexploit AtomSetProperties.empty_inter_2.
  instantiate (1:=empty); done.
  instantiate (1:=(singleton i0)); intro Hres.
  rewrite <- Hnd in Hres.
  eapply AtomSetProperties.empty_is_empty_1; eauto.
  + hexploit AtomSetProperties.empty_inter_1.
  instantiate (1:=empty); done.
  instantiate (1:=(singleton i0)); intro Hres.
  rewrite <- Hnd in Hres.
  eapply AtomSetProperties.empty_is_empty_1; eauto.
  + hexploit AtomSetProperties.empty_inter_1.
  instantiate (1:=empty); done.
  instantiate (1:=empty); intro Hres.
  rewrite <- Hnd in Hres.
  eapply AtomSetProperties.empty_is_empty_1; eauto.      

  - hexploit AtomSetProperties.empty_inter_2; try by instantiate (1:=empty).
  instantiate (1:= (vars_aux.def_cmd_opt (ret cmd1))).
  intro Hempty.
  simpl in Hempty; simpl in Hnd; rewrite <- Hnd in Hempty.
  apply AtomSetProperties.empty_is_empty_1; done.

  - hexploit AtomSetProperties.empty_inter_1; try by instantiate (1:=empty).
  instantiate (1:= (vars_aux.def_cmd_opt (ret cmd2))).
  intro Hempty.
  simpl in Hempty; simpl in Hnd; rewrite <- Hnd in Hempty.
  apply AtomSetProperties.empty_is_empty_1; done.

  - hexploit AtomSetProperties.empty_inter_1; try by instantiate (1:=empty).
  instantiate (1:= empty).
  intro Hempty.
  simpl in Hnd; rewrite <- Hnd in Hempty.
  apply AtomSetProperties.empty_is_empty_1; done.
Qed.
