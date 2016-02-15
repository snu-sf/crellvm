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
Import vars_aux.

Section HintSemEach.

  Ltac destruct_tac :=
    unfold vgtac.is_true in *;
    repeat match goal with
             | [ |- negb _ = true ] => apply negb_true_iff
             | [ |- _ || _ = false ] => (rewrite orb_false_iff; split)
             | [ |- IdExtSetImpl.mem _ (IdExtSetImpl.add _ _) = false ] =>
               rewrite IdExtSetFacts.add_b
             | [ |- IdExtSetImpl.mem _ (IdExtSetImpl.union _ _) = false ] =>
               rewrite IdExtSetFacts.union_b
             | [H: negb _ = true |- _] => apply negb_true_iff in H
             | [H: _ || _ = false |- _] => rewrite orb_false_iff in H; inv H
             | [H: IdExtSetImpl.mem _ (IdExtSetImpl.add _ _) = false |- _] =>
               rewrite IdExtSetFacts.add_b in H
             | [H: IdExtSetImpl.mem _ (IdExtSetImpl.union _ _) = false |- _] =>
               rewrite IdExtSetFacts.union_b in H
           end.

  Ltac rhs_destruct_tac_1 :=
    repeat match goal with
             | [H: match ?a with | ret _ => _ | merror => merror end = ret _ |- _] =>
               let ov := fresh "ov" in
                 remember a as ov; destruct ov; [|done]
             | [H: match ?a with | ret _ => _ | merror => False end |- _] =>
                 remember a as ov; destruct ov; [|done]
           end.

  Ltac rhs_destruct_tac_2 :=
    repeat match goal with
             | [H: ret _ = ?a |-
               match ?a with | ret _ => _ | merror => merror end = ret _] =>
             rewrite <- H
           end; try done.

  (* Definitions for getting information nd_(ntag_new) \notin inv' *)
  Definition id_not_used_in_eqs_eq_reg (y: id_ext) (rs: EqRegSetImpl.t) :=
    forall x r (He: EqRegSetImpl.mem (x, r) rs),
      negb (IdExtSetImpl.mem y (IdExtSetImpl.add x (used_locals_in_rhs r))).
  Definition id_not_used_in_eqs_eq_heap (y: id_ext) (hs: EqHeapSetImpl.t) :=
    forall p t a v (He: EqHeapSetImpl.mem (p,t,a,v) hs),
      negb (IdExtSetImpl.mem y
        (IdExtSetImpl.union (used_locals_in_value p) (used_locals_in_value v))).
  Definition id_not_used_in_eqs_neq_reg (y: id_ext) (nrs: NeqRegSetImpl.t) :=
    forall x r (He: NeqRegSetImpl.mem (x, r) nrs),
      negb (IdExtSetImpl.mem y (IdExtSetImpl.add x (used_locals_in_localglobal r))).
  Definition id_not_used_in_eqs (y: id_ext) (e: eqs_t) :=
    id_not_used_in_eqs_eq_reg y (eqs_eq_reg e) /\
    id_not_used_in_eqs_eq_heap y (eqs_eq_heap e) /\
    id_not_used_in_eqs_neq_reg y (eqs_neq_reg e).
  Definition od_not_used_in_eqs (od: list atom) (e: eqs_t) :=
    forall y (Hy: List.In y od), id_not_used_in_eqs (y, ntag_old) e.
  Definition nd_not_used_in_eqs (nd: list atom) (e: eqs_t) :=
    forall y (Hy: List.In y nd), id_not_used_in_eqs (y, ntag_new) e.
  Definition oldnew_olc_prop nd lc olc :=
    forall x (Hx: List.In x nd), lookupAL GVs lc x = lookupAL GVs olc x.
  Definition oldnew_prop nd lc olc inv :=
    oldnew_olc_prop nd lc olc /\ nd_not_used_in_eqs nd inv.

  (* Auxiliary lemmas before defining variables and hypotheses. *)
  Lemma not_used_preserves_getOperandValue:
    forall cfg olc lc i iv v
      (Hmem: IdExtSetImpl.mem (i, ntag_new) (used_locals_in_value v) = false),
      getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg) =
      getOperandValueExt (CurTargetData cfg) v olc
      (updateAddAL GVs lc i iv) (Globals cfg).
  Proof.
    intros; destruct v; [|done].
    simpl; destruct x as [x [|]]; simpl; [done|]; simpl in Hmem.
    assert (Hnix: i0 <> x).
    { intro Hcontr; subst x.
      rewrite IdExtSetFacts2.F.singleton_b in Hmem.
      unfold IdExtSetFacts2.F.eqb in Hmem.
      destruct (IdExtSetFacts.eq_dec (i0, ntag_new) (i0, ntag_new)); done.
    }
    apply lookupAL_updateAddAL_neq; eauto.
  Qed.

  Lemma not_used_preserves_rhs:
    forall cfg olc lc i iv r gvs
      (Hmem: IdExtSetImpl.mem (i, ntag_new) (used_locals_in_rhs r) = false),
      rhs_ext_value_sem cfg olc lc r gvs <->
      rhs_ext_value_sem cfg olc (updateAddAL GVs lc i iv) r gvs.
  Proof.
    intros; split; intros.

    - destruct r; try (inv H; fail); simpl in Hmem; destruct_tac.
      + inv H; econstructor.
        unfold BOPEXT in *.
        rhs_destruct_tac_1.
        repeat rewrite <- not_used_preserves_getOperandValue; eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold FBOPEXT in *.
        rhs_destruct_tac_1.
        repeat rewrite <- not_used_preserves_getOperandValue; eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor; eauto;
        rewrite <- not_used_preserves_getOperandValue; eauto.
      + inv H; econstructor; eauto;
        rewrite <- not_used_preserves_getOperandValue; eauto.
      + inv H; econstructor; eauto.
        * rewrite <- not_used_preserves_getOperandValue; eauto.
        * clear H10. generalize dependent vidxss.
          induction lsv as [|[sa va] lsv]; [done|].
          intros; simpl.
          unfold used_locals_in_lsv in H1; simpl in H1.
          destruct_tac.
          inv H9.
          remember (getOperandValueExt (CurTargetData cfg) va olc
            lc (Globals cfg)) as vaov; destruct vaov; [|done].
          symmetry in Heqvaov.
          rewrite not_used_preserves_getOperandValue with (i:=i0) (iv:=iv) in Heqvaov;
            eauto; rewrite Heqvaov.
          destruct (values2GenericValueExt (CurTargetData cfg) lsv olc lc (Globals cfg));
            try done.
          hexploit IHlsv; try done.
          by intros Hind; rewrite Hind.
      + inv H; econstructor.
        unfold TRUNCEXT in *.
        rhs_destruct_tac_1.
        repeat rewrite <- not_used_preserves_getOperandValue; eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold EXTEXT in *.
        rhs_destruct_tac_1.
        repeat rewrite <- not_used_preserves_getOperandValue; eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold CASTEXT in *.
        rhs_destruct_tac_1.
        repeat rewrite <- not_used_preserves_getOperandValue; eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold ICMPEXT in *.
        rhs_destruct_tac_1.
        repeat rewrite <- not_used_preserves_getOperandValue; eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold FCMPEXT in *.
        rhs_destruct_tac_1.
        repeat rewrite <- not_used_preserves_getOperandValue; eauto.
        rhs_destruct_tac_2.
      + inv H.
        * eapply rhs_ext_select_true_sem; eauto.
            rewrite <- not_used_preserves_getOperandValue; eauto.
            rewrite <- not_used_preserves_getOperandValue; eauto.
        * eapply rhs_ext_select_false_sem; eauto.
            rewrite <- not_used_preserves_getOperandValue; eauto.
            rewrite <- not_used_preserves_getOperandValue; eauto.
      + inv H; econstructor; eauto;
        rewrite <- not_used_preserves_getOperandValue; eauto.

    - destruct r; try (inv H; fail); simpl in Hmem; destruct_tac.
      + inv H; econstructor.
        unfold BOPEXT in *.
        rhs_destruct_tac_1.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=w); eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold FBOPEXT in *.
        rhs_destruct_tac_1.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=w); eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor; eauto;
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
      + inv H; econstructor; eauto.
        * erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        * erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=w); eauto.
      + inv H; econstructor; eauto.
        * erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        * clear H10. generalize dependent vidxss.
          induction lsv as [|[sa va] lsv]; [done|].
          intros; simpl.
          unfold used_locals_in_lsv in H1; simpl in H1.
          destruct_tac.
          inv H9.
          remember (getOperandValueExt (CurTargetData cfg) va olc
            (updateAddAL GVs lc i0 iv) (Globals cfg)) as vaov; destruct vaov; [|done].
          symmetry in Heqvaov.
          rewrite <- not_used_preserves_getOperandValue in Heqvaov;
            eauto; rewrite Heqvaov.
          destruct (values2GenericValueExt (CurTargetData cfg) lsv olc
            (updateAddAL GVs lc i0 iv) (Globals cfg)); try done.
          hexploit IHlsv; try done.
          by intros Hind; rewrite Hind.
      + inv H; econstructor.
        unfold TRUNCEXT in *.
        rhs_destruct_tac_1.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold EXTEXT in *.
        rhs_destruct_tac_1.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold CASTEXT in *.
        rhs_destruct_tac_1.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold ICMPEXT in *.
        rhs_destruct_tac_1.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=w); eauto.
        rhs_destruct_tac_2.
      + inv H; econstructor.
        unfold FCMPEXT in *.
        rhs_destruct_tac_1.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=w); eauto.
        rhs_destruct_tac_2.
      + inv H.
        * eapply rhs_ext_select_true_sem; eauto.
            erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
            erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=w); eauto.
        * eapply rhs_ext_select_false_sem; eauto.
            erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
            erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=z); eauto.
      + inv H; econstructor; eauto;
        erewrite not_used_preserves_getOperandValue with (iv:=iv) (v:=v); eauto.
  Qed.

  Lemma id_not_used_preserves_eq_reg_sem:
    forall cfg olc lc i iv mem gmax x r
      (Hidnuse: negb (IdExtSetImpl.mem (i, ntag_new)
        (IdExtSetImpl.add x (used_locals_in_rhs r)))),
      eq_reg_sem cfg olc lc mem gmax x r <->
      eq_reg_sem cfg olc (updateAddAL GVs lc i iv) mem gmax x r.
  Proof.
    intros.
    rewrite IdExtSetFacts.add_b in Hidnuse; apply negb_true_iff in Hidnuse;
      apply orb_false_iff in Hidnuse; destruct Hidnuse as [Hxieq Hmem].
    split; intros.

    - inv H.
      + eapply eq_reg_sem_value; eauto.
        * destruct x as [x [|]]; simpl; simpl in Hlookup; [done|].
          unfold IdExtSetFacts.eqb in Hxieq.
          destruct (IdExtSetFacts.eq_dec (x, ntag_new) (i0, ntag_new)); [done|].
          rewrite <- lookupAL_updateAddAL_neq; eauto.
          intro Hcontr; subst x; elim n; done.
        * apply not_used_preserves_rhs; eauto.
      + eapply eq_reg_sem_old_alloca; eauto.
        destruct x as [x [|]]; simpl; simpl in Hlookup; [done|].
        unfold IdExtSetFacts.eqb in Hxieq.
        destruct (IdExtSetFacts.eq_dec (x, ntag_new) (i0, ntag_new)); [done|].
        rewrite <- lookupAL_updateAddAL_neq; eauto.
        intro Hcontr; subst x; elim n; done.

    - inv H.
      + eapply eq_reg_sem_value; eauto.
        * destruct x as [x [|]]; simpl; simpl in Hlookup; [done|].
          unfold IdExtSetFacts.eqb in Hxieq.
          destruct (IdExtSetFacts.eq_dec (x, ntag_new) (i0, ntag_new)); [done|].
          erewrite lookupAL_updateAddAL_neq; eauto.
          intro Hcontr; subst x; elim n; done.
        * eapply not_used_preserves_rhs; eauto.
      + eapply eq_reg_sem_old_alloca; eauto.
        destruct x as [x [|]]; simpl; simpl in Hlookup; [done|].
        unfold IdExtSetFacts.eqb in Hxieq.
        destruct (IdExtSetFacts.eq_dec (x, ntag_new) (i0, ntag_new)); [done|].
        erewrite lookupAL_updateAddAL_neq; eauto.
        intro Hcontr; subst x; elim n; done.
  Qed.

  Lemma id_not_used_preserves_eq_heap_sem:
    forall cfg olc lc i iv mem p t a v
      (Hidnuse: negb (IdExtSetImpl.mem (i, ntag_new)
        (IdExtSetImpl.union (used_locals_in_value p) (used_locals_in_value v)))),
      eq_heap_sem cfg olc lc mem p t a v <->
      eq_heap_sem cfg olc (updateAddAL GVs lc i iv) mem p t a v.
  Proof.
    intros; unfold vgtac.is_true in Hidnuse; destruct_tac.
    split; intros; unfold eq_heap_sem in *;
    [repeat rewrite <- not_used_preserves_getOperandValue; eauto|
     rewrite not_used_preserves_getOperandValue with (i:=i0) (iv:=iv) (v:=p); eauto;
     rewrite not_used_preserves_getOperandValue with (i:=i0) (iv:=iv) (v:=v); eauto].
  Qed.    

  Lemma id_not_used_preserves_neq_reg_sem:
    forall cfg olc lc i iv x r
      (Hidnuse: negb (IdExtSetImpl.mem (i, ntag_new)
        (IdExtSetImpl.add x (used_locals_in_localglobal r)))),
      neq_reg_sem cfg olc lc x r <->
      neq_reg_sem cfg olc (updateAddAL GVs lc i iv) x r.
  Proof.
    intros; unfold vgtac.is_true in Hidnuse; destruct_tac.
    split; intros; unfold neq_reg_sem in *.

    - destruct x as [x [|]]; simpl in *.
      + destruct (lookupAL GVs olc x); [|done]; destruct r; [|done].
        destruct i1 as [i1 [|]]; simpl in *; [done|].
        rewrite <- lookupAL_updateAddAL_neq; eauto.
        intro Hcontr; subst i1.
        rewrite IdExtSetFacts2.F.singleton_b in H0.
        unfold IdExtSetFacts2.F.eqb in H0.
        destruct (IdExtSetFacts.eq_dec (i0, ntag_new) (i0, ntag_new)); done.
      + rewrite <- lookupAL_updateAddAL_neq; eauto;
        [|by intro Hcontr; subst x; unfold IdExtSetFacts.eqb in H;
          destruct (IdExtSetFacts.eq_dec (i0, ntag_new) (i0, ntag_new))].
        destruct (lookupAL GVs lc x); [|done]; destruct r; [|done].            
        destruct i1 as [i1 [|]]; simpl in *; [done|].
        rewrite <- lookupAL_updateAddAL_neq; eauto.
        intro Hcontr; subst i1.
        rewrite IdExtSetFacts2.F.singleton_b in H0.
        unfold IdExtSetFacts2.F.eqb in H0.
        destruct (IdExtSetFacts.eq_dec (i0, ntag_new) (i0, ntag_new)); done.

    - destruct x as [x [|]]; simpl in *.
      + destruct (lookupAL GVs olc x); [|done]; destruct r; [|done].
        destruct i1 as [i1 [|]]; simpl in *; [done|].
        rewrite lookupAL_updateAddAL_neq with (id0:=i0) (gv0:=iv); eauto.
        intro Hcontr; subst i1.
        rewrite IdExtSetFacts2.F.singleton_b in H0.
        unfold IdExtSetFacts2.F.eqb in H0.
        destruct (IdExtSetFacts.eq_dec (i0, ntag_new) (i0, ntag_new)); done.
      + rewrite lookupAL_updateAddAL_neq with (id0:=i0) (gv0:=iv); eauto;
        [|by intro Hcontr; subst x; unfold IdExtSetFacts.eqb in H;
          destruct (IdExtSetFacts.eq_dec (i0, ntag_new) (i0, ntag_new))].
        destruct (lookupAL GVs (updateAddAL GVs lc i0 iv) x); [|done];
          destruct r; [|done].
        destruct i1 as [i1 [|]]; simpl in *; [done|].
        rewrite lookupAL_updateAddAL_neq with (id0:=i0) (gv0:=iv); eauto.
        intro Hcontr; subst i1.
        rewrite IdExtSetFacts2.F.singleton_b in H0.
        unfold IdExtSetFacts2.F.eqb in H0.
        destruct (IdExtSetFacts.eq_dec (i0, ntag_new) (i0, ntag_new)); done.
  Qed.

  Lemma id_not_used_preserves_eqs_sem:
    forall cfg olc lc i iv mem gmax inv (Hidnuse: id_not_used_in_eqs (i, ntag_new) inv),
      eqs_sem cfg olc lc mem gmax inv <->
      eqs_sem cfg olc (updateAddAL GVs lc i iv) mem gmax inv.
  Proof.
    intros.
    unfold id_not_used_in_eqs in Hidnuse; destruct Hidnuse as [Hureg [Huheap Hunreg]].
    split; intros; unfold eqs_sem in *; destruct H as [Hreg [Hheap Hnreg]].

    splits;
    [unfold eqs_eq_reg_sem in *; intros; exploit Hreg; eauto;
     eapply id_not_used_preserves_eq_reg_sem; eauto|
     unfold eqs_eq_heap_sem in *; intros; exploit Hheap; eauto;
     eapply id_not_used_preserves_eq_heap_sem; eauto|
     unfold eqs_neq_reg_sem in *; intros; exploit Hnreg; eauto;
     eapply id_not_used_preserves_neq_reg_sem; eauto].

    splits;
    [unfold eqs_eq_reg_sem in *; intros; exploit Hreg; eauto;
     eapply id_not_used_preserves_eq_reg_sem; eauto|
     unfold eqs_eq_heap_sem in *; intros; exploit Hheap; eauto;
     eapply id_not_used_preserves_eq_heap_sem; eauto|
     unfold eqs_neq_reg_sem in *; intros; exploit Hnreg; eauto;
     eapply id_not_used_preserves_neq_reg_sem; eauto].
  Qed.

  Lemma id_notin_nd_preserves_lookup:
    forall cfg l1 phis pb lc id0 g
      (Heqiphis: ret l1 = getIncomingValuesForBlockFromPHINodes 
        (CurTargetData cfg) phis pb (Globals cfg) lc)
      (Hlookup: lookupAL GVs lc id0 = g)
      (Hnmem: ~ List.In id0 (def_phinodes phis)),
      lookupAL GVs (updateValuesForNewBlock l1 lc) id0 = g.
  Proof.
    intros.
    generalize dependent l1; induction phis; intros;
    [by simpl in *; inv Heqiphis; simpl|].
    
    simpl in Heqiphis.
    destruct a.
    destruct (getValueViaBlockFromValuels l0 pb); [|done].
    destruct (getOperandValue (CurTargetData cfg) v lc (Globals cfg)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes
      (CurTargetData cfg) phis pb (Globals cfg) lc) as idgvs.
    destruct idgvs; [|done].
    inv Heqiphis.

    simpl.
    assert (Hnii: id5 <> id0).
    { intro Hcontr; subst id5.
      simpl in Hnmem; elim Hnmem; left; done.
    }
    rewrite <- lookupAL_updateAddAL_neq; eauto.

    eapply IHphis; eauto.
    intro Hcontr; elim Hnmem; simpl; right; done.
  Qed.

  Definition list_sub {A} (l1 l2: list A) : Prop :=
    forall x (Hx: List.In x l1), List.In x l2.

  Lemma list_sub_refl: forall {A} (l: list A), list_sub l l.
  Proof. by intros; unfold list_sub. Qed.

  Lemma list_sub_in_l: 
    forall {A} (a: A) (l1 l2: list A) (H: list_sub (a::l1) l2), List.In a l2.
  Proof. by intros; apply H; left. Qed.

  Lemma list_sub_in_r: 
    forall {A} (a: A) (l1 l2: list A) (H: list_sub (a::l1) l2), list_sub l1 l2.
  Proof. by intros; unfold list_sub in *; intros; apply H; right. Qed.

  Lemma list_sub_app_l:
    forall {A} (l1 l2: list A), list_sub l1 (List.app l1 l2).
  Proof. by intros; unfold list_sub; intros; rewrite in_app; left. Qed.

  Lemma list_sub_app_r:
    forall {A} (l1 l2: list A), list_sub l2 (List.app l1 l2).
  Proof. by intros; unfold list_sub; intros; rewrite in_app; right. Qed.

  Lemma list_sub_atom_inter_l:
    forall (l1 l2: list atom), list_sub (atom_inter l1 l2) l1.
  Proof.
    by unfold atom_inter, list_sub; intros; rewrite filter_In in Hx; destruct Hx.
  Qed.

  Lemma list_sub_atom_inter_r:
    forall (l1 l2: list atom), list_sub (atom_inter l1 l2) l2.
  Proof.
    unfold atom_inter, list_sub; intros; rewrite filter_In in Hx; destruct Hx.
    destruct (in_dec id_dec x l2); done.
  Qed.

  Lemma phi_addphis_preserves_hint_sem_each_aux:
    forall lb b lpb pb lc lc' olc mem gmax cfg phis nd inv inv'
      (Hlb: lb = fst b) (Hlpb: lpb = fst pb)
      (Hlc': ret lc' = switchToNewBasicBlock (CurTargetData cfg) b pb (Globals cfg) lc)
      (Hphis: phis = getPHINodesFromBlock b)
      (Hnd: nd = def_phinodes phis)
      (Hinv': inv' = add_ntag_phis_to_eqs nd lpb inv phis)
      (Honp: oldnew_prop nd lc olc inv)
      (Hinv: eqs_sem cfg olc lc' mem gmax inv),
      eqs_sem cfg olc lc' mem gmax inv'.
  Proof.
    intros.
    unfold switchToNewBasicBlock in Hlc'.
    rewrite <- Hphis in Hlc'; clear Hphis.

    (* To use induction, we weaken one of hypotheses. *)
    assert (Hsub: list_sub (def_phinodes phis) nd).
    { rewrite Hnd; eapply list_sub_refl; eauto. }
    clear Hnd.

    generalize dependent inv'.
    generalize dependent nd.
    generalize dependent lc'.
    induction phis; intros;
      [by unfold add_ntag_phis_to_eqs in Hinv'; simpl in *; destruct inv;
        simpl in Hinv'; subst|].

    simpl in Hlc'.
    destruct a.
    remember (getValueViaBlockFromValuels l0 pb) as vpb; destruct vpb; [|done].
    remember (getOperandValue (CurTargetData cfg) v lc (Globals cfg)) as vov;
      destruct vov; [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
      (Globals cfg) lc) as iphis; destruct iphis; [|done].
    simpl in Hlc'; inversion Hlc'; subst lc'; clear Hlc'.
    simpl in Hsub.

    (* Drawing an induction hypothesis. *)
    exploit IHphis.
    { reflexivity. }
    { unfold oldnew_prop in Honp; destruct Honp as [_ Hnuse].
      unfold nd_not_used_in_eqs in Hnuse.
      exploit (Hnuse id5).
      { unfold vgtac.is_true.
        destruct (in_dec id_dec id5 nd); [done|]; elim n.
        eapply list_sub_in_l; eauto.
      }
      intros Hidnuse; eapply id_not_used_preserves_eqs_sem; eauto.
    }
    { eapply Honp. }
    { eapply list_sub_in_r; eauto. }
    { reflexivity. }
    intros Hindfact.

    unfold add_ntag_phis_to_eqs in Hinv'.
    unfold getValueViaBlockFromValuels in Heqvpb; rewrite <- Hlpb in Heqvpb.
    destruct Hindfact as [Hireg [Hiheap Hinreg]].
    subst inv'; unfold add_eq_reg, eqs_sem; splits; simpl;
      destruct inv as [ireg iheap inreg].

    Case "1. eq_reg case: filter and add".
    clear Hiheap Hinreg.
    unfold add_ntag_phis_to_eqs, eqs_eq_reg in *; simpl; rewrite <- Heqvpb.
    unfold eqs_eq_reg_sem in *; intros x r Hxrmem.
    rewrite EqRegSetFacts.add_b in Hxrmem.
    apply orb_true_iff in Hxrmem; destruct Hxrmem as [Hsingle|Hfind].
    
    SCase "1.1. for a newly-added phinode invariant".
    unfold EqRegSetFacts.eqb in Hsingle.
    destruct (EqRegSetFacts.eq_dec
      (add_ntag id5, rhs_ext_value (add_tag_value nd v)) (x, r)); [|done];
    clear Hsingle; inversion e; subst x r; clear e.
    eapply eq_reg_sem_value with (gvs':=g).
    { simpl; rewrite lookupAL_updateAddAL_eq; reflexivity. }
    { eapply rhs_ext_value__sem; eauto.
      destruct v; simpl.
      + unfold add_tag.
        remember (in_dec id_dec id0 nd) as mind; destruct mind.
        * simpl; unfold oldnew_prop in Honp; destruct Honp as [Holc _].
          unfold oldnew_olc_prop in Holc.
          rewrite <- Holc; eauto.
        * simpl; simpl in Heqvov; symmetry in Heqvov.
          assert (Hnii: id5 <> id0).
            intro Hcontr; subst id5.
            elim n; eapply list_sub_in_l; eauto.
          rewrite <- lookupAL_updateAddAL_neq; eauto.
          assert (Hmip: ~ List.In id0 (def_phinodes phis)).
            intro Hcontr; elim n.
            by eapply Hsub; right.
          eapply id_notin_nd_preserves_lookup; eauto.
      + by simpl in Heqvov.
    }
    { eapply eq_gvs_refl; eauto. }

    SCase "1.2. filtered others; must use induction hypothesis".
    unfold filter_local_in_eqs_eq_reg in Hfind.
    rewrite EqRegSetFacts.filter_b in Hfind;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in Hfind; destruct Hfind as [Hmem Hfilter].
    exploit Hireg; eauto; intros Hbrd.
    apply id_not_used_preserves_eq_reg_sem; eauto.

    Case "2. eq_heap case: filter only".
    clear Hireg Hinreg.
    unfold add_ntag_phis_to_eqs, eqs_eq_heap in *; rewrite <- Heqvpb.
    unfold eqs_eq_heap_sem in *; intros ip it ia iv Hipvmem.

    unfold filter_local_in_eqs_eq_heap in Hipvmem.
    rewrite EqHeapSetFacts.filter_b in Hipvmem;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in Hipvmem; destruct Hipvmem as [Hmem Hfilter].
    exploit Hiheap; eauto; intros Hbrd.
    apply id_not_used_preserves_eq_heap_sem; eauto.

    Case "3. neq_reg case: filter only".
    clear Hireg Hiheap.
    unfold add_ntag_phis_to_eqs, eqs_neq_reg in *; rewrite <- Heqvpb.
    unfold eqs_neq_reg_sem in *; intros x l Hxlmem.

    unfold filter_local_in_eqs_neq_reg in Hxlmem.
    rewrite NeqRegSetFacts.filter_b in Hxlmem;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in Hxlmem; destruct Hxlmem as [Hmem Hfilter].
    exploit Hinreg; eauto; intros Hbrd.
    apply id_not_used_preserves_neq_reg_sem; eauto.
  Qed.

  Lemma filter_preserves_id_not_used_in_eqs_eq_reg:
    forall a y inv
      (Hreg: id_not_used_in_eqs_eq_reg (y, ntag_old) inv) (Hn: a <> y),
      id_not_used_in_eqs_eq_reg (y, ntag_old)
      (filter_local_in_eqs_eq_reg (add_otag a) inv).
  Proof.
    intros.
    unfold id_not_used_in_eqs_eq_reg in *; intros.
    unfold filter_local_in_eqs_eq_reg in He.
    rewrite EqRegSetFacts.filter_b in He;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in He; destruct He as [Hmem Hnu].
    eapply Hreg; eauto.
  Qed.

  Lemma filter_preserves_id_not_used_in_eqs_eq_heap:
    forall a y inv
      (Hheap: id_not_used_in_eqs_eq_heap (y, ntag_old) inv) (Hn: a <> y),
      id_not_used_in_eqs_eq_heap (y, ntag_old)
      (filter_local_in_eqs_eq_heap (add_otag a) inv).
  Proof.
    intros.
    unfold id_not_used_in_eqs_eq_heap in *; intros.
    unfold filter_local_in_eqs_eq_heap in He.
    rewrite EqHeapSetFacts.filter_b in He;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in He; destruct He as [Hmem Hnu].
    eapply Hheap; eauto.
  Qed.

  Lemma filter_preserves_id_not_used_in_eqs_neq_reg:
    forall a y inv
      (Hnreg: id_not_used_in_eqs_neq_reg (y, ntag_old) inv) (Hn: a <> y),
      id_not_used_in_eqs_neq_reg (y, ntag_old)
      (filter_local_in_eqs_neq_reg (add_otag a) inv).
  Proof.
    intros.
    unfold id_not_used_in_eqs_neq_reg in *; intros.
    unfold filter_local_in_eqs_neq_reg in He.
    rewrite NeqRegSetFacts.filter_b in He;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in He; destruct He as [Hmem Hnu].
    eapply Hnreg; eauto.
  Qed.

  Definition remove_olc_by_nd olc nd : GVsMap :=
    List.fold_right
      (fun x o => deleteAL _ o x)
      olc nd.

  Lemma remove_olc_by_nd_others_prop:
    forall x lc nd (Hnin: ~ In x nd),
      lookupAL GVs lc x = lookupAL GVs (remove_olc_by_nd lc nd) x.
  Proof.
    intros; induction nd; [done|].
    simpl in *; rewrite lookupAL_deleteAL_neq; eauto.
  Qed.

  Lemma remove_olc_prop_lookup:
    forall x id5 lc olc
      (Hneq: IdExtSetFacts.eqb x (add_otag id5) = false),
      lookupALExt olc lc x =
      lookupALExt (deleteAL GVs olc id5) lc x.
  Proof.
    intros.
    unfold IdExtSetFacts.eqb in Hneq.
    destruct (IdExtSetFacts.eq_dec x (add_otag id5)); [done|].
    destruct x as [x [|]]; simpl in *; [|done].
    rewrite lookupAL_deleteAL_neq; eauto.
    intro Hcontr; subst; elim n; done.
  Qed.

  Lemma remove_olc_prop_value:
    forall p id5 cfg lc olc
      (Hnmem: IdExtSetImpl.mem (add_otag id5) (used_locals_in_value p) = false),
      getOperandValueExt (CurTargetData cfg) p olc lc (Globals cfg) =
      getOperandValueExt (CurTargetData cfg) p (deleteAL GVs olc id5) lc (Globals cfg).
  Proof.
    intros; destruct p; simpl in *; [|done].
    rewrite IdExtSetFacts.singleton_b in *.
    eapply remove_olc_prop_lookup; eauto.
  Qed.

  Lemma remove_olc_prop_rhs:
    forall r id5 cfg lc olc gvs
      (Hnmem: IdExtSetImpl.mem (add_otag id5) (used_locals_in_rhs r) = false)
      (Hrhs : rhs_ext_value_sem cfg olc
        lc r gvs),
      rhs_ext_value_sem cfg (deleteAL GVs olc id5) lc r gvs.
  Proof.
    intros; inv Hrhs; simpl in *; destruct_tac.
    - econstructor.
      unfold BOPEXT in *.
      rhs_destruct_tac_1.
      repeat rewrite <- remove_olc_prop_value; eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold FBOPEXT in *.
      rhs_destruct_tac_1.
      repeat rewrite <- remove_olc_prop_value; eauto.
      rhs_destruct_tac_2.
    - econstructor; eauto; repeat rewrite <- remove_olc_prop_value; eauto.
    - econstructor; eauto; repeat rewrite <- remove_olc_prop_value; eauto.
    - econstructor; eauto; repeat rewrite <- remove_olc_prop_value; eauto.
      clear -H0 H4; generalize dependent vidxss; induction idxs; intros; [done|].
      destruct a; simpl in *; destruct_tac.
      remember (getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg))
      as vov; destruct vov; [|done].
      rewrite <- remove_olc_prop_value; eauto.
      remember (values2GenericValueExt (CurTargetData cfg) idxs olc lc (Globals cfg))
      as vs; destruct vs; [|done].
      rewrite <- Heqvov.
      by exploit IHidxs; eauto; intro Hbrd; rewrite Hbrd.
    - econstructor.
      unfold TRUNCEXT in *.
      rhs_destruct_tac_1.
      repeat rewrite <- remove_olc_prop_value; eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold EXTEXT in *.
      rhs_destruct_tac_1.
      repeat rewrite <- remove_olc_prop_value; eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold CASTEXT in *.
      rhs_destruct_tac_1.
      repeat rewrite <- remove_olc_prop_value; eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold ICMPEXT in *.
      rhs_destruct_tac_1.
      repeat rewrite <- remove_olc_prop_value; eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold FCMPEXT in *.
      rhs_destruct_tac_1.
      repeat rewrite <- remove_olc_prop_value; eauto.
      rhs_destruct_tac_2.
    - eapply rhs_ext_select_true_sem; eauto.
      repeat rewrite <- remove_olc_prop_value; eauto.
      repeat rewrite <- remove_olc_prop_value; eauto.
    - eapply rhs_ext_select_false_sem; eauto.
      repeat rewrite <- remove_olc_prop_value; eauto.
      repeat rewrite <- remove_olc_prop_value; eauto.
    - econstructor.
      repeat rewrite <- remove_olc_prop_value; eauto.

  Qed.

  Lemma remove_olc_prop_rhs_inv:
    forall r id5 cfg lc olc gvs
      (Hnmem: IdExtSetImpl.mem (add_otag id5) (used_locals_in_rhs r) = false)
      (Hrhs: rhs_ext_value_sem cfg (deleteAL GVs olc id5) lc r gvs),
      rhs_ext_value_sem cfg olc lc r gvs.
  Proof.
    intros.
    inv Hrhs; simpl in *; destruct_tac.
    - econstructor.
      unfold BOPEXT in *.
      rhs_destruct_tac_1.
      rewrite remove_olc_prop_value with (p:=v1) (id5:=id5); eauto.
      rewrite remove_olc_prop_value with (p:=v2) (id5:=id5); eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold FBOPEXT in *.
      rhs_destruct_tac_1.
      rewrite remove_olc_prop_value with (p:=v1) (id5:=id5); eauto.
      rewrite remove_olc_prop_value with (p:=v2) (id5:=id5); eauto.
      rhs_destruct_tac_2.
    - econstructor; eauto; rewrite remove_olc_prop_value with (p:=v) (id5:=id5); eauto.
    - econstructor; eauto.
      + rewrite remove_olc_prop_value with (p:=v) (id5:=id5); eauto.
      + rewrite remove_olc_prop_value with (p:=v') (id5:=id5); eauto.
    - econstructor; eauto.
      + rewrite remove_olc_prop_value with (p:=v) (id5:=id5); eauto.
      + clear -H0 H4; generalize dependent vidxss; induction idxs; intros; [done|].
        destruct a; simpl in *; destruct_tac.
        rhs_destruct_tac_1.
        rewrite remove_olc_prop_value with (p:=v) (id5:=id5); eauto.
        rewrite <- Heqov.
        by exploit IHidxs; eauto; intro Hbrd; rewrite Hbrd.
    - econstructor.
      unfold TRUNCEXT in *.
      rhs_destruct_tac_1.
      rewrite remove_olc_prop_value with (p:=v1) (id5:=id5); eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold EXTEXT in *.
      rhs_destruct_tac_1.
      rewrite remove_olc_prop_value with (p:=v1) (id5:=id5); eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold CASTEXT in *.
      rhs_destruct_tac_1.
      rewrite remove_olc_prop_value with (p:=v1) (id5:=id5); eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold ICMPEXT in *.
      rhs_destruct_tac_1.
      rewrite remove_olc_prop_value with (p:=v1) (id5:=id5); eauto.
      rewrite remove_olc_prop_value with (p:=v2) (id5:=id5); eauto.
      rhs_destruct_tac_2.
    - econstructor.
      unfold FCMPEXT in *.
      rhs_destruct_tac_1.
      rewrite remove_olc_prop_value with (p:=v1) (id5:=id5); eauto.
      rewrite remove_olc_prop_value with (p:=v2) (id5:=id5); eauto.
      rhs_destruct_tac_2.
    - eapply rhs_ext_select_true_sem; eauto.
      + rewrite remove_olc_prop_value with (p:=v0) (id5:=id5); eauto.
      + rewrite remove_olc_prop_value with (p:=v1) (id5:=id5); eauto.
    - eapply rhs_ext_select_false_sem; eauto.
      + rewrite remove_olc_prop_value with (p:=v0) (id5:=id5); eauto.
      + rewrite remove_olc_prop_value with (p:=v2) (id5:=id5); eauto.
    - econstructor.
      rewrite remove_olc_prop_value with (p:=v) (id5:=id5); eauto.
  Qed.

  Lemma old_id_not_used_preserves_eqs_sem:
    forall id5 cfg lc olc mem0 gmax inv
      (Hinu: id_not_used_in_eqs (id5, ntag_old) inv)
      (Hinv : eqs_sem cfg (deleteAL GVs olc id5) lc mem0 gmax inv),
      eqs_sem cfg olc lc mem0 gmax inv.
  Proof.
    intros; unfold eqs_sem in *; destruct inv as [ireg iheap inreg]; simpl in *.
    destruct Hinv as [Hreg [Hheap Hnreg]].
    unfold id_not_used_in_eqs in Hinu; simpl in Hinu.
    destruct Hinu as [Hireg [Hiheap Hinreg]].
    splits.

    Case "1. regs".
    unfold eqs_eq_reg_sem in *; intros x r Hxr.
    exploit Hireg; eauto; intro Hnuse.
    exploit Hreg; eauto; intro Hbrd.
    destruct_tac.
    inv Hbrd.

    SSCase "1.1. eq_reg_sem_value".
    eapply eq_reg_sem_value; eauto.
    { erewrite remove_olc_prop_lookup; eauto. }
    { eapply remove_olc_prop_rhs_inv; eauto. }

    SSCase "1.2. eq_reg_sem_old_alloca".
    eapply eq_reg_sem_old_alloca; eauto.
    erewrite remove_olc_prop_lookup; eauto.

    SCase "2. heap".
    unfold eqs_eq_heap_sem in *; intros p t a v Hpv.
    exploit Hiheap; eauto; intro Hnuse.
    exploit Hheap; eauto; intro Hbrd.
    destruct_tac.
    unfold eq_heap_sem in *.
    rhs_destruct_tac_1.
    rewrite remove_olc_prop_value with (p:=p) (id5:=id5); eauto.
    rewrite remove_olc_prop_value with (p:=v) (id5:=id5); eauto.
    rewrite <- Heqov, <- Heqov0; eauto.

    SCase "3. nregs".
    unfold eqs_neq_reg_sem in *; intros x l Hxl.
    exploit Hinreg; eauto; intro Hnuse.
    exploit Hnreg; eauto; intro Hbrd.
    destruct_tac.
    unfold neq_reg_sem in *.
    rhs_destruct_tac_1.
    rewrite remove_olc_prop_lookup with (id5:=id5); eauto.
    rewrite <-Heqov; eauto.
    destruct l; [|done].
    rhs_destruct_tac_1.
    rewrite remove_olc_prop_lookup with (id5:=id5); eauto.
    rewrite <-Heqov0; eauto.
    simpl in H0; rewrite IdExtSetFacts.singleton_b in H0; done.
  Qed.

  Lemma phi_remove_old_preserves_invariant_sem:
    forall cfg olc lc lc' mem gmax b pb phis nd inv inv'
      (Hlc': ret lc' = switchToNewBasicBlock (CurTargetData cfg) b pb (Globals cfg) lc)
      (Hphis: phis = getPHINodesFromBlock b)
      (Hnd: nd = def_phinodes phis)
      (Hinv': inv' = remove_old_by_newdefs_list inv nd)
      (Hinv: eqs_sem cfg olc lc mem gmax inv),
      eqs_sem cfg (remove_olc_by_nd olc nd) lc mem gmax inv' /\
      od_not_used_in_eqs nd inv'.
  Proof.
    intros; split.

    Case "- eqs_sem preservation".
    intros.
    unfold switchToNewBasicBlock in Hlc'; rewrite <-Hphis in Hlc'; clear Hphis b.
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
      (Globals cfg) lc) as ivs; destruct ivs; [|done]; inv Hlc'.
    generalize dependent l0; induction phis; intros;
    [by unfold remove_old_by_newdefs_list; inv Heqivs|].

    clear Hinv; simpl in *. (* Hinv is used only in induction base case. *)
    destruct a.
    destruct (getValueViaBlockFromValuels l1 pb); [|done].
    destruct (getOperandValue (CurTargetData cfg) v lc (Globals cfg)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
      (Globals cfg) lc) as iphis; destruct iphis; [|done].
    inv Heqivs.
    destruct inv as [ireg iheap inreg].
    exploit IHphis; eauto; intro Hind; clear Heqiphis l2 IHphis; simpl in *.
    unfold remove_old_by_newdefs_list, eqs_sem in *.
    destruct Hind as [Hreg_ind [Hheap_ind Hnreg_ind]]; simpl in *.
    splits; simpl.

    SCase "1. regs".
    clear Hheap_ind Hnreg_ind.
    unfold eqs_eq_reg_sem in *; intros x r Hxr.
    unfold filter_local_in_eqs_eq_reg in Hxr.
    rewrite EqRegSetFacts.filter_b in Hxr;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in Hxr; destruct Hxr as [Hmem Hfilter].
    exploit Hreg_ind; eauto; intro Hind; clear Hreg_ind.
    destruct_tac.
    inv Hind.

    SSCase "1.1. eq_reg_sem_value".
    eapply eq_reg_sem_value; eauto.
    { rewrite <- remove_olc_prop_lookup; eauto. }
    { eapply remove_olc_prop_rhs; eauto. }

    SSCase "1.2. eq_reg_sem_old_alloca".
    eapply eq_reg_sem_old_alloca; eauto.
    rewrite <- remove_olc_prop_lookup; eauto.

    SCase "2. heap".
    clear Hreg_ind Hnreg_ind v.
    unfold eqs_eq_heap_sem in *; intros p t a v Hpv.
    unfold filter_local_in_eqs_eq_heap in Hpv.
    rewrite EqHeapSetFacts.filter_b in Hpv;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in Hpv; destruct Hpv as [Hmem Hfilter].
    exploit Hheap_ind; eauto; intro Hind; clear Hheap_ind.
    destruct_tac.
    unfold eq_heap_sem in *.
    remember (getOperandValueExt (CurTargetData cfg) p
      (remove_olc_by_nd olc (def_phinodes phis)) lc 
      (Globals cfg)) as pv; destruct pv; [|done].
    rewrite <- remove_olc_prop_value; eauto.
    remember (getOperandValueExt (CurTargetData cfg) v
      (remove_olc_by_nd olc (def_phinodes phis)) lc 
      (Globals cfg)) as vv; destruct vv; [|done].
    rewrite <- remove_olc_prop_value; eauto.
    rewrite <- Heqpv, <- Heqvv; eauto.

    SCase "3. nregs".
    clear Hreg_ind Hheap_ind.
    unfold eqs_neq_reg_sem in *; intros x lg Hxl.
    unfold filter_local_in_eqs_neq_reg in Hxl.
    rewrite NeqRegSetFacts.filter_b in Hxl;
      [|by unfold compat_bool, Proper, "==>"; intros; subst].
    apply andb_true_iff in Hxl; destruct Hxl as [Hmem Hfilter].
    exploit Hnreg_ind; eauto; intro Hind; clear Hnreg_ind.
    destruct_tac.
    unfold neq_reg_sem in *.
    remember (lookupALExt (remove_olc_by_nd olc (def_phinodes phis)) lc x) as xv;
      destruct xv; [|done].
    rewrite <- remove_olc_prop_lookup, <- Heqxv; eauto.
    destruct lg; [|done].
    remember (lookupALExt (remove_olc_by_nd olc (def_phinodes phis)) lc i0) as iv;
      destruct iv; [|done].
    simpl in H0; rewrite IdExtSetFacts.singleton_b in H0.
    rewrite <- remove_olc_prop_lookup, <- Heqiv; eauto.

    Case "- od_not_used_in_eqs".
    rewrite Hinv'; clear.
    induction nd; simpl; [done|].
    unfold od_not_used_in_eqs, remove_old_by_newdefs_list in *; intros; simpl.
    destruct Hy as [Hya|Hynd].

    SCase "1. a = y".
    subst a; clear; unfold id_not_used_in_eqs; simpl; splits;
      unfold id_not_used_in_eqs_eq_reg, id_not_used_in_eqs_eq_heap,
        id_not_used_in_eqs_neq_reg; intros;
      unfold filter_local_in_eqs_eq_reg, filter_local_in_eqs_eq_heap,
        filter_local_in_eqs_neq_reg in He;
      try (rewrite EqRegSetFacts.filter_b in He;
        [|by unfold compat_bool, Proper, "==>"; intros; subst]);
      try (rewrite EqHeapSetFacts.filter_b in He;
        [|by unfold compat_bool, Proper, "==>"; intros; subst]);
      try (rewrite NeqRegSetFacts.filter_b in He;
        [|by unfold compat_bool, Proper, "==>"; intros; subst]);
      unfold vgtac.is_true in *;
      apply andb_true_iff in He; destruct He as [Hmem Hnmem]; done.

    SCase "2. In y nd".
    exploit IHnd; eauto; intro Hbrd; clear IHnd.
    unfold id_not_used_in_eqs in *; simpl in *.
    destruct Hbrd as [Hreg [Hheap Hnreg]]; splits.

    SSCase "2.1. regs".
    destruct (id_dec a y).
    { subst a; clear; unfold id_not_used_in_eqs; simpl; splits;
      unfold id_not_used_in_eqs_eq_reg; intros;
      unfold filter_local_in_eqs_eq_reg  in He;
      rewrite EqRegSetFacts.filter_b in He;
        [|by unfold compat_bool, Proper, "==>"; intros; subst];
      unfold vgtac.is_true in *;
      apply andb_true_iff in He; destruct He as [Hmem Hnmem]; done.
    }
    { eapply filter_preserves_id_not_used_in_eqs_eq_reg; eauto. }

    SSCase "2.2. heap".
    destruct (id_dec a y).
    { subst a; clear; unfold id_not_used_in_eqs; simpl; splits;
      unfold id_not_used_in_eqs_eq_heap; intros;
      unfold filter_local_in_eqs_eq_heap  in He;
      rewrite EqHeapSetFacts.filter_b in He;
        [|by unfold compat_bool, Proper, "==>"; intros; subst];
      unfold vgtac.is_true in *;
      apply andb_true_iff in He; destruct He as [Hmem Hnmem]; done.
    }
    { eapply filter_preserves_id_not_used_in_eqs_eq_heap; eauto. }

    SSCase "2.3. nregs".
    destruct (id_dec a y).
    { subst a; clear; unfold id_not_used_in_eqs; simpl; splits;
      unfold id_not_used_in_eqs_neq_reg; intros;
      unfold filter_local_in_eqs_neq_reg  in He;
      rewrite NeqRegSetFacts.filter_b in He;
        [|by unfold compat_bool, Proper, "==>"; intros; subst];
      unfold vgtac.is_true in *;
      apply andb_true_iff in He; destruct He as [Hmem Hnmem]; done.
    }
    { eapply filter_preserves_id_not_used_in_eqs_neq_reg; eauto. }
  Qed.

  Lemma new_to_old_uniqueness_preserves_id:
    forall oi i xo (Hn: oi <> i)
      (Hneq: IdExtSetFacts.eqb xo (i, ntag_old) = false),
      IdExtSetFacts.eqb (new_to_old_local_in_id oi xo) (i, ntag_old) = false.
  Proof.
    intros.
    destruct xo as [x [|]]; simpl in *.
    - unfold IdExtSetFacts.eqb in *; destruct (id_dec oi x); done.
    - unfold IdExtSetFacts.eqb in *; destruct (id_dec oi x); [|done].
      subst x; unfold add_otag in *.
      destruct (IdExtSetFacts.eq_dec (oi, ntag_old) (i0, ntag_old)); [|done].
      by elim Hn; inv e.
  Qed.

  Lemma new_to_old_uniqueness_preserves_value:
    forall oi i v (Hn: oi <> i)
      (Hnmem: IdExtSetImpl.mem (i, ntag_old) (used_locals_in_value v) = false),
      IdExtSetImpl.mem (i, ntag_old)
      (used_locals_in_value (new_to_old_local_in_value oi v)) = false.
  Proof.
    intros; destruct v; simpl in *.
    - rewrite IdExtSetFacts.singleton_b in *.
      eapply new_to_old_uniqueness_preserves_id; eauto.
    - eapply IdExtSetFacts.empty_b; eauto.
  Qed.

  Lemma new_to_old_uniqueness_preserves_rhs:
    forall oi i ro (Hn: oi <> i)
      (Hnmem: IdExtSetImpl.mem (i, ntag_old) (used_locals_in_rhs ro) = false),
      IdExtSetImpl.mem (i, ntag_old)
      (used_locals_in_rhs (new_to_old_local_in_rhs oi ro)) = false.
  Proof.
    intros.
    destruct ro; try done; simpl in *; destruct_tac;
    repeat match goal with
      | [ |- IdExtSetImpl.mem _ (used_locals_in_value
        (new_to_old_local_in_value _ ?v)) = false ] => (destruct v; simpl in *)
      | [ |- IdExtSetImpl.mem _ (IdExtSetImpl.singleton
        (new_to_old_local_in_id _ ?x)) = false ] =>
        (rewrite IdExtSetFacts.singleton_b in *; simpl in *)
      | [ |- IdExtSetFacts.eqb (new_to_old_local_in_id _ _) (i0, ntag_old) = false ] =>
        (eapply new_to_old_uniqueness_preserves_id; eauto)
      | [ |- IdExtSetImpl.mem _ IdExtSetImpl.empty = false ] =>
        (eapply IdExtSetFacts2.F.empty_b; eauto)
    end.

    (* lsv case left. *)
    clear H; induction lsv; [done|]; simpl in *.
    destruct a; simpl in *; destruct_tac.
    - destruct v0; simpl in *.
      + rewrite IdExtSetFacts.singleton_b in *; simpl in *.
        eapply new_to_old_uniqueness_preserves_id; eauto.
      + eapply IdExtSetFacts2.F.empty_b; eauto.
    - eapply IHlsv; eauto.
  Qed.

  Lemma new_to_old_uniqueness_preserves_eqs_eq_reg:
    forall pinv ninv i phis
      (Huniq: negb (in_dec id_dec i (def_phinodes phis)) = true)
      (Hninv: ninv =
        fold_right
        (fun (x : id) (acc : EqRegSetImpl.t) =>
          new_to_old_local_in_eq_reg x acc) pinv (def_phinodes phis))
      (Hinur: id_not_used_in_eqs_eq_reg (i, ntag_old) pinv),
      id_not_used_in_eqs_eq_reg (i, ntag_old) ninv.
  Proof.
    intros.
    destruct (in_dec id_dec i0 (def_phinodes phis)); [done|]; clear Huniq.
    generalize dependent ninv; induction phis; intros; [by simpl in *; subst|].
    assert (Hindin: ~ In i0 (def_phinodes phis)).
    { by intro Hcontr; elim n; right. }

    simpl in Hninv.
    remember (fold_right
      (fun (x : id) (acc : EqRegSetImpl.t) =>
        new_to_old_local_in_eq_reg x acc) pinv 
      (def_phinodes phis)) as indinv; clear Heqindinv.
    hexploit IHphis; eauto; intro Hind; clear IHphis.
    rewrite Hninv; clear Hninv ninv.

    unfold id_not_used_in_eqs_eq_reg in *; intros.
    unfold new_to_old_local_in_eq_reg in He.
    exploit EqRegSetFacts2.in_fold_exists; eauto.
    intros [[xo ro] [Hmem Hxr]].
    exploit Hind; eauto; intro Hbrd.
    unfold new_to_old_local_in_idrhs in Hxr; inv Hxr.
    destruct a; simpl in *.
    destruct_tac.
    - eapply new_to_old_uniqueness_preserves_id; eauto.
    - eapply new_to_old_uniqueness_preserves_rhs; eauto.
  Qed.

  Lemma new_to_old_uniqueness_preserves_eqs_eq_heap:
    forall pinv ninv i phis
      (Huniq: negb (in_dec id_dec i (def_phinodes phis)) = true)
      (Hninv: ninv =
        fold_right
        (fun (x : id) (acc : EqHeapSetImpl.t) =>
          new_to_old_local_in_eq_heap x acc) pinv (def_phinodes phis))
      (Hinur: id_not_used_in_eqs_eq_heap (i, ntag_old) pinv),
      id_not_used_in_eqs_eq_heap (i, ntag_old) ninv.
  Proof.
    intros.
    destruct (in_dec id_dec i0 (def_phinodes phis)); [done|]; clear Huniq.
    generalize dependent ninv; induction phis; intros; [by simpl in *; subst|].
    assert (Hindin: ~ In i0 (def_phinodes phis)).
    { by intro Hcontr; elim n; right. }

    simpl in Hninv.
    remember (fold_right
      (fun (x : id) (acc : EqHeapSetImpl.t) =>
        new_to_old_local_in_eq_heap x acc) pinv 
      (def_phinodes phis)) as indinv; clear Heqindinv.
    hexploit IHphis; eauto; intro Hind; clear IHphis.
    rewrite Hninv; clear Hninv ninv.

    unfold id_not_used_in_eqs_eq_heap in *; intros.
    unfold new_to_old_local_in_eq_heap in He.
    exploit EqHeapSetFacts2.in_fold_exists; eauto.
    intros [[[[po tto] ao] vo] [Hmem Hpv]].
    exploit Hind; eauto; intro Hbrd.
    unfold new_to_old_local_in_vv in Hpv; inv Hpv.
    destruct a; simpl in *.
    destruct_tac; eapply new_to_old_uniqueness_preserves_value; eauto.
  Qed.

  Lemma new_to_old_uniqueness_preserves_eqs_neq_reg:
    forall pinv ninv i phis
      (Huniq: negb (in_dec id_dec i (def_phinodes phis)) = true)
      (Hninv: ninv =
        fold_right
        (fun (x : id) (acc : NeqRegSetImpl.t) =>
          new_to_old_local_in_neq_reg x acc) pinv (def_phinodes phis))
      (Hinur: id_not_used_in_eqs_neq_reg (i, ntag_old) pinv),
      id_not_used_in_eqs_neq_reg (i, ntag_old) ninv.
  Proof.
    intros.
    destruct (in_dec id_dec i0 (def_phinodes phis)); [done|]; clear Huniq.
    generalize dependent ninv; induction phis; intros; [by simpl in *; subst|].
    assert (Hindin: ~ In i0 (def_phinodes phis)).
    { by intro Hcontr; elim n; right. }

    simpl in Hninv.
    remember (fold_right
      (fun (x : id) (acc : NeqRegSetImpl.t) =>
        new_to_old_local_in_neq_reg x acc) pinv 
      (def_phinodes phis)) as indinv; clear Heqindinv.
    hexploit IHphis; eauto; intro Hind; clear IHphis.
    rewrite Hninv; clear Hninv ninv.

    unfold id_not_used_in_eqs_neq_reg in *; intros.
    unfold new_to_old_local_in_neq_reg in He.
    exploit NeqRegSetFacts2.in_fold_exists; eauto.
    intros [[xo lgo] [Hmem Hxl]].
    exploit Hind; eauto; intro Hbrd.
    unfold new_to_old_local_in_idlg in Hxl; inv Hxl.
    destruct a; simpl in *.
    destruct_tac.
    - eapply new_to_old_uniqueness_preserves_id; eauto.
    - destruct lgo; simpl in *.
      + rewrite IdExtSetFacts.singleton_b in *.
        eapply new_to_old_uniqueness_preserves_id; eauto.
      + eapply IdExtSetFacts.empty_b; eauto.
  Qed.

  Lemma old_id_not_used_preserves_lookup:
    forall olc lc i g xo
      (Hneq: IdExtSetFacts.eqb xo (i, ntag_old) = false),
      lookupALExt olc lc xo =
      lookupALExt
      match lookupAL GVs lc i with
        | ret ov => updateAddAL GVs olc i ov
        | merror => deleteAL GVs olc i
      end (updateAddAL GVs lc i g) (new_to_old_local_in_id i xo).
  Proof.
    intros.
    unfold IdExtSetFacts.eqb in Hneq.
    destruct (IdExtSetFacts.eq_dec xo (i0, ntag_old)); [done|]; clear Hneq.
    destruct xo as [x [|]]; simpl in *.

    Case "1. xo is old".
    destruct (id_dec i0 x); [by subst; elim n|]; simpl.
    remember (lookupAL GVs lc i0) as iv; destruct iv.
    { rewrite <- lookupAL_updateAddAL_neq; eauto. }
    { rewrite lookupAL_deleteAL_neq; eauto. }

    Case "2. xo is new".
    destruct (id_dec i0 x); simpl in *.
    - subst x; remember (lookupAL GVs lc i0) as iv; destruct iv.
      + rewrite lookupAL_updateAddAL_eq; eauto.
      + rewrite lookupAL_deleteAL_eq; eauto.
    - rewrite <- lookupAL_updateAddAL_neq; eauto.
  Qed.

  Lemma old_id_not_used_preserves_value:
    forall cfg olc lc v i g 
      (Hnmem: IdExtSetImpl.mem (i, ntag_old) (used_locals_in_value v) = false),
      getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg) =
      getOperandValueExt (CurTargetData cfg) (new_to_old_local_in_value i v)
      match lookupAL GVs lc i with
        | ret ov => updateAddAL GVs olc i ov
        | merror => deleteAL GVs olc i
      end (updateAddAL GVs lc i g) (Globals cfg).
  Proof.
    intros; destruct v; simpl in *; [|done].
    rewrite IdExtSetFacts.singleton_b in Hnmem.
    eapply old_id_not_used_preserves_lookup; eauto.
  Qed.

  Lemma old_id_not_used_preserves_rhs:
    forall cfg olc lc i g ro gvs
      (Hnmem: IdExtSetImpl.mem (i, ntag_old) (used_locals_in_rhs ro) = false)
      (Hrhs: rhs_ext_value_sem cfg olc lc ro gvs),
      rhs_ext_value_sem cfg
      match lookupAL GVs lc i with
        | ret ov => updateAddAL GVs olc i ov
        | merror => deleteAL GVs olc i
      end (updateAddAL GVs lc i g) (new_to_old_local_in_rhs i ro) gvs.
  Proof.
    intros; destruct ro; inv Hrhs.
    - econstructor; unfold BOPEXT in *; simpl in *; destruct_tac.
      rhs_destruct_tac_1.
      repeat rewrite <- old_id_not_used_preserves_value; eauto.
      rhs_destruct_tac_2.
    - econstructor; unfold FBOPEXT in *; simpl in *; destruct_tac.
      rhs_destruct_tac_1.
      repeat rewrite <- old_id_not_used_preserves_value; eauto.
      rhs_destruct_tac_2.
    - econstructor; eauto.
      rewrite <- old_id_not_used_preserves_value; eauto.
    - econstructor; eauto; simpl in *; destruct_tac;
      rewrite <- old_id_not_used_preserves_value; eauto.
    - econstructor; eauto; simpl in *; destruct_tac.
      + rewrite <- old_id_not_used_preserves_value; eauto.
      + clear -H6 H0. generalize dependent vidxss; induction lsv; intros; [done|].
        destruct a; simpl in *; destruct_tac.
        rhs_destruct_tac_1.
        rewrite <- old_id_not_used_preserves_value; eauto.
        exploit IHlsv; eauto; intro Hbrd.
        rhs_destruct_tac_2; rewrite Hbrd; done.
    - econstructor; unfold TRUNCEXT in *; simpl in *; destruct_tac.
      rhs_destruct_tac_1.
      rewrite <- old_id_not_used_preserves_value; eauto.
      rhs_destruct_tac_2.
    - econstructor; unfold EXTEXT in *; simpl in *; destruct_tac.
      rhs_destruct_tac_1.
      rewrite <- old_id_not_used_preserves_value; eauto.
      rhs_destruct_tac_2.
    - econstructor; unfold CASTEXT in *; simpl in *; destruct_tac.
      rhs_destruct_tac_1.
      rewrite <- old_id_not_used_preserves_value; eauto.
      rhs_destruct_tac_2.
    - econstructor; unfold ICMPEXT in *; simpl in *; destruct_tac.
      rhs_destruct_tac_1.
      repeat rewrite <- old_id_not_used_preserves_value; eauto.
      rhs_destruct_tac_2.
    - econstructor; unfold FCMPEXT in *; simpl in *; destruct_tac.
      rhs_destruct_tac_1.
      repeat rewrite <- old_id_not_used_preserves_value; eauto.
      rhs_destruct_tac_2.
    - eapply rhs_ext_select_true_sem; eauto; simpl in *; destruct_tac.
      + rewrite <- old_id_not_used_preserves_value; eauto.
      + rewrite <- old_id_not_used_preserves_value; eauto.
    - eapply rhs_ext_select_false_sem; eauto; simpl in *; destruct_tac.
      + rewrite <- old_id_not_used_preserves_value; eauto.
      + rewrite <- old_id_not_used_preserves_value; eauto.
    - econstructor; rewrite <- old_id_not_used_preserves_value; eauto.
  Qed.

  Lemma old_id_not_used_preserves_eq_reg_sem:
    forall cfg olc lc mem0 gmax xo ro i g regs
      (Hmem: EqRegSetImpl.mem (xo, ro) regs)
      (Hinufr: id_not_used_in_eqs_eq_reg (i, ntag_old) regs)
      (Hxro: eq_reg_sem cfg olc lc mem0 gmax xo ro),
      eq_reg_sem cfg
      match lookupAL GVs lc i with
        | ret ov => updateAddAL GVs olc i ov
        | merror => deleteAL GVs olc i
      end (updateAddAL GVs lc i g) mem0 gmax (new_to_old_local_in_id i xo)
      (new_to_old_local_in_rhs i ro).
  Proof.
    intros; exploit Hinufr; eauto; intro Hnu.
    destruct_tac. inv Hxro.

    Case "1. values".
    eapply eq_reg_sem_value; eauto.
    { rewrite <- old_id_not_used_preserves_lookup; eauto. }
    { eapply old_id_not_used_preserves_rhs; eauto. }

    Case "2. old_alloca".
    eapply eq_reg_sem_old_alloca; eauto.
    rewrite <- old_id_not_used_preserves_lookup; eauto.
  Qed.

  Lemma old_id_not_used_preserves_eq_heap_sem:
    forall cfg olc lc mem0 po tto ao vo i g heaps
      (Hmem: EqHeapSetImpl.mem (po, tto, ao, vo) heaps)
      (Hinufr: id_not_used_in_eqs_eq_heap (i, ntag_old) heaps)
      (Hxro: eq_heap_sem cfg olc lc mem0 po tto ao vo),
      eq_heap_sem cfg
      match lookupAL GVs lc i with
        | ret ov => updateAddAL GVs olc i ov
        | merror => deleteAL GVs olc i
      end (updateAddAL GVs lc i g) mem0 (new_to_old_local_in_value i po)
      tto ao (new_to_old_local_in_value i vo).
  Proof.
    intros; exploit Hinufr; eauto; intro Hnu.
    destruct_tac.
    unfold eq_heap_sem in *.
    rhs_destruct_tac_1.
    repeat rewrite <- old_id_not_used_preserves_value; eauto.
    by rewrite <-Heqov, <-Heqov0.
  Qed.

  Lemma old_id_not_used_preserves_neq_reg_sem:
    forall cfg olc lc xo lo i g nregs
      (Hmem: NeqRegSetImpl.mem (xo, lo) nregs)
      (Hinufr: id_not_used_in_eqs_neq_reg (i, ntag_old) nregs)
      (Hxro: neq_reg_sem cfg olc lc xo lo),
      neq_reg_sem cfg
      match lookupAL GVs lc i with
        | ret ov => updateAddAL GVs olc i ov
        | merror => deleteAL GVs olc i
      end (updateAddAL GVs lc i g) (new_to_old_local_in_id i xo)
      (new_to_old_local_in_localglobal i lo).
  Proof.
    intros; exploit Hinufr; eauto; intro Hnu.
    destruct_tac.
    unfold neq_reg_sem in *.
    rhs_destruct_tac_1.
    rewrite <- old_id_not_used_preserves_lookup, <-Heqov; eauto.
    destruct lo; simpl in *; [|done].
    clear Heqov; rhs_destruct_tac_1.
    rewrite <-old_id_not_used_preserves_lookup, <-Heqov; eauto.
    rewrite IdExtSetFacts.singleton_b in H0; done.
  Qed.

  Definition update_olc_by_vs olc lc vs :=
    List.fold_right
    (fun xv lo =>
      let '(x, v) := xv in let '(l, o) := lo in
        (updateAddAL GVs l x v,
          match (lookupAL GVs l x) with
            | ret ov => updateAddAL GVs o x ov
            | merror => deleteAL GVs o x
          end))
    (lc, olc) vs.

  Lemma update_olc_by_vs_uniqueness_prop_1:
    forall cfg olc lc i g x vs pb phis
      (Hnin: negb (in_dec id_dec i (def_phinodes phis)) = true)
      (Heqindvs : ret vs = getIncomingValuesForBlockFromPHINodes 
        (CurTargetData cfg) phis pb (Globals cfg) lc)
      (Hinind : In x (def_phinodes phis)),
      lookupAL GVs (snd (update_olc_by_vs olc lc vs)) x =
      lookupAL GVs (snd (update_olc_by_vs olc lc ((i, g) :: vs))) x.
  Proof.
    intros.
    destruct (in_dec id_dec i0 (def_phinodes phis)); [done|]; clear Hnin.
    assert (Hnix: i0 <> x).
    { intro Hcontr; subst i0; elim n; done. }
    simpl.
    remember (update_olc_by_vs olc lc vs) as plc;
      destruct plc as [plc polc]; simpl in *.
    destruct (lookupAL GVs plc i0).
    - rewrite <- lookupAL_updateAddAL_neq; eauto.
    - rewrite lookupAL_deleteAL_neq; eauto.
  Qed.

  Lemma update_olc_by_vs_uniqueness_prop_2:
    forall cfg olc lc olc' lc' vs pb phis i
      (Hni: negb (in_dec id_dec i (def_phinodes phis)))
      (Heqindvs : ret vs = getIncomingValuesForBlockFromPHINodes 
        (CurTargetData cfg) phis pb (Globals cfg) lc)
      (Heqdcvs: (lc', olc') = update_olc_by_vs olc lc vs),
      lookupAL GVs lc i = lookupAL GVs lc' i.
  Proof.
    intros.
    destruct (in_dec id_dec i0 (def_phinodes phis)); [done|]; clear Hni.
    generalize dependent olc'; generalize dependent lc'; generalize dependent vs;
    induction phis; intros; [by inv Heqindvs; simpl in *; inv Heqdcvs|].
    simpl in n.

    simpl in Heqindvs.
    destruct a.
    destruct (getValueViaBlockFromValuels l0 pb); [|done].
    destruct (getOperandValue (CurTargetData cfg) v lc (Globals cfg)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
      (Globals cfg) lc) as indvs; destruct indvs; [|done].
    inv Heqindvs; simpl in Heqdcvs.
    remember (update_olc_by_vs olc lc l1) as il; destruct il as [ilc iolc].

    exploit IHphis; eauto; intro Hbrd.
    rewrite Hbrd; inv Heqdcvs.
    rewrite <- lookupAL_updateAddAL_neq; eauto.
  Qed.

  Lemma update_olc_by_vs_uniqueness_prop_3:
    forall cfg olc lc olc' lc' vs pb phis i
      (Hni: ~ In i (def_phinodes phis))
      (Heqindvs : ret vs = getIncomingValuesForBlockFromPHINodes 
        (CurTargetData cfg) phis pb (Globals cfg) lc)
      (Heqdcvs: (lc', olc') = update_olc_by_vs olc lc vs),
      lookupAL GVs olc i = lookupAL GVs olc' i.
  Proof.
    intros.
    generalize dependent vs; generalize dependent lc'; generalize dependent olc'.
    induction phis; intros; [by inv Heqindvs; inv Heqdcvs|].
    simpl in *.
    destruct a.
    destruct (getValueViaBlockFromValuels l0 pb); [|done].
    destruct (getOperandValue (CurTargetData cfg) v lc (Globals cfg)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
      (Globals cfg) lc) as ivs; destruct ivs; [|done].
    simpl in *; inversion Heqindvs; subst vs; clear Heqindvs.
    simpl in *; remember (update_olc_by_vs olc lc l1) as ov;
      destruct ov as [indlc indolc]; inv Heqdcvs.
    destruct (lookupAL GVs indlc id5).
    - rewrite <- lookupAL_updateAddAL_neq; eauto.
    - rewrite lookupAL_deleteAL_neq; eauto.
  Qed.

  Lemma update_olc_by_vs_uniqueness_prop_4:
    forall cfg olc lc olc' lc' vs pb phis i
      (Huniq: is_uniq_def_phinodes phis)
      (Hi: In i (def_phinodes phis))
      (Heqindvs : ret vs = getIncomingValuesForBlockFromPHINodes 
        (CurTargetData cfg) phis pb (Globals cfg) lc)
      (Heqdcvs: (lc', olc') = update_olc_by_vs olc lc vs),
      lookupAL GVs olc' i = lookupAL GVs lc i.
  Proof.
    intros.
    generalize dependent vs; generalize dependent lc'; generalize dependent olc'.
    induction phis; intros; [by inv Heqindvs; inv Heqdcvs|].
    simpl in *.
    destruct a.
    destruct (getValueViaBlockFromValuels l0 pb); [|done].
    destruct (getOperandValue (CurTargetData cfg) v lc (Globals cfg)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
      (Globals cfg) lc) as ivs; destruct ivs; [|done].
    simpl in *; inversion Heqindvs; subst vs; clear Heqindvs.
    simpl in *; remember (update_olc_by_vs olc lc l1) as ov;
      destruct ov as [indlc indolc]; inv Heqdcvs.
    apply andb_true_iff in Huniq; destruct Huniq as [Hninid Hiuniq].
    apply negb_true_iff in Hninid.

    destruct Hi as [Heq|Hindin].

    - subst.
      remember (lookupAL GVs indlc i0) as indiv; destruct indiv.
      + rewrite lookupAL_updateAddAL_eq; rewrite Heqindiv.
        symmetry; eapply update_olc_by_vs_uniqueness_prop_2; eauto.
        unfold vgtac.is_true; apply negb_true_iff; done.
      + rewrite lookupAL_deleteAL_eq; rewrite Heqindiv.
        symmetry; eapply update_olc_by_vs_uniqueness_prop_2; eauto.
        unfold vgtac.is_true; apply negb_true_iff; done.

    - destruct (in_dec id_dec id5 (def_phinodes phis)); [done|]; clear Hninid.
      assert (Hnii: id5 <> i0).
      { by intro Hcontr; subst; elim n. }
      exploit IHphis; eauto; intro Hbrd.
      remember (lookupAL GVs indlc id5) as indiv; destruct indiv.
      + rewrite <-lookupAL_updateAddAL_neq; eauto.
      + rewrite lookupAL_deleteAL_neq; eauto.
  Qed.

  Lemma phi_new_to_old_preserves_invariant_sem:
    forall cfg olc lc lc' mem gmax pb phis nd inv inv' vs
      (Huniq: is_uniq_def_phinodes phis)
      (Hnd: nd = def_phinodes phis)
      (Hvs: ret vs = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg)
        phis pb (Globals cfg) lc)
      (Hlc': lc' = updateValuesForNewBlock vs lc)
      (Hinv': inv' = new_to_old_by_newdefs_list inv nd)
      (Hnu: od_not_used_in_eqs nd inv)
      (Hinv: eqs_sem cfg (remove_olc_by_nd olc nd) lc mem gmax inv),
      eqs_sem cfg (snd (update_olc_by_vs olc lc vs)) lc' mem gmax inv'.
  Proof.
    intros; subst.
    generalize dependent vs; induction phis; intros; [by inv Hvs|].

    simpl in *.
    destruct a; simpl in Hinv.
    symmetry in Hvs; rhs_destruct_tac_1.
    inversion Hvs; subst vs; clear Hvs.
    destruct inv as [ireg iheap inreg].
    apply andb_true_iff in Huniq; destruct Huniq as [Huniqi Huniqp].
    exploit IHphis; eauto.
    { move Hnu at bottom; simpl in Hnu.
      unfold od_not_used_in_eqs in *; intros.
      by eapply Hnu; eauto; right.
    }
    { simpl in Hnu; unfold od_not_used_in_eqs in Hnu.
      exploit Hnu. left; reflexivity. intro Hinu.
      eapply old_id_not_used_preserves_eqs_sem; eauto.
    }
    intro Hind; clear IHphis; simpl in *.

    unfold eqs_sem in Hind; destruct Hind as [Hrind [Hhind Hnrind]].
    unfold od_not_used_in_eqs in Hnu; exploit Hnu. left; reflexivity. intro Hinu.
    unfold id_not_used_in_eqs in Hinu; simpl in Hinu.
    destruct Hinu as [Hinur [Hinuh Hinunr]].
    remember (update_olc_by_vs olc lc l1) as folc; destruct folc as [flc folc].
    simpl in *.
    assert (Hflc: flc = updateValuesForNewBlock l1 lc).
    { clear -Heqfolc.
      generalize dependent flc; generalize dependent folc.
      induction l1; intros; [by simpl in *; inv Heqfolc|].
      destruct a; unfold update_olc_by_vs in Heqfolc; simpl in Heqfolc.
      remember (update_olc_by_vs olc lc l1) as plo.
      destruct plo as [plc polc].
      exploit IHl1; eauto; intros Hind.
      simpl; rewrite <- Hind.
      unfold update_olc_by_vs in Heqplo.
      rewrite <- Heqplo in Heqfolc.
      inv Heqfolc; done.
    }
    rewrite <- Hflc in *; clear Hflc.
    unfold new_to_old_by_newdefs_list, eqs_sem; simpl in *; splits.

    Case "1. regs".
    unfold eqs_eq_reg_sem in *; intros x r Hxr.
    unfold new_to_old_local_in_eq_reg in Hxr.
    exploit EqRegSetFacts2.in_fold_exists; eauto.
    intros [[xo ro] [Hmem Hoeq]].
    unfold new_to_old_local_in_idrhs in Hoeq; inversion Hoeq; subst x r; clear Hoeq.
    exploit Hrind; eauto; intro Hxro.
    hexploit new_to_old_uniqueness_preserves_eqs_eq_reg; eauto; intros Hinufr.
    eapply old_id_not_used_preserves_eq_reg_sem; eauto.

    Case "2. heap".
    unfold eqs_eq_heap_sem in *; intros p t a v' Hpv.
    unfold new_to_old_local_in_eq_heap in Hpv.
    exploit EqHeapSetFacts2.in_fold_exists; eauto.
    intros [[[[po tto] ao] vo] [Hmem Hoeq]].
    unfold new_to_old_local_in_vv in Hoeq; inversion Hoeq; subst p t a v'; clear Hoeq.
    exploit Hhind; eauto; intro Hpvo.
    hexploit new_to_old_uniqueness_preserves_eqs_eq_heap; eauto; intros Hinufh.
    eapply old_id_not_used_preserves_eq_heap_sem; eauto.

    Case "3. nregs".
    unfold eqs_neq_reg_sem in *; intros x l Hxl.
    unfold new_to_old_local_in_neq_reg in Hxl.
    exploit NeqRegSetFacts2.in_fold_exists; eauto.
    intros [[xo lo] [Hmem Hoeq]].
    unfold new_to_old_local_in_idlg in Hoeq; inversion Hoeq; subst x l; clear Hoeq.
    exploit Hnrind; eauto; intro Hxlo.
    hexploit new_to_old_uniqueness_preserves_eqs_neq_reg; eauto; intros Hinufnr.
    eapply old_id_not_used_preserves_neq_reg_sem; eauto.
  Qed.

  Lemma phi_oldnew_preserves_invariant_sem:
    forall cfg olc lc lc' mem gmax b pb phis nd vs inv inv'
      (Huniq: is_uniq_def_phinodes phis)
      (Hvs: ret vs = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg)
        phis pb (Globals cfg) lc)
      (Hlc': lc' = updateValuesForNewBlock vs lc)
      (Hphis: phis = getPHINodesFromBlock b)
      (Hnd: nd = def_phinodes phis)
      (Hinv': inv' = new_to_old_by_newdefs_list (remove_old_by_newdefs_list inv nd) nd)
      (Hinv: eqs_sem cfg olc lc mem gmax inv),
      eqs_sem cfg (snd (update_olc_by_vs olc lc vs)) lc' mem gmax inv'.
  Proof.
    intros.
    exploit phi_remove_old_preserves_invariant_sem; eauto.
    { instantiate (1:=pb); instantiate (1:=lc').
      by unfold switchToNewBasicBlock; rewrite <-Hphis, <-Hvs, <-Hlc'.
    }
    intros [Hstep Hnu].
    eapply phi_new_to_old_preserves_invariant_sem; eauto.
  Qed.

  Lemma oldnew_preserves_id_not_used_id:
    forall xo y a
      (H: IdExtSetFacts.eqb xo (y, ntag_new) = false),
      IdExtSetFacts.eqb (new_to_old_local_in_id a xo) (y, ntag_new) = false.
  Proof.
    intros; destruct xo as [xo [|]]; simpl in *.
    - destruct (id_dec a xo); done.
    - destruct (id_dec a xo); [|done]; subst a.
      unfold IdExtSetFacts.eqb.
      destruct (IdExtSetFacts.eq_dec (add_otag xo) (y, ntag_new)); done.
  Qed.

  Lemma oldnew_preserves_id_not_used_value:
    forall y v a
      (H: IdExtSetImpl.mem (y, ntag_new) (used_locals_in_value v) = false),
      IdExtSetImpl.mem (y, ntag_new)
      (used_locals_in_value (new_to_old_local_in_value a v)) = false.
  Proof.
    intros; destruct v; simpl in *; [|done].
    rewrite IdExtSetFacts.singleton_b in *.
    eapply oldnew_preserves_id_not_used_id; eauto.
  Qed.

  Lemma oldnew_preserves_id_not_used_in_eqs_eq_reg:
    forall a y inv
      (Hreg: id_not_used_in_eqs_eq_reg (y, ntag_new) inv) (Hn: a <> y),
      id_not_used_in_eqs_eq_reg (y, ntag_new)
      (new_to_old_local_in_eq_reg a inv).
  Proof.
    intros.
    unfold id_not_used_in_eqs_eq_reg in *; intros.
    unfold new_to_old_local_in_eq_reg in He.
    exploit EqRegSetFacts2.in_fold_exists; eauto.
    intros [[xo ro] [Hmem Hoeq]].
    unfold new_to_old_local_in_idrhs in Hoeq; inv Hoeq.
    exploit Hreg; eauto; intro Hxro.
    unfold vgtac.is_true in *; destruct_tac.
    - eapply oldnew_preserves_id_not_used_id; eauto.
    - clear -H0; destruct ro; try done; simpl in *; destruct_tac;
      try (eapply oldnew_preserves_id_not_used_value; eauto).
      clear -H1; induction lsv; [done|].
      destruct a0; simpl in *; destruct_tac.
      + eapply oldnew_preserves_id_not_used_value; eauto.
      + eapply IHlsv; eauto.
  Qed.

  Lemma oldnew_preserves_id_not_used_in_eqs_eq_heap:
    forall a y inv
      (Hheap: id_not_used_in_eqs_eq_heap (y, ntag_new) inv) (Hn: a <> y),
      id_not_used_in_eqs_eq_heap (y, ntag_new)
      (new_to_old_local_in_eq_heap a inv).
  Proof.
    intros.
    unfold id_not_used_in_eqs_eq_heap in *; intros.
    unfold new_to_old_local_in_eq_heap in He.
    exploit EqHeapSetFacts2.in_fold_exists; eauto.
    intros [[[[vo tyo] ao] po] [Hmem Hoeq]].
    unfold new_to_old_local_in_vv in Hoeq; inv Hoeq.
    exploit Hheap; eauto; intro Hyro.
    unfold vgtac.is_true in *; destruct_tac;
      eapply oldnew_preserves_id_not_used_value; eauto.
  Qed.

  Lemma oldnew_preserves_id_not_used_in_eqs_neq_reg:
    forall a y inv
      (Hnreg: id_not_used_in_eqs_neq_reg (y, ntag_new) inv) (Hn: a <> y),
      id_not_used_in_eqs_neq_reg (y, ntag_new)
      (new_to_old_local_in_neq_reg a inv).
  Proof.
    intros.
    unfold id_not_used_in_eqs_neq_reg in *; intros.
    unfold new_to_old_local_in_neq_reg in He.
    exploit NeqRegSetFacts2.in_fold_exists; eauto.
    intros [[xo lgo] [Hmem Hoeq]].
    unfold new_to_old_local_in_idlg in Hoeq; inv Hoeq.
    exploit Hnreg; eauto; intro Hyro.
    unfold vgtac.is_true in *; destruct_tac.
    - eapply oldnew_preserves_id_not_used_id; eauto.
    - destruct lgo; simpl in *; [|done].
      rewrite IdExtSetFacts.singleton_b in *.
      eapply oldnew_preserves_id_not_used_id; eauto.
  Qed.

  Lemma oldnew_implies_id_not_used_id:
    forall a ox, IdExtSetFacts.eqb (new_to_old_local_in_id a ox) (a, ntag_new) = false.
  Proof.
    intros.
    destruct ox as [ox [|]]; simpl.
    - destruct (id_dec a ox); unfold add_otag, add_ntag; unfold IdExtSetFacts.eqb;
      destruct (IdExtSetFacts.eq_dec (ox, ntag_old) (a, ntag_new)); done.
    - destruct (id_dec a ox); unfold add_otag, add_ntag; unfold IdExtSetFacts.eqb.
      + subst a; destruct (IdExtSetFacts.eq_dec (ox, ntag_old) (ox, ntag_new)); done.
      + destruct (IdExtSetFacts.eq_dec (ox, ntag_new) (a, ntag_new)); [|done].
        by elim n; inv e.
  Qed.

  Lemma oldnew_implies_id_not_used_value:
    forall a op,
      IdExtSetImpl.mem (a, ntag_new)
      (used_locals_in_value (new_to_old_local_in_value a op)) = false.
  Proof.
    intros; destruct op.
    - simpl; rewrite IdExtSetFacts.singleton_b; apply oldnew_implies_id_not_used_id.
    - simpl; apply IdExtSetFacts.empty_b.
  Qed.

  Lemma oldnew_implies_id_not_used_lg:
    forall a or,
      IdExtSetImpl.mem (a, ntag_new)
      (used_locals_in_localglobal (new_to_old_local_in_localglobal a or)) = false.
  Proof.
    intros; destruct or.
    - simpl; rewrite IdExtSetFacts.singleton_b; apply oldnew_implies_id_not_used_id.
    - simpl; apply IdExtSetFacts.empty_b.
  Qed.

  Lemma oldnew_implies_id_not_used_rhs:
    forall a or,
      IdExtSetImpl.mem (a, ntag_new)
      (used_locals_in_rhs (new_to_old_local_in_rhs a or)) = false.
  Proof.
    intros; destruct or; simpl; destruct_tac;
      try (eapply oldnew_implies_id_not_used_value; eauto);
      try (apply IdExtSetFacts.empty_b).

    (* lsv proof *)
    induction lsv; [by apply IdExtSetFacts.empty_b|].
    destruct a0; simpl; destruct_tac; [|done].
    eapply oldnew_implies_id_not_used_value; eauto.
  Qed.

  Lemma oldnew_implies_id_not_used_eq_reg:
    forall inv inv' a (Hinv': inv' = new_to_old_local_in_eq_reg a inv),
      id_not_used_in_eqs_eq_reg (a, ntag_new) inv'.
  Proof.
    intros; rewrite Hinv'.
    unfold id_not_used_in_eqs_eq_reg; intros.
    unfold new_to_old_local_in_eq_reg in He.
    exploit EqRegSetFacts2.in_fold_exists; eauto.
    intros [[ox or] [Hxrmem Hxrn2o]].
    unfold new_to_old_local_in_idrhs in Hxrn2o; inv Hxrn2o.
    rewrite IdExtSetFacts.add_b.
    apply negb_true_iff, orb_false_iff; split.
    - eapply oldnew_implies_id_not_used_id; eauto.
    - eapply oldnew_implies_id_not_used_rhs; eauto.
  Qed.

  Lemma oldnew_implies_id_not_used_eq_heap:
    forall inv inv' a (Hinv': inv' = new_to_old_local_in_eq_heap a inv),
      id_not_used_in_eqs_eq_heap (a, ntag_new) inv'.
  Proof.
    intros; rewrite Hinv'.
    unfold id_not_used_in_eqs_eq_heap; intros.
    unfold new_to_old_local_in_eq_heap in He.
    exploit EqHeapSetFacts2.in_fold_exists; eauto.
    intros [[[[op ot] oa] ov] [Hpvmem Hpvn2o]].
    unfold new_to_old_local_in_vv in Hpvn2o; inv Hpvn2o.
    rewrite IdExtSetFacts.union_b.
    apply negb_true_iff, orb_false_iff; split;
      eapply oldnew_implies_id_not_used_value; eauto.
  Qed.

  Lemma oldnew_implies_id_not_used_neq_reg:
    forall inv inv' a (Hinv': inv' = new_to_old_local_in_neq_reg a inv),
      id_not_used_in_eqs_neq_reg (a, ntag_new) inv'.
  Proof.
    intros; rewrite Hinv'.
    unfold id_not_used_in_eqs_neq_reg; intros.
    unfold new_to_old_local_in_neq_reg in He.
    exploit NeqRegSetFacts2.in_fold_exists; eauto.
    intros [[ox or] [Hxrmem Hxrn2o]].
    unfold new_to_old_local_in_idlg in Hxrn2o; inv Hxrn2o.
    rewrite IdExtSetFacts.add_b.
    apply negb_true_iff, orb_false_iff; split.
    - eapply oldnew_implies_id_not_used_id; eauto.
    - eapply oldnew_implies_id_not_used_lg; eauto.
  Qed.

  Lemma oldnew_implies_oldnew_prop:
    forall inv inv' nd cfg lc olc vs pb phis
      (Hnd: nd = def_phinodes phis)
      (Huniq: is_uniq_def_phinodes phis)
      (Hinv: inv' = new_to_old_by_newdefs_list (remove_old_by_newdefs_list inv nd) nd)
      (Hvs: ret vs = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg)
        phis pb (Globals cfg) lc),
      oldnew_prop nd lc (snd (update_olc_by_vs olc lc vs)) inv'.
  Proof.
    intros; unfold oldnew_prop; split.

    Case "1. oldnew_olc_prop".
    clear Hinv; unfold oldnew_olc_prop; intros.
    generalize dependent nd; generalize dependent vs;
    induction phis; simpl in *; intros; [by inv Hvs|].
    destruct a.
    destruct (getValueViaBlockFromValuels l0 pb); [|done].
    destruct (getOperandValue (CurTargetData cfg) v lc (Globals cfg)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
      (Globals cfg) lc) as indvs; destruct indvs; [|done]; inv Hvs.
    simpl in Huniq; apply andb_true_iff in Huniq; destruct Huniq as [Hnin Hinduniq].
    simpl in Hx; destruct Hx as [Hl|Hinind].
    { subst x; simpl.
      remember (update_olc_by_vs olc lc l1) as dcvs; destruct dcvs; simpl.
      exploit update_olc_by_vs_uniqueness_prop_2; eauto.
      intro Hres; rewrite Hres.
      destruct (lookupAL GVs a id5).
      + rewrite lookupAL_updateAddAL_eq; eauto.
      + rewrite lookupAL_deleteAL_eq; eauto.
    }
    { exploit IHphis; eauto.
      { by rewrite app_nil_r. }
      intro Hbrd; rewrite Hbrd.
      eapply update_olc_by_vs_uniqueness_prop_1; eauto.
    }

    Case "2. nd_not_used_in_eqs".
    unfold nd_not_used_in_eqs; intros.
    remember (remove_old_by_newdefs_list inv nd) as rond; clear Heqrond.
    unfold new_to_old_by_newdefs_list in Hinv.
    clear Hnd Hvs; generalize dependent inv'; induction nd; [done|]; intros.
    simpl in Hy; destruct Hy as [Hya|Hyl].
    - clear IHnd; subst a; simpl in Hinv.
      rewrite Hinv; unfold id_not_used_in_eqs; simpl; splits.
      + eapply oldnew_implies_id_not_used_eq_reg; eauto.
      + eapply oldnew_implies_id_not_used_eq_heap; eauto.
      + eapply oldnew_implies_id_not_used_neq_reg; eauto.
    - simpl in Hinv.
      destruct (id_dec a y).
      + subst y;  rewrite Hinv; unfold id_not_used_in_eqs; simpl; splits.
        * eapply oldnew_implies_id_not_used_eq_reg; eauto.
        * eapply oldnew_implies_id_not_used_eq_heap; eauto.
        * eapply oldnew_implies_id_not_used_neq_reg; eauto.
      + exploit IHnd; try eapply Hyl; try reflexivity; intros Hbrd.
        unfold id_not_used_in_eqs in Hbrd; simpl in Hbrd;
          destruct Hbrd as [Hreg [Hheap Hnreg]].
        rewrite Hinv; unfold id_not_used_in_eqs; simpl; splits.
        * eapply oldnew_preserves_id_not_used_in_eqs_eq_reg; eauto.
        * eapply oldnew_preserves_id_not_used_in_eqs_eq_heap; eauto.
        * eapply oldnew_preserves_id_not_used_in_eqs_neq_reg; eauto.
  Qed.

  (* Variables and hypotheses for the main lemma. *)
  Variable
    (cfg1 cfg2: Config)
    (b1 b2 pb1 pb2: block) (lb lpb: l)
    (mem1 mem2: mem)
    (lc1 lc2 lc1' lc2': GVsMap)
    (phis1 phis2: phinodes).
  Hypothesis
    (Hlb1: lb = fst b1) (Hlb2: lb = fst b2)
    (Hlpb1: lpb = fst pb1) (Hlpb2: lpb = fst pb2)
    (Hlc1': ret lc1' = switchToNewBasicBlock (CurTargetData cfg1)
      b1 pb1 (Globals cfg1) lc1)
    (Hlc2': ret lc2' = switchToNewBasicBlock (CurTargetData cfg2)
      b2 pb2 (Globals cfg2) lc2)
    (Hphis1: phis1 = getPHINodesFromBlock b1)
    (Hphis2: phis2 = getPHINodesFromBlock b2).

  Lemma phinodes_updated_locals_prop_1:
    forall x
      (Hxmem: ~ List.In x (def_phinodes phis1)),
      lookupAL GVs lc1 x = lookupAL GVs lc1' x.
  Proof.
    intros.
    unfold switchToNewBasicBlock in Hlc1'.
    rewrite <- Hphis1 in Hlc1'.
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg1) phis1
      pb1 (Globals cfg1) lc1) as pvalues1.
    destruct pvalues1; [|done]; inversion Hlc1'; subst lc1'; clear Hlc1'.
    clear Hphis1.

    generalize dependent l0; induction phis1;
    [by intros; simpl in *; inv Heqpvalues1; simpl|].

    intros.
    simpl in Heqpvalues1.
    destruct a.
    destruct (getValueViaBlockFromValuels l1 pb1); [|done].
    destruct (getOperandValue (CurTargetData cfg1) v lc1 (Globals cfg1)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg1) p pb1
      (Globals cfg1) lc1) as iphis; destruct iphis; [|done].

    simpl in Hxmem.
    destruct (id_dec id5 x); [by subst id5; elim Hxmem; left|].
    exploit IHp.
    { by intro Hcontr; elim Hxmem; right. }
    { reflexivity. }
    intro Hindres.

    inversion Heqpvalues1; subst l0; clear Heqpvalues1; simpl.
    rewrite <- lookupAL_updateAddAL_neq; eauto.
  Qed.

  Lemma phinodes_updated_locals_prop_2:
    forall x
      (Hxmem: ~ List.In x (def_phinodes phis2)),
      lookupAL GVs lc2 x = lookupAL GVs lc2' x.
  Proof.
    intros.
    unfold switchToNewBasicBlock in Hlc2'.
    rewrite <- Hphis2 in Hlc2'.
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg2) phis2
      pb2 (Globals cfg2) lc2) as pvalues2.
    destruct pvalues2; [|done]; inversion Hlc2'; subst lc2'; clear Hlc2'.
    clear Hphis2.

    generalize dependent l0; induction phis2;
    [by intros; simpl in *; inv Heqpvalues2; simpl|].

    intros.
    simpl in Heqpvalues2.
    destruct a.
    destruct (getValueViaBlockFromValuels l1 pb2); [|done].
    destruct (getOperandValue (CurTargetData cfg2) v lc2 (Globals cfg2)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg2) p pb2
      (Globals cfg2) lc2) as iphis; destruct iphis; [|done].

    simpl in Hxmem.
    destruct (id_dec id5 x); [by subst id5; elim Hxmem; left|].
    exploit IHp.
    { by intro Hcontr; elim Hxmem; right. }
    { reflexivity. }
    intro Hindres.

    inversion Heqpvalues2; subst l0; clear Heqpvalues2; simpl.
    rewrite <- lookupAL_updateAddAL_neq; eauto.
  Qed.

  Variable
    (nd1 nd2 ndi ndu: list atom).
  Hypothesis
    (Hnd1: nd1 = def_phinodes phis1)
    (Hnd2: nd2 = def_phinodes phis2)
    (Hndi: ndi = atom_inter nd1 nd2)
    (Hndu: ndu = atom_union nd1 nd2).

  Lemma phi_remove_old_preserves_maydiff_sem:
    forall alpha md md' olc1 olc2
      (Huniq1: is_uniq_def_phinodes phis1)
      (Huniq2: is_uniq_def_phinodes phis2)
      (Hmd': md' = remove_old_md_by_newdefs_list md ndi)
      (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md),
      maydiff_sem lc1 lc2 alpha (remove_olc_by_nd olc1 ndi)
      (remove_olc_by_nd olc2 ndi) md'.
  Proof.
    intros; clear Hlc1' Hlc2'. (* not used in this lemma *)
    unfold switchToNewBasicBlock in *.
    clear Hphis1 Hphis2 Hlb1 Hlb2 b1 b2.

    (* NOTE: section variables are not generalized naturally... *)
    generalize dependent phis1; clear Hnd1.
    generalize dependent phis2; clear Hnd2.
    generalize dependent nd2; clear Hndi Hndu.
    generalize dependent md'; generalize dependent ndi;
    generalize dependent ndu.

    induction nd1; intros; [by subst ndi0 ndu0; simpl in *; subst md'|].

    clear phis1; rename phis3 into phis1.
    clear phis2; rename phis0 into phis2.
    clear nd2; rename nd0 into nd2.
    clear ndi; rename ndi0 into ndi.
    clear ndu; rename ndu0 into ndu.

    simpl in Hndi.
    destruct (in_dec id_dec a nd2).

    Case "1. a \in nd2".
    simpl in Hndu.
    rewrite Hndi in *; simpl in Hmd'; simpl.
    remember (remove_old_md_by_newdefs_list md (atom_inter l0 nd2)) as indmd.
    destruct phis1 as [|aphi lphis]; [done|].
    simpl in Hnd1; inversion Hnd1.
    simpl in Huniq1; apply andb_true_iff in Huniq1; destruct Huniq1 as [Hnain Huniql].

    hexploit IHl0.
    { apply Heqindmd. }
    { reflexivity. }
    { reflexivity. }
    { apply Hnd2. }
    { apply Huniq2. }
    { apply H1. }
    { apply Huniql. }
    intros Hind; clear IHl0.
    rewrite <-H0 in *; clear H0; rewrite <-H1 in *; clear H1; rewrite Hmd'.
    clear -Hind. (* simplified by induction hypothesis. *)

    unfold maydiff_sem in *; intros x Hx.
    rewrite IdExtSetFacts.remove_b in Hx; apply andb_false_iff in Hx.
    destruct Hx as [Hnmem|Hneq]; simpl in *.
    { exploit Hind; eauto; intro Hres; destruct x as [x [|]]; [|done].
      destruct (id_dec a x).
      + subst x.
        unfold variable_equivalent in *; simpl.
        repeat rewrite lookupAL_deleteAL_eq; eauto.
      + unfold variable_equivalent in *; simpl.
        repeat rewrite lookupAL_deleteAL_neq; eauto.
    }
    { unfold IdExtSetFacts.eqb in Hneq.
      destruct (IdExtSetFacts.eq_dec (add_otag a) x); [|done]; subst x.
      unfold variable_equivalent; simpl.
      repeat rewrite lookupAL_deleteAL_eq; eauto.
    }

    Case "2. a \notin nd2".
    destruct phis1 as [|aphi lphis]; [done|].
    simpl in Hnd1; inversion Hnd1.
    simpl in Huniq1; apply andb_true_iff in Huniq1; destruct Huniq1 as [Hnain Huniql].
    eapply IHl0.
    - apply Hmd'. - apply Hndi. - reflexivity.
    - apply Hnd2. - apply Huniq2. - apply H1. - apply Huniql.

  Qed.

  Definition phi_update_maydiff md ndi ndu :=
    List.fold_right
    (fun x acc => 
      if ((List.in_dec id_dec x ndi) && (negb (IdExtSetImpl.mem (add_ntag x) md)))
        then IdExtSetImpl.add (add_ntag x) (IdExtSetImpl.remove (add_otag x) acc)
        else IdExtSetImpl.add (add_ntag x) (IdExtSetImpl.add (add_otag x) acc)
    )
    md ndu.

  Lemma phi_maydiff_not_related_prop:
    forall x md md'
      (Hmd': md' = phi_update_maydiff md ndi ndu)
      (Hnmem: IdExtSetImpl.mem x md' = false)
      (Hnin: ~ In (fst x) ndu),
      IdExtSetImpl.mem x md = false.
  Proof.
    intros. clear -Hmd' Hnmem Hnin.
    generalize dependent md'; induction ndu; intros; [by simpl in *; subst|].
    eapply IHl0; eauto.
    - intro Hcontr; elim Hnin; right; done.
    - subst; simpl in Hnmem.
      destruct (in_dec id_dec a ndi && negb (IdExtSetImpl.mem (add_ntag a) md)).
      + rewrite IdExtSetFacts.add_b in Hnmem; apply orb_false_iff in Hnmem.
        destruct Hnmem as [_ Hnmem].
        rewrite IdExtSetFacts.remove_b in Hnmem; apply andb_false_iff in Hnmem.
        destruct Hnmem as [Hnmem|Hcontr]; [done|].
        elimtype False.
        apply negb_false_iff in Hcontr.
        unfold IdExtSetFacts.eqb in Hcontr.
        destruct (IdExtSetFacts.eq_dec (add_otag a) x); [|done].
        by subst x; simpl in Hnin; elim Hnin; left.
      + by repeat (rewrite IdExtSetFacts.add_b in Hnmem; apply orb_false_iff in Hnmem;
        destruct Hnmem as [_ Hnmem]).
  Qed.

  Lemma phi_maydiff_not_related_preserves_lookup:
    forall cfg lc vs phis nd ndu pb x
      (Hvs: ret vs = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
        (Globals cfg) lc)
      (Hndu: list_sub nd ndu)
      (Hnin: ~ In x ndu)
      (Hnd: nd = def_phinodes phis),
      lookupAL GVs lc x = lookupAL GVs (updateValuesForNewBlock vs lc) x.
  Proof.
    clear; intros.
    assert (Hnnd: In x nd -> False).
    { intro Hcontr; elim Hnin; eapply Hndu; eauto. }
    clear Hnin Hndu; subst.
    generalize dependent vs; induction phis; intros; [by inv Hvs|].
    simpl in Hvs.
    destruct a.
    destruct (getValueViaBlockFromValuels l0 pb); [|done].
    destruct (getOperandValue (CurTargetData cfg) v lc (Globals cfg)); [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
      (Globals cfg) lc) as ivs; destruct ivs; [|done].
    inv Hvs; simpl; simpl in Hnnd.
    rewrite <- lookupAL_updateAddAL_neq; eauto.
  Qed.

  Lemma phi_maydiff_update_preserves_maydiff_sem:
    forall alpha md md' olc1 olc2 vs1 vs2
      (Huniq1: is_uniq_def_phinodes phis1)
      (Huniq2: is_uniq_def_phinodes phis2)
      (Hvs1: ret vs1 = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg1)
        phis1 pb1 (Globals cfg1) lc1)
      (Hvs2: ret vs2 = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg2)
        phis2 pb2 (Globals cfg2) lc2)

      (Hmd': md' = phi_update_maydiff md ndi ndu)
      (Hsem: maydiff_sem lc1 lc2 alpha (remove_olc_by_nd olc1 ndi)
        (remove_olc_by_nd olc2 ndi) md),

      maydiff_sem lc1' lc2' alpha (snd (update_olc_by_vs olc1 lc1 vs1))
      (snd (update_olc_by_vs olc2 lc2 vs2)) md'.
  Proof.
    intros.
    unfold maydiff_sem in *; intros.
    destruct (in_dec id_dec (fst x) ndu).

    { Case "1. x is related with phinodes".
    unfold phi_update_maydiff in Hmd'.
    clear -H Hmd' Hsem Hndi i0 Hvs1 Hvs2 Hnd1 Hnd2 Huniq1 Huniq2.
    generalize dependent md'; induction ndu; intros; [by elim i0|].

    simpl in i0; destruct i0 as [Heqa|Hindin].

    - subst a; simpl in Hmd'.
      remember (fold_right
        (fun (x : id) (acc : IdExtSetImpl.t) =>
          if in_dec id_dec x ndi &&
            negb (IdExtSetImpl.mem (add_ntag x) md)
            then
              IdExtSetImpl.add (add_ntag x)
              (IdExtSetImpl.remove (add_otag x) acc)
            else
              IdExtSetImpl.add (add_ntag x)
              (IdExtSetImpl.add (add_otag x) acc)) md l0) as mdind; clear Heqmdind.
      clear IHl0.

      remember (in_dec id_dec (fst x) ndi &&
        negb (IdExtSetImpl.mem (add_ntag (fst x)) md)) as mcond; destruct mcond.

      + symmetry in Heqmcond; apply andb_true_iff in Heqmcond.
        destruct Heqmcond as [Handi Hainmd].
        rewrite Hmd' in H; clear Hmd'.
        destruct x as [x [|]];
          [|by unfold add_ntag in H; simpl in H;
            rewrite IdExtSetFacts.add_b in H; apply orb_false_iff in H;
            destruct H as [Hcontr _];
            unfold IdExtSetFacts.eqb in Hcontr;
            destruct (IdExtSetFacts.eq_dec (x, ntag_new) (x, ntag_new))].

        simpl in Hainmd; apply negb_true_iff in Hainmd.
        exploit Hsem; eauto; intro Hres.
        unfold variable_equivalent in *; simpl in *.
        remember (update_olc_by_vs olc1 lc1 vs1) as ov1; destruct ov1 as [vslc1 vsolc1].
        remember (update_olc_by_vs olc2 lc2 vs2) as ov2; destruct ov2 as [vslc2 vsolc2].
        simpl.
        exploit update_olc_by_vs_uniqueness_prop_4.
        { apply Huniq1. }
        { instantiate (1:=x).
          destruct (in_dec id_dec x ndi); [|done]; clear Handi; rewrite Hndi in i0.
          rewrite <-Hnd1.
          eapply list_sub_atom_inter_l; eauto.
        }
        { apply Hvs1. }
        { apply Heqov1. }
        intro Heq; rewrite Heq; clear Heq.
        exploit update_olc_by_vs_uniqueness_prop_4.
        { apply Huniq2. }
        { instantiate (1:=x).
          destruct (in_dec id_dec x ndi); [|done]; clear Handi; rewrite Hndi in i0.
          rewrite <-Hnd2.
          eapply list_sub_atom_inter_r; eauto.
        }
        { apply Hvs2. }
        { apply Heqov2. }
        intro Heq; rewrite Heq; clear Heq.
        done.

      + rewrite Hmd' in H; clear Hmd'.
        destruct x as [x [|]]; simpl in H; unfold add_ntag, add_otag in H.
        * rewrite IdExtSetFacts.add_b in H; apply orb_false_iff in H.
          destruct H as [_ H].
          rewrite IdExtSetFacts.add_b in H; apply orb_false_iff in H.
          destruct H as [H _].
          unfold IdExtSetFacts.eqb in H.
          destruct (IdExtSetFacts.eq_dec (x, ntag_old) (x, ntag_old)); done.
        * rewrite IdExtSetFacts.add_b in H; apply orb_false_iff in H.
          destruct H as [H _].
          unfold IdExtSetFacts.eqb in H.
          destruct (IdExtSetFacts.eq_dec (x, ntag_new) (x, ntag_new)); done.

    - simpl in Hmd'.
      remember (fold_right
        (fun (x : id) (acc : IdExtSetImpl.t) =>
          if in_dec id_dec x ndi && negb (IdExtSetImpl.mem (add_ntag x) md)
            then
              IdExtSetImpl.add (add_ntag x)
              (IdExtSetImpl.remove (add_otag x) acc)
            else
              IdExtSetImpl.add (add_ntag x)
              (IdExtSetImpl.add (add_otag x) acc)) md l0) as mdind; clear Heqmdind.
      remember (in_dec id_dec a ndi &&
        negb (IdExtSetImpl.mem (add_ntag a) md)) as mcond; destruct mcond.

      + rewrite Hmd' in H; clear Hmd'.
        rewrite IdExtSetFacts.add_b in H; apply orb_false_iff in H.
        destruct H as [_ H].
        rewrite IdExtSetFacts.remove_b in H; apply andb_false_iff in H.
        destruct H as [H|Heqax]; [by eapply IHl0|]; clear IHl0.
        symmetry in Heqmcond; apply andb_true_iff in Heqmcond.

        apply negb_false_iff in Heqax; unfold IdExtSetFacts.eqb in Heqax.
        destruct (IdExtSetFacts.eq_dec (add_otag a) x); [|done]; clear Heqax; subst x.
        destruct Heqmcond as [Handi Hainmd]; apply negb_true_iff in Hainmd.
        exploit Hsem; eauto; intro Hres.
        unfold variable_equivalent in *; simpl in *.
        remember (update_olc_by_vs olc1 lc1 vs1) as ov1; destruct ov1 as [vslc1 vsolc1].
        remember (update_olc_by_vs olc2 lc2 vs2) as ov2; destruct ov2 as [vslc2 vsolc2].
        simpl.
        exploit update_olc_by_vs_uniqueness_prop_4.
        { apply Huniq1. }
        { instantiate (1:=a).
          destruct (in_dec id_dec a ndi); [|done]; clear Handi; rewrite Hndi in i0.
          rewrite <-Hnd1.
          eapply list_sub_atom_inter_l; eauto.
        }
        { apply Hvs1. }
        { apply Heqov1. }
        intro Heq; rewrite Heq; clear Heq.
        exploit update_olc_by_vs_uniqueness_prop_4.
        { apply Huniq2. }
        { instantiate (1:=a).
          destruct (in_dec id_dec a ndi); [|done]; clear Handi; rewrite Hndi in i0.
          rewrite <-Hnd2.
          eapply list_sub_atom_inter_r; eauto.
        }
        { apply Hvs2. }
        { apply Heqov2. }
        intro Heq; rewrite Heq; clear Heq.
        done.

      + rewrite Hmd' in H.
        rewrite IdExtSetFacts.add_b in H; apply orb_false_iff in H.
        destruct H as [_ H].
        rewrite IdExtSetFacts.add_b in H; apply orb_false_iff in H.
        destruct H as [_ H].
        eapply IHl0; eauto.
    }

    Case "2. x is not related with phinodes".
    exploit phi_maydiff_not_related_prop; eauto; intro Hninmd.
    exploit Hsem; eauto; intro Hbrd.
    unfold variable_equivalent in *.
    destruct x as [x [|]]; simpl in *.

    { SCase "2.1. when x is old".
    remember (update_olc_by_vs olc1 lc1 vs1) as ov1; destruct ov1 as [olcvs1 lcvs1].
    remember (update_olc_by_vs olc2 lc2 vs2) as ov2; destruct ov2 as [olcvs2 lcvs2].
    simpl.
    exploit update_olc_by_vs_uniqueness_prop_3.
    { instantiate (1:=phis1); instantiate (1:=x).
      rewrite <-Hnd1; intro Hcontr; elim n; rewrite Hndu.
      eapply list_sub_app_l; eauto.
    }
    { apply Hvs1. }
    { apply Heqov1. }
    intro Heq; rewrite <-Heq; clear Heq.
    exploit update_olc_by_vs_uniqueness_prop_3.
    { instantiate (1:=phis2); instantiate (1:=x).
      rewrite <-Hnd2; intro Hcontr; elim n; rewrite Hndu.
      eapply list_sub_app_r; eauto.
    }
    { apply Hvs2. }
    { apply Heqov2. }
    intro Heq; rewrite <-Heq; clear Heq.
    assert (Hnini: ~ In x ndi).
    { intro Hcontr; elim n; rewrite Hndi in Hcontr; rewrite Hndu.
      unfold atom_inter, atom_union in *.
      rewrite filter_In in Hcontr; destruct Hcontr as [Hres _].
      rewrite in_app; left; done.
    }
    rewrite <- remove_olc_by_nd_others_prop in Hbrd; eauto.
    rewrite <- remove_olc_by_nd_others_prop in Hbrd; eauto.
    }

    { SCase "2.2. when x is new".
    assert (Hxeq1: lookupAL GVs lc1 x = lookupAL GVs lc1' x).
    { unfold switchToNewBasicBlock in Hlc1'.
      rewrite <-Hphis1, <-Hvs1 in Hlc1'; inversion Hlc1'; subst lc1'; clear Hlc1'.
      eapply phi_maydiff_not_related_preserves_lookup; eauto.
      rewrite Hndu; apply list_sub_app_l.
    }
    assert (Hxeq2: lookupAL GVs lc2 x = lookupAL GVs lc2' x).
    { unfold switchToNewBasicBlock in Hlc2'.
      rewrite <-Hphis2, <-Hvs2 in Hlc2'; inversion Hlc2'; subst lc2'; clear Hlc2'.
      eapply phi_maydiff_not_related_preserves_lookup; eauto.
      rewrite Hndu; apply list_sub_app_r.
    }
    rewrite <-Hxeq1, <-Hxeq2; done.
    }
  Qed.

  Lemma phi_oldnew_preserves_maydiff_sem:
    forall alpha md md' olc1 olc2 vs1 vs2
      (Huniq1: is_uniq_def_phinodes phis1)
      (Huniq2: is_uniq_def_phinodes phis2)
      (Hvs1: ret vs1 = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg1)
        phis1 pb1 (Globals cfg1) lc1)
      (Hvs2: ret vs2 = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg2)
        phis2 pb2 (Globals cfg2) lc2)
      (Hmd': md' = phi_update_maydiff (remove_old_md_by_newdefs_list md ndi) ndi ndu)
      (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md),
      maydiff_sem lc1' lc2' alpha (snd (update_olc_by_vs olc1 lc1 vs1))
      (snd (update_olc_by_vs olc2 lc2 vs2)) md'.
  Proof.
    intros.
    eapply phi_maydiff_update_preserves_maydiff_sem; eauto.
    eapply phi_remove_old_preserves_maydiff_sem; eauto.
  Qed.

  Lemma phi_oldnew_preserves_isolated_sem:
    forall cfg olc lc lc' li iso vs pb phis
      (Hlc': ret lc' = ret updateValuesForNewBlock vs lc)
      (Hicheck: false = negb (IdExtSetImpl.for_all
        (fun x => negb (List.in_dec id_dec (fst x) (def_phinodes phis))) iso))
      (Hvs: ret vs =
        getIncomingValuesForBlockFromPHINodes (CurTargetData cfg) phis pb
        (Globals cfg) lc)
      (Hiso: isolated_sem (CurTargetData cfg) olc lc li iso),
      isolated_sem (CurTargetData cfg) (snd (update_olc_by_vs olc lc vs))
      lc' li iso.
  Proof.
    intros; inversion Hlc'; clear H0 Hlc' lc'.
    unfold isolated_sem, IdExtSetImpl.For_all in *.
    intros x Hx.
    exploit Hiso; eauto; intro Hfact; clear Hiso.

    assert (~ List.In (fst x) (def_phinodes phis)) as Hnin.
    { intro Hcontr.
      symmetry in Hicheck; apply negb_false_iff in Hicheck.
      apply IdExtSetImpl.for_all_2 in Hicheck;
        [|unfold compat_bool, Proper, "==>"; intros; subst; done].
      exploit Hicheck; eauto; intro Hcontr'.
      simpl in Hcontr'; apply negb_true_iff in Hcontr'.
      destruct (in_dec id_dec (fst x) (def_phinodes phis)); done.
    }
    
    destruct Hfact as [He|[xv [Hl Hptr]]].

    - left; destruct x as [x [|]]; simpl in *.
      + erewrite <-update_olc_by_vs_uniqueness_prop_3; eauto.
        * instantiate (1:= fst (update_olc_by_vs olc lc vs)).
          destruct (update_olc_by_vs olc lc vs); done.
      + eapply id_notin_nd_preserves_lookup; eauto.

    - right; exists xv; split; [|done].
      destruct x as [x [|]]; simpl in *.
      + erewrite <-update_olc_by_vs_uniqueness_prop_3; eauto.
        * instantiate (1:= fst (update_olc_by_vs olc lc vs)).
          destruct (update_olc_by_vs olc lc vs); done.
      + eapply id_notin_nd_preserves_lookup; eauto.
  Qed.

  Lemma phi_oldnew_preserves_hint_sem_each:
    forall alpha md inv1 inv2 iso1 iso2 md' inv1' inv2' olc1 olc2 gmax vs1 vs2 li1 li2
      (Huniq1: is_uniq_def_phinodes phis1)
      (Huniq2: is_uniq_def_phinodes phis2)
      (Hicheck1: false = negb (IdExtSetImpl.for_all
        (fun x => negb (List.in_dec id_dec (fst x) (def_phinodes phis1))) iso1))
      (Hicheck2: false = negb (IdExtSetImpl.for_all
        (fun x => negb (List.in_dec id_dec (fst x) (def_phinodes phis2))) iso2))
      (Hvs1: ret vs1 = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg1)
        phis1 pb1 (Globals cfg1) lc1)
      (Hvs2: ret vs2 = getIncomingValuesForBlockFromPHINodes (CurTargetData cfg2)
        phis2 pb2 (Globals cfg2) lc2)
      (Hmd': md' = phi_update_maydiff (remove_old_md_by_newdefs_list md ndi) ndi ndu)
      (Hinv1': inv1' = new_to_old_by_newdefs_list
        (remove_old_by_newdefs_list inv1 nd1) nd1)
      (Hinv2': inv2' = new_to_old_by_newdefs_list
        (remove_old_by_newdefs_list inv2 nd2) nd2)
      (Hmd: maydiff_sem lc1 lc2 alpha olc1 olc2 md)
      (Hinv: invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2
        (mkInvariant inv1 inv2 iso1 iso2)),
      maydiff_sem lc1' lc2' alpha
      (snd (update_olc_by_vs olc1 lc1 vs1)) (snd (update_olc_by_vs olc2 lc2 vs2)) md' /\
      invariant_sem cfg1 cfg2 lc1' lc2' mem1 mem2
      (snd (update_olc_by_vs olc1 lc1 vs1)) (snd (update_olc_by_vs olc2 lc2 vs2)) gmax
      li1 li2 (mkInvariant inv1' inv2' iso1 iso2) /\
      (oldnew_prop nd1 lc1 (snd (update_olc_by_vs olc1 lc1 vs1)) inv1') /\
      (oldnew_prop nd2 lc2 (snd (update_olc_by_vs olc2 lc2 vs2)) inv2').
  Proof.
    intros.
    unfold switchToNewBasicBlock in *.
    rewrite <-Hphis1, <-Hvs1 in Hlc1'; rewrite <-Hphis2, <-Hvs2 in Hlc2'.
    splits.
    - eapply phi_oldnew_preserves_maydiff_sem; eauto.
    - unfold invariant_sem in *; simpl in *;
      destruct Hinv as [Hlinv [Hrinv [Hliso Hriso]]]; splits.
      + eapply phi_oldnew_preserves_invariant_sem.
        * apply Huniq1. * apply Hvs1. * by inv Hlc1'. * apply Hphis1.
        * apply Hnd1. * apply Hinv1'. * apply Hlinv.
      + eapply phi_oldnew_preserves_invariant_sem.
        * apply Huniq2. * apply Hvs2. * by inv Hlc2'. * apply Hphis2.
        * apply Hnd2. * apply Hinv2'. * apply Hrinv.
      + eapply phi_oldnew_preserves_isolated_sem; eauto.
      + eapply phi_oldnew_preserves_isolated_sem; eauto.
    - eapply oldnew_implies_oldnew_prop; eauto.
    - eapply oldnew_implies_oldnew_prop; eauto.
  Qed.

  Lemma phi_addphis_preserves_hint_sem_each:
    forall inv1 inv2 inv1' inv2' olc1 olc2 gmax iso1 iso2 li1 li2
      (Hinv1': inv1' = add_ntag_phis_to_eqs nd1 lpb inv1 phis1)
      (Hinv2': inv2' = add_ntag_phis_to_eqs nd2 lpb inv2 phis2)

      (Hsem: invariant_sem cfg1 cfg2 lc1' lc2' mem1 mem2 olc1 olc2 gmax li1 li2
        (mkInvariant inv1 inv2 iso1 iso2))
      (Honp1: oldnew_prop nd1 lc1 olc1 inv1)
      (Honp2: oldnew_prop nd2 lc2 olc2 inv2),
      invariant_sem cfg1 cfg2 lc1' lc2' mem1 mem2 olc1 olc2 gmax li1 li2
      (mkInvariant inv1' inv2' iso1 iso2).
  Proof.
    intros; destruct Hsem as [Hinv1 [Hinv2 [Hiso1 Hiso2]]]; rr; splits; try done; simpl.
    - eapply phi_addphis_preserves_hint_sem_each_aux; try eapply Hlc1'; eauto.
    - eapply phi_addphis_preserves_hint_sem_each_aux; try eapply Hlc2'; eauto.
  Qed.

  (* All step lemma gathered. *)
  Lemma invariant_proceed_preserves_hint_sem_insn_phi:
    forall hint nhint alpha gmax li1 pi1 li2 pi2
      pns1 pns2 pecs1 pecs2 ec1 ec2 ec1' ec2' n1 n2
      (Hlc1: lc1 = (Locals ec1)) (Hlc2: lc2 = (Locals ec2))
      (Heqlc1': lc1' = (Locals ec1')) (Heqlc2': lc2' = (Locals ec2'))
      (Hals1: Allocas ec1 = Allocas ec1') (Hals2: Allocas ec2 = Allocas ec2')
      (Hprc: ret nhint = invariant_proceed_phis hint phis1 phis2 lpb)
      (Hsem: hint_sem_insn hint pecs1 pecs2 pns1 pns2 pi1 pi2 li1 li2
        alpha gmax cfg1 (ec1::pecs1) mem1 (n1::pns1)
        cfg2 (ec2::pecs2) mem2 (n2::pns2)),
      hint_sem_insn nhint pecs1 pecs2 pns1 pns2 pi1 pi2 li1 li2
      alpha gmax cfg1 (ec1'::pecs1) mem1 (n1::pns1)
      cfg2 (ec2'::pecs2) mem2 (n2::pns2).
  Proof.
    intros.
    destruct hint as [md [inv1 inv2 iso1 iso2] ir],
      nhint as [nmd [ninv1 ninv2 niso1 niso2] nir].
    exploit hint_sem_insn_implies_hint_sem_each; eauto; intro Hbegin; clear Hsem.
    eapply hint_sem_each_implies_hint_sem_insn; eauto.
    rewrite <-Hlc1, <-Hlc2, <-Heqlc1', <-Heqlc2' in *; clear Hlc1 Hlc2 Heqlc1' Heqlc2'.
    rewrite <-Hals1, <-Hals2 in *; clear Hals1 Hals2.
    unfold invariant_proceed_phis in Hprc.

    (* Gathering information from invariant_proceed_phis *)
    unfold iso_original, iso_optimized,  hint_invariant in Hprc.
    remember (negb
      (IdExtSetImpl.for_all
        (fun x : id_ext =>
          negb (in_dec id_dec (fst x) (def_phinodes phis1))) iso1)) as icheck1.
    destruct icheck1; [done|].
    remember (negb
      (IdExtSetImpl.for_all
        (fun x : id_ext =>
          negb (in_dec id_dec (fst x) (def_phinodes phis2))) iso2)) as icheck2.
    destruct icheck2; [done|].
    remember (negb (is_uniq_def_phinodes phis1 && is_uniq_def_phinodes phis2))
    as ucheck.
    destruct ucheck; [done|].
    symmetry in Hequcheck; apply negb_false_iff in Hequcheck.
    apply andb_true_iff in Hequcheck; destruct Hequcheck as [Huniq1 Huniq2].
    destruct Hbegin as [Hmi Hiav]; split; [|done]; clear Hiav.

    (* B. remove_old for md & inv / new_to_old for inv / maydiff_update *)
    unfold switchToNewBasicBlock in *.
    rewrite <-Hphis1 in Hlc1'; rewrite <-Hphis2 in Hlc2'.
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg1) phis1
      pb1 (Globals cfg1) lc1) as vs1; destruct vs1; [|done].
    remember (getIncomingValuesForBlockFromPHINodes (CurTargetData cfg2) phis2
      pb2 (Globals cfg2) lc2) as vs2; destruct vs2; [|done].
    destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
    exploit phi_oldnew_preserves_hint_sem_each; eauto.
    intros [Hmd' [Hinv' [Hop1 Hop2]]]; clear Hmd Hinv.

    (* C. addphis *)
    exploit phi_addphis_preserves_hint_sem_each; eauto; intro Hinv''; clear Hinv'.

    (* Done! *)
    inv Hprc.
    exists (snd (update_olc_by_vs olc1 lc1 l0)).
    exists (snd (update_olc_by_vs olc2 lc2 l1)).
    split; done.
  Qed.

End HintSemEach.
