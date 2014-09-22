Require Import vgtac.

Require Import vellvm.
Require Import hint_sem.
Require Import validator_aux.
Require Import vars_aux.
Require Import syntax_ext.

Require Import FSets.
Require Import FSets.FSetInterface.

Import Opsem.

Require Import hint_sem_aux.

Notation GVs := DGVs.(GVsT).

Definition updateAddAL_opt A m k (v_opt:monad A) :=
  match v_opt with
    | ret v => updateAddAL _ m k v
    | merror => deleteAL _ m k
  end.

Lemma lookupAL_updateAddAL_opt_neq X m x y (v_opt:monad X) (Hxy: x <> y) :
  lookupAL _ (updateAddAL_opt _ m y v_opt) x = lookupAL _ m x.
Proof.
  destruct v_opt; simpl in *.
  - rewrite <- lookupAL_updateAddAL_neq; eauto.
  - rewrite lookupAL_deleteAL_neq; eauto.
Qed.

Lemma lookupAL_updateAddAL_opt_eq X m x (v_opt:monad X) :
  lookupAL _ (updateAddAL_opt _ m x v_opt) x = v_opt.
Proof.
  destruct v_opt; simpl in *.
  - rewrite lookupAL_updateAddAL_eq; eauto.
  - rewrite lookupAL_deleteAL_eq; eauto.
Qed.

Lemma eqAL_updateAddAL_opt_deleteAL X m x :
  eqAL X (updateAddAL_opt _ (deleteAL _ m x) x (lookupAL _ m x)) m.
Proof.
  intro y. destruct (id_dec y x); [subst|].
  - by rewrite lookupAL_updateAddAL_opt_eq.
  - rewrite lookupAL_updateAddAL_opt_neq; [|done].
  rewrite lookupAL_deleteAL_neq; [done|].
  by intro; apply n.
Qed.

Lemma update_preserves_maydiff_sem_left':
  forall lc1 lc2 olc1 olc2 alpha' md i
    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md),
    maydiff_sem lc1 lc2 alpha'
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
    [by subst; unfold vars_aux.add_otag, IdExtSetFacts.eqb in Hno;
      destruct (IdExtSetFacts.eq_dec (x, ntag_old) (x, ntag_old))|].
    destruct (lookupAL GVs lc1 i0);
      [by rewrite <- lookupAL_updateAddAL_neq; eauto|
        by rewrite lookupAL_deleteAL_neq; eauto].
  - destruct (id_dec i0 x);
    [by subst; unfold vars_aux.add_ntag, IdExtSetFacts.eqb in Hnn;
      destruct (IdExtSetFacts.eq_dec (x, ntag_new) (x, ntag_new))|].
    auto.
Qed.

Lemma update_preserves_maydiff_sem_right':
  forall lc1 lc2 olc1 olc2 alpha' md i
    (Hmd: maydiff_sem lc1 lc2 alpha' olc1 olc2 md),
    maydiff_sem lc1 lc2 alpha' olc1
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
    [by subst; unfold vars_aux.add_otag, IdExtSetFacts.eqb in Hno;
      destruct (IdExtSetFacts.eq_dec (x, ntag_old) (x, ntag_old))|].
    destruct (lookupAL GVs lc2 i0);
      [by rewrite <- lookupAL_updateAddAL_neq; eauto|
        by rewrite lookupAL_deleteAL_neq; eauto].
  - destruct (id_dec i0 x);
    [by subst; unfold vars_aux.add_ntag, IdExtSetFacts.eqb in Hnn;
      destruct (IdExtSetFacts.eq_dec (x, ntag_new) (x, ntag_new))|].
    auto.
Qed.

Lemma oldnew_preserves_lookup':
  forall i0 olc lc lc' vgvs ie gvs
    (Hec': lc' = (updateAddAL_opt GVs lc i0 gvs))
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
  - destruct (id_dec i0 i); subst; simpl.
    + by rewrite Hov, lookupAL_updateAddAL_eq.
    + by rewrite lookupAL_updateAddAL_opt_neq; eauto.
Qed.

Lemma oldnew_preserves_getOperandValueExt':
  forall i0 cfg v olc lc lc' vgvs gvs
    (Hec': lc' = (updateAddAL_opt GVs lc i0 gvs))
    (Hnot: IdExtSetImpl.mem (add_otag i0) (used_locals_in_value v) = false)
    (Hov: getOperandValueExt (CurTargetData cfg) v olc lc (Globals cfg)
      = ret vgvs),
    getOperandValueExt (CurTargetData cfg) (new_to_old_local_in_value i0 v)
    match lookupAL GVs lc i0 with
      | ret xv => updateAddAL GVs olc i0 xv
      | merror => deleteAL GVs olc i0
    end lc' (Globals cfg) = ret vgvs.
Proof.
  intros; destruct v as [ie|cst]; [|done].
  simpl. eapply oldnew_preserves_lookup'; eauto.
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
      * rewrite lookupAL_updateAddAL_opt_neq; eauto.

  - destruct r; try (inv Hrhs; fail); simpl in Hnot; mem_destruct_tac.

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

(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
