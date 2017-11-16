Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.
Require Import opsem.

Require Import sflib.
Require Import paco.
Import Opsem.

Require Import TODO.
Require Import TODOProof.
Require Import Decs.
Require Import Exprs.
Require Import Validator.
Require Import GenericValues.
Require Import Inject.
Require InvMem.
Require InvState.
Require Import Hints.
Require Import memory_props.
Import Memory.
Require Import opsem_wf.
Require Import genericvalues_inject.
Require Import memory_sim.
Require Import MemAux.
Require Import SoundBase.

Set Implicit Arguments.



Lemma list_inb_false_app_inv
      X (xs0 xs1: list X) X_dec x
      (INB: list_inb X_dec (xs0 ++ xs1) x = false)
  :
    <<INB0: list_inb X_dec xs0 x = false>> /\
            <<INB1: list_inb X_dec xs1 x = false>>
.
Proof.
  unfold NW.
  unfold list_inb, is_some in *.
  des_ifs_safe.
  rewrite find_app in Heq. des_ifs.
Qed.

Lemma list_inb_false_app
      X (xs0 xs1: list X) X_dec x
      (INB0: list_inb X_dec xs0 x = false)
      (INB1: list_inb X_dec xs1 x = false)
  :
    <<INB: list_inb X_dec (xs0 ++ xs1) x = false>>
.
Proof.
  unfold NW.
  unfold list_inb, is_some in *.
  des_ifs_safe.
  rewrite find_app in Heq. des_ifs.
Qed.

Lemma list_inb_false_sub
      X (xs0 xs1: list X) X_dec x
      (INB: list_inb X_dec xs1 x = false)
      (SUB: sublist xs0 xs1)
  :
    <<INB: list_inb X_dec xs0 x = false>>
.
Proof.
  unfold NW.
  unfold list_inb, is_some in *.
  des_ifs_safe.

  apply find_some in Heq. des.
  destruct (X_dec _ _); ss. clarify.

  eapply find_none in Heq0; cycle 1.
  { eapply sublist_In; eauto. }

  destruct (X_dec _ _); ss.
Qed.

Lemma list_inb_single
      x0 idt0 dec
      (INB: list_inb IdT.eq_dec [x0] idt0 = dec)
  :
    <<DEC: proj_sumbool (IdTSetFacts.eq_dec idt0 x0) = dec>>
.
Proof.
  unfold list_inb, is_some in *. ss.
  red. unfold proj_sumbool in *; des_ifs; solve_leibniz; ss.
  contradict n.
  finish_by_refl.
Qed.

Lemma list_inb_filter_map_cons
      X (v: X) (vs: list X) (f: X -> option IdT.t)
      idt0
      (INB0: list_inb IdT.eq_dec (f v) idt0 = false)
      (INB1: list_inb IdT.eq_dec
                      (filter_map f vs) idt0 = false)
  :
    <<INB: list_inb IdT.eq_dec
                    (filter_map f (v :: vs)) idt0 = false>>
.
Proof.
  ss.
  compute in INB0.
  compute in INB1.
  compute.
  des_ifs.
Qed.

Corollary list_inb_filter_map_cons_one
      X (v w: X) (f: X -> option IdT.t) idt0
      (INB0: list_inb IdT.eq_dec (f v) idt0 = false)
      (INB1: list_inb IdT.eq_dec (f w) idt0 = false)
  :
    <<INB: list_inb IdT.eq_dec (filter_map f [v; w]) idt0 = false>>
.
Proof.
  eapply list_inb_filter_map_cons; eauto.
Qed.


Section CLEAR_IDTS.

  Lemma clear_idt_spec_id
        i0 idt0
        (CLEAR: proj_sumbool (IdT.eq_dec i0 idt0) = false)
        st invst0
  :
    <<EQ: InvState.Unary.sem_idT st invst0 i0 =
          InvState.Unary.sem_idT st (InvState.Unary.clear_idt idt0 invst0) i0>>
  .
  Proof.
    red.
    unfold InvState.Unary.clear_idt. ss. des_ifs_safe.
    destruct t; ss.
    + des_sumbool.
      destruct i0; ss.
      destruct t; ss.
      unfold InvState.Unary.sem_idT in *. ss.
      rewrite lookup_AL_filter_spec. des_ifs.
      des_bool. des_sumbool. clarify.
    + des_sumbool.
      destruct i0; ss.
      destruct t; ss.
      unfold InvState.Unary.sem_idT in *. ss.
      rewrite lookup_AL_filter_spec. des_ifs.
      des_bool. des_sumbool. clarify.
  Qed.

  Lemma clear_idt_spec_value
        v0 idt0
        (CLEAR: list_inb IdT.eq_dec (ValueT.get_idTs v0) idt0 = false)
        conf st invst0
    :
      <<EQ: InvState.Unary.sem_valueT conf st invst0 v0 =
            InvState.Unary.sem_valueT conf st (InvState.Unary.clear_idt idt0 invst0) v0>>
  .
  Proof.
    red. unfold InvState.Unary.sem_valueT. des_ifs.
    erewrite clear_idt_spec_id; eauto.
    apply list_inb_single in CLEAR. des. des_sumbool.
    unfold proj_sumbool. des_ifs.
    contradict CLEAR. finish_by_refl.
  Qed.

  Lemma clear_idt_spec_list_value
        vs0 idt0
        (CLEAR: list_inb IdT.eq_dec (filter_map ValueT.get_idTs (List.map snd vs0)) idt0 = false)
        conf st invst0
    :
      <<EQ: InvState.Unary.sem_list_valueT conf st invst0 vs0 =
            InvState.Unary.sem_list_valueT conf st (InvState.Unary.clear_idt idt0 invst0) vs0>>
  .
  Proof.
    red. (* unfold InvState.Unary.sem_valueT. des_ifs. *)
    (* unfold InvState.Unary.clear_idt. ss. des_ifs_safe. *)
    ginduction vs0; ii; ss; des_ifs_safe; clarify.
    destruct t.
    + erewrite <- clear_idt_spec_value; cycle 1.
      { des_ifs. ss. clarify. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      exploit IHvs0; try eassumption.
      { instantiate (1:= idt0).
        des_ifs. ss. clarify. eapply list_inb_false_sub; eauto. repeat econs; eauto.
        eapply sublist_refl; eauto. }
      intro IH. erewrite <- IH.
      des_ifs.
    + erewrite <- clear_idt_spec_value; cycle 1.
      { des_ifs. }
      exploit IHvs0; try eassumption.
      intro IH. erewrite <- IH.
      des_ifs.
  Qed.

  Lemma clear_idt_spec_expr
        x idt0
        (CLEAR: list_inb IdT.eq_dec (Expr.get_idTs x) idt0 = false)
        conf st invst0
    :
      <<EQ: InvState.Unary.sem_expr conf st invst0 x =
            InvState.Unary.sem_expr conf st (InvState.Unary.clear_idt idt0 invst0) x>>
  .
  Proof.
    red.
    unfold Expr.get_idTs in *.
    destruct x; ss.
    - repeat erewrite <- clear_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- clear_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- clear_idt_spec_value; ss.
    - repeat erewrite <- clear_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- clear_idt_spec_value; ss.
      repeat erewrite <- clear_idt_spec_list_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto.
        eapply sublist_refl; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- clear_idt_spec_value; ss.
    - repeat erewrite <- clear_idt_spec_value; ss.
    - repeat erewrite <- clear_idt_spec_value; ss.
    - repeat erewrite <- clear_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- clear_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- clear_idt_spec_value; ss.
      { des_ifs; ss; eapply list_inb_false_sub; eauto; repeat econs; eauto. }
      { des_ifs; ss; eapply list_inb_false_sub; eauto; repeat econs; eauto. }
      { des_ifs; ss; eapply list_inb_false_sub; eauto; repeat econs; eauto. }
    - repeat erewrite <- clear_idt_spec_value; ss.
    - repeat erewrite <- clear_idt_spec_value; ss.
  Qed.

  Lemma clear_idt_spec_expr_set
        ep eps idt0
        (CLEAR: ExprPairSet.In ep (ExprPairSet.clear_idt idt0 eps))
        conf st invst0
    :
      <<EQ: InvState.Unary.sem_expr conf st invst0 ep.(fst) =
            InvState.Unary.sem_expr conf st (InvState.Unary.clear_idt idt0 invst0) ep.(fst)>> /\
            <<EQ: InvState.Unary.sem_expr conf st invst0 ep.(snd) =
                  InvState.Unary.sem_expr conf st (InvState.Unary.clear_idt idt0 invst0) ep.(snd)>>
  .
  Proof.
    unfold NW. destruct ep; ss.
    unfold ExprPairSet.clear_idt in *.
    apply ExprPairSetFacts.filter_iff in CLEAR; [| solve_compat_bool ].
    repeat (des; des_bool).
    apply list_inb_false_app_inv in CLEAR0. des. ss.
    erewrite <- clear_idt_spec_expr; eauto.
    erewrite <- clear_idt_spec_expr; eauto.
  Qed.

  Lemma clear_idt_ghost_spec_unary
        conf st invst0 invmem0 gmax pubs inv0
        (SEM: InvState.Unary.sem conf st invst0 invmem0 gmax pubs inv0)
        i0
    :
      <<SEM: InvState.Unary.sem conf st (InvState.Unary.clear_idt (Tag.ghost, i0) invst0)
                                invmem0 gmax pubs (Invariant.clear_idt_unary (Tag.ghost, i0) inv0)>>
  .
  Proof.
    Local Opaque InvState.Unary.clear_idt.
    econs; eauto; try apply SEM; ss.
    + inv SEM.
      (* clear LESSDEF NOALIAS UNIQUE PRIVATE ALLOCAS_PARENT ALLOCAS_VALID WF_LOCAL WF_PREVIOUS WF_GHOST. *)
      (* clear UNIQUE_PARENT_LOCAL WF_FDEF WF_EC. *)
      clear NOALIAS UNIQUE PRIVATE ALLOCAS_PARENT ALLOCAS_VALID WF_LOCAL WF_PREVIOUS WF_GHOST.
      clear UNIQUE_PARENT_LOCAL WF_FDEF WF_EC.
      ii.
      exploit clear_idt_spec_expr_set; eauto. i; des.
      exploit LESSDEF; eauto.
      { instantiate (1:= x).
        clear - H. unfold ExprPairSet.clear_idt in *.
        apply ExprPairSetFacts.filter_iff in H; [| solve_compat_bool ]. des; ss.
      }
      { instantiate (1:= val1). rewrite EQ. eauto. }
      i; des.
      esplits; eauto.
      rewrite <- EQ0. ss.
    + inv SEM.
      clear LESSDEF UNIQUE PRIVATE ALLOCAS_PARENT ALLOCAS_VALID WF_LOCAL WF_PREVIOUS WF_GHOST.
      clear UNIQUE_PARENT_LOCAL WF_FDEF WF_EC.
      unfold Invariant.clear_idt_alias in *.
      econs; eauto.
      * inv NOALIAS. clear NOALIAS0.
        i. ss.
        apply ValueTPairSetFacts.mem_iff in MEM.
        unfold ValueTPairSet.clear_idt in *.
        apply ValueTPairSetFacts.filter_iff in MEM; [| solve_compat_bool ].
        des; des_bool; ss.
        unfold ValueTPair.get_idTs in *. ss.
        apply list_inb_false_app_inv in MEM0. des.
        erewrite <- clear_idt_spec_value in VAL1; ss.
        erewrite <- clear_idt_spec_value in VAL2; ss.
        eapply DIFFBLOCK; eauto.
        apply ValueTPairSetFacts.mem_iff; eauto.
      * inv NOALIAS. clear DIFFBLOCK.
        i. ss.
        apply PtrPairSetFacts.mem_iff in MEM.
        unfold PtrPairSet.clear_idt in *.
        apply PtrPairSetFacts.filter_iff in MEM; [| solve_compat_bool ].
        des; des_bool; ss.
        unfold PtrPair.get_idTs in *. ss.
        apply list_inb_false_app_inv in MEM0. des.
        unfold Ptr.get_idTs in *. des_ifs. ss.
        erewrite <- clear_idt_spec_value in VAL1; ss.
        erewrite <- clear_idt_spec_value in VAL2; ss.
        eapply NOALIAS0; eauto.
        { apply PtrPairSetFacts.mem_iff; eauto. }
        { ss. }
        { ss. }
    + inv SEM.
      clear LESSDEF NOALIAS UNIQUE ALLOCAS_PARENT ALLOCAS_VALID WF_LOCAL WF_PREVIOUS WF_GHOST.
      clear UNIQUE_PARENT_LOCAL WF_FDEF WF_EC.
      unfold IdTSet.clear_idt in *.

      ii.
      unfold IdTSet.clear_idt in *.
      apply IdTSetFacts.filter_iff in H; [| solve_compat_bool ].
      des; des_bool; ss.
      eapply PRIVATE; eauto.
      erewrite clear_idt_spec_id; try eassumption.
      unfold proj_sumbool in *. des_ifs.
    + inv SEM.
      clear LESSDEF NOALIAS UNIQUE PRIVATE ALLOCAS_PARENT ALLOCAS_VALID WF_LOCAL WF_PREVIOUS.
      clear UNIQUE_PARENT_LOCAL WF_FDEF WF_EC.
      ii.
      Local Transparent InvState.Unary.clear_idt.
      unfold InvState.Unary.clear_idt in *. ss.
      Local Opaque InvState.Unary.clear_idt.
      eapply WF_GHOST; eauto.
      erewrite lookup_AL_filter_some; eauto.
  Qed.
  Local Transparent InvState.Unary.clear_idt.

  Lemma clear_idt_ghost_spec
        conf_src conf_tgt st_src st_tgt invst0 invmem0 inv0
        (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem0 inv0)
    :
      forall idt0 (GHOST: idt0.(fst) = Tag.ghost),
        <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt (InvState.Rel.clear_idt idt0 invst0)
                                  invmem0 (Invariant.clear_idt idt0 inv0)>>
  .
  Proof.
    i. red.
    destruct idt0; ss. clarify.
    unfold Invariant.clear_idt.
    (* unfold InvState.Rel.clear_idt. *)
    unfold Invariant.clear_idt_unary.
    Local Opaque InvState.Unary.clear_idt.
    econs; eauto; ss; try apply STATE.
    - eapply clear_idt_ghost_spec_unary; eauto.
      apply STATE.
    - eapply clear_idt_ghost_spec_unary; eauto.
      apply STATE.
    - inv STATE.
      clear SRC TGT TGT_NOUNIQ ALLOCAS.
      ii.
      unfold InvState.Rel.clear_idt. ss.
      destruct (IdT.eq_dec id0 (Tag.ghost, t0)).
      + clarify. exfalso.
        clear - VAL_SRC.
        Local Transparent InvState.Unary.clear_idt.
        unfold InvState.Unary.sem_idT in *. ss.
        Local Opaque InvState.Unary.clear_idt.
        rewrite lookup_AL_filter_spec in VAL_SRC. des_ifs. des_bool. des_sumbool. ss.
      + erewrite <- clear_idt_spec_id; ss; cycle 1.
        { unfold proj_sumbool. des_ifs. }
        eapply MAYDIFF; try eassumption.
        * destruct (IdTSet.mem id0 (Invariant.maydiff inv0)) eqn:T; ss.
          apply IdTSetFacts.mem_iff in T.
          apply IdTSetFacts.not_mem_iff in NOTIN.
          exfalso.
          apply NOTIN.
          unfold IdTSet.clear_idt.
          apply IdTSetFacts.filter_iff; [ solve_compat_bool | ].
          split; ss. unfold negb. des_ifs. des_sumbool. clarify.
        * erewrite clear_idt_spec_id; try eassumption.
          unfold proj_sumbool. des_ifs.
  Qed.
  Local Transparent InvState.Unary.clear_idt.

End CLEAR_IDTS.




Section CLEAR_IDTS_INV.

  Lemma clear_idt_inv_spec_id
        i0 idt0 st invst0
        gv
        (SOME: InvState.Unary.sem_idT st (InvState.Unary.clear_idt idt0 invst0) i0
               = Some gv)
        (NOTPHYSICAL: idt0.(fst) <> Tag.physical)
    :
      <<CLEAR: proj_sumbool (IdT.eq_dec i0 idt0) = false>>
  .
  Proof.
    red.
    unfold InvState.Unary.clear_idt in *. des_ifs_safe. ss.
    unfold proj_sumbool. des_ifs_safe.
    destruct t; ss.
    - unfold InvState.Unary.sem_idT, InvState.Unary.sem_tag in *. ss.
      rewrite lookup_AL_filter_spec in SOME. unfold negb, proj_sumbool in *. des_ifs.
    - unfold InvState.Unary.sem_idT, InvState.Unary.sem_tag in *. ss.
      rewrite lookup_AL_filter_spec in SOME. unfold negb, proj_sumbool in *. des_ifs.
  Qed.

  Lemma clear_idt_inv_spec_value
        v0 idt0 conf st invst0
        gv
        (SOME: InvState.Unary.sem_valueT conf st (InvState.Unary.clear_idt idt0 invst0) v0
               = Some gv)
        (NOTPHYSICAL: idt0.(fst) <> Tag.physical)
    :
      <<CLEAR: list_inb IdT.eq_dec (ValueT.get_idTs v0) idt0 = false>>
  .
  Proof.
    destruct v0; ss.
    compute. des_ifs.
    exploit clear_idt_inv_spec_id; try eassumption.
    i; des. des_sumbool. ss.
  Qed.

  Lemma clear_idt_inv_spec_list_value
        vs0 idt0 conf st invst0
        gv
        (SOME: InvState.Unary.sem_list_valueT conf st (InvState.Unary.clear_idt idt0 invst0) vs0
               = Some gv)
        (NOTPHYSICAL: idt0.(fst) <> Tag.physical)
    :
      <<CLEAR: list_inb IdT.eq_dec (filter_map ValueT.get_idTs (List.map snd vs0))
                        idt0 = false>>
  .
  Proof.
    Local Opaque InvState.Unary.clear_idt.
    destruct idt0; ss.
    ginduction vs0; ii; ss.
    des_ifs_safe. ss.
    abstr (filter_map ValueT.get_idTs (List.map snd vs0)) tt.
    exploit clear_idt_inv_spec_value; try eassumption. i.
    destruct t1; ss; cycle 1.
    { eapply IHvs0; eauto. }
    replace (x :: tt) with ([x] ++ tt) by ss.
    apply list_inb_false_app; cycle 1.
    { eapply IHvs0; eauto. }
    compute. des_ifs.
  Qed.

  Lemma clear_idt_inv_spec_expr
        x idt0 conf st invst0
        gv
        (SOME: InvState.Unary.sem_expr conf st (InvState.Unary.clear_idt idt0 invst0) x
               = Some gv)
        (NOTPHYSICAL: idt0.(fst) <> Tag.physical)
    :
      <<CLEAR: list_inb IdT.eq_dec (Expr.get_idTs x) idt0 = false>>
  .
  Proof.
    Local Opaque filter_map.
    red.
    unfold Expr.get_idTs in *.
    destruct x; ss.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss. intro IH0.
      exploit clear_idt_inv_spec_value; try exact Heq0; ss. intro IH1.
      eapply list_inb_filter_map_cons; eauto.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss. intro IH0.
      exploit clear_idt_inv_spec_value; try exact Heq0; ss. intro IH1.
      eapply list_inb_filter_map_cons; eauto.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss. intro IH0.
      exploit clear_idt_inv_spec_value; try exact Heq0; ss. intro IH1.
      eapply list_inb_filter_map_cons; eauto.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss. intro IH0.
      exploit clear_idt_inv_spec_list_value; try exact Heq0; ss. intro IH1.
      eapply list_inb_filter_map_cons; eauto.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss. intro IH0.
      exploit clear_idt_inv_spec_value; try exact Heq0; ss. intro IH1.
      eapply list_inb_filter_map_cons; eauto.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss. intro IH0.
      exploit clear_idt_inv_spec_value; try exact Heq0; ss. intro IH1.
      eapply list_inb_filter_map_cons; eauto.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss. intro IH0.
      exploit clear_idt_inv_spec_value; try exact Heq0; ss. intro IH1.
      exploit clear_idt_inv_spec_value; try exact Heq1; ss. intro IH2.
      eapply list_inb_filter_map_cons; eauto.
      eapply list_inb_filter_map_cons; eauto.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact SOME; ss.
    - des_ifs_safe.
      exploit clear_idt_inv_spec_value; try exact Heq; ss.
  Qed.


End CLEAR_IDTS_INV.
  







Section CONS_IDT.

  Definition cons_idt_unary (idt0: IdT.t) (gv: GenericValue)
             (inv0: InvState.Unary.t): InvState.Unary.t :=
    match idt0.(fst) with
    | Tag.physical => inv0
    | Tag.previous => (InvState.Unary.update_previous
                         (fun idgs => (idt0.(snd), gv) :: idgs) inv0)
    | Tag.ghost => (InvState.Unary.update_ghost
                      (fun idgs => (idt0.(snd), gv) :: idgs) inv0)
    end
  .

  Definition cons_idt (idt0: IdT.t) (gv_src gv_tgt: GenericValue)
             (inv0: InvState.Rel.t): InvState.Rel.t :=
    InvState.Rel.mk (cons_idt_unary idt0 gv_src inv0.(InvState.Rel.src))
                    (cons_idt_unary idt0 gv_tgt inv0.(InvState.Rel.tgt))
  .

  Lemma cons_idt_spec_id
        i0 idt0
        (CLEAR: proj_sumbool (IdT.eq_dec i0 idt0) = false)
        st invst0
        gv0
  :
    <<EQ: InvState.Unary.sem_idT st invst0 i0 =
          InvState.Unary.sem_idT st (cons_idt_unary idt0 gv0 invst0) i0>>
  .
  Proof.
    red.
    destruct idt0; ss.
    unfold cons_idt_unary. ss.
    unfold InvState.Unary.sem_idT.
    unfold InvState.Unary.sem_tag.
    destruct i0; ss.
    des_sumbool.
    destruct t, t1; ss; des_ifs.
  Qed.

  (* Lemma clear_idt_spec_inv_id *)
  (*       i0 idt0 st_src invst0 *)
  (*       gv *)
  (*       (SOME: InvState.Unary.sem_idT st_src (InvState.Unary.clear_idt idt0 invst0) i0 *)
  (*              = Some gv) *)
  (*       (NOTPHYSICAL: idt0.(fst) <> Tag.physical) *)
  (*   : *)
  (*     (* <<NOTIN: idt0 <> i0>> *) *)
  (*     <<CLEAR: proj_sumbool (IdT.eq_dec i0 idt0) = false>> *)
  (* . *)

  Lemma cons_idt_spec_value
        v0 idt0
        (CLEAR: list_inb IdT.eq_dec (ValueT.get_idTs v0) idt0 = false)
        st conf invst0
        gv0
  :
    <<EQ: InvState.Unary.sem_valueT conf st invst0 v0 =
          InvState.Unary.sem_valueT conf st (cons_idt_unary idt0 gv0 invst0) v0>>
  .
  Proof.
    red. unfold InvState.Unary.sem_valueT. des_ifs.
    erewrite cons_idt_spec_id; eauto.
    apply list_inb_single in CLEAR. des. des_sumbool.
    unfold proj_sumbool. des_ifs.
    contradict CLEAR. finish_by_refl.
  Qed.

  Lemma cons_idt_spec_list_value
        vs0 idt0
        (CLEAR: list_inb IdT.eq_dec
                         (filter_map ValueT.get_idTs (List.map snd vs0)) idt0 = false)
        st conf invst0
        gv0
  :
    <<EQ: InvState.Unary.sem_list_valueT conf st invst0 vs0 =
          InvState.Unary.sem_list_valueT conf st (cons_idt_unary idt0 gv0 invst0) vs0>>
  .
  Proof.
    red.
    ginduction vs0; ii; ss; des_ifs_safe; clarify.
    destruct t.
    + erewrite <- cons_idt_spec_value; cycle 1.
      { des_ifs. ss. clarify. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      exploit IHvs0; try eassumption.
      { instantiate (1:= idt0).
        des_ifs. ss. clarify. eapply list_inb_false_sub; eauto. repeat econs; eauto.
        eapply sublist_refl; eauto. }
      intro IH. erewrite <- IH.
      des_ifs.
    + erewrite <- cons_idt_spec_value; cycle 1.
      { des_ifs. }
      exploit IHvs0; try eassumption.
      intro IH. erewrite <- IH.
      des_ifs.
  Qed.

  Lemma cons_idt_spec_expr
        x idt0
        (CLEAR: list_inb IdT.eq_dec (Expr.get_idTs x) idt0 = false)
        st conf invst0
        gv0
  :
    <<EQ: InvState.Unary.sem_expr conf st invst0 x =
          InvState.Unary.sem_expr conf st (cons_idt_unary idt0 gv0 invst0) x>>
  .
  Proof.
    red.
    unfold Expr.get_idTs in *.
    destruct x; ss.
    - repeat erewrite <- cons_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- cons_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- cons_idt_spec_value; ss.
    - repeat erewrite <- cons_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- cons_idt_spec_value; ss.
      repeat erewrite <- cons_idt_spec_list_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto.
        eapply sublist_refl; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- cons_idt_spec_value; ss.
    - repeat erewrite <- cons_idt_spec_value; ss.
    - repeat erewrite <- cons_idt_spec_value; ss.
    - repeat erewrite <- cons_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- cons_idt_spec_value; ss.
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
      { des_ifs. ss. eapply list_inb_false_sub; eauto. repeat econs; eauto. }
    - repeat erewrite <- cons_idt_spec_value; ss.
      { des_ifs; ss; eapply list_inb_false_sub; eauto; repeat econs; eauto. }
      { des_ifs; ss; eapply list_inb_false_sub; eauto; repeat econs; eauto. }
      { des_ifs; ss; eapply list_inb_false_sub; eauto; repeat econs; eauto. }
    - repeat erewrite <- cons_idt_spec_value; ss.
    - repeat erewrite <- cons_idt_spec_value; ss.
  Qed.

  Local Opaque cons_idt_unary.
  Local Opaque InvState.Unary.clear_idt.

  Corollary cons_idt_expr_sim
        x idt0 gv_res
        conf st invst0
        (SEM: InvState.Unary.sem_expr
                conf st
                (InvState.Unary.clear_idt idt0 invst0) x
               = Some gv_res)
        gv0
    :
      <<SEM: InvState.Unary.sem_expr
               conf st
               (cons_idt_unary idt0 gv0 (InvState.Unary.clear_idt idt0 invst0)) x
               =
               (* Some gv_res *)
               (* This form is easier to use *)
               InvState.Unary.sem_expr
                 conf st
                 (InvState.Unary.clear_idt idt0 invst0) x>>
  .
  Proof.
    destruct idt0; ss.
    destruct t; ss.
    - erewrite <- cons_idt_spec_expr; try eassumption; ss.
      eapply clear_idt_inv_spec_expr; ss; eauto.
    - erewrite <- cons_idt_spec_expr; try eassumption; ss.
      eapply clear_idt_inv_spec_expr; ss; eauto.
  Qed.

End CONS_IDT.


Section SET_INV.

  Lemma in_ExprPairSet_inv
        e0 e1 idt0 eps
        (IN: ExprPairSet.In (e0, e1)
                            (ExprPairSet.clear_idt idt0 eps))
        (NOTPHYS: idt0.(fst) <> Tag.physical)
  :
    <<CLEAR0: list_inb IdT.eq_dec (Expr.get_idTs e0) idt0 = false>> /\
    <<CLEAR1: list_inb IdT.eq_dec (Expr.get_idTs e1) idt0 = false>>
  .
  Proof.
    unfold ExprPairSet.clear_idt in IN.
    eapply ExprPairSetFacts.filter_iff in IN; [ | solve_compat_bool ].
    des; des_bool.
    unfold ExprPair.get_idTs in *. ss.
    apply list_inb_false_app_inv in IN0. des. ss.
  Qed.

  Lemma in_ValueTPairSet_inv
        e0 e1 idt0 vps
        (IN: ValueTPairSet.In (e0, e1)
                            (ValueTPairSet.clear_idt idt0 vps))
        (NOTPHYS: idt0.(fst) <> Tag.physical)
  :
    <<CLEAR0: list_inb IdT.eq_dec (ValueT.get_idTs e0) idt0 = false>> /\
    <<CLEAR1: list_inb IdT.eq_dec (ValueT.get_idTs e1) idt0 = false>>
  .
  Proof.
    unfold ValueTPairSet.clear_idt in IN.
    eapply ValueTPairSetFacts.filter_iff in IN; [ | solve_compat_bool ].
    des; des_bool.
    unfold ValueTPair.get_idTs in *. ss.
    apply list_inb_false_app_inv in IN0. des. ss.
  Qed.

  Lemma in_PtrPairSet_inv
        e0 e1 idt0 vps
        (IN: PtrPairSet.In (e0, e1)
                            (PtrPairSet.clear_idt idt0 vps))
        (NOTPHYS: idt0.(fst) <> Tag.physical)
  :
    <<CLEAR0: list_inb IdT.eq_dec (Ptr.get_idTs e0) idt0 = false>> /\
    <<CLEAR1: list_inb IdT.eq_dec (Ptr.get_idTs e1) idt0 = false>>
  .
  Proof.
    unfold PtrPairSet.clear_idt in IN.
    eapply PtrPairSetFacts.filter_iff in IN; [ | solve_compat_bool ].
    des; des_bool.
    unfold PtrPair.get_idTs in *. ss.
    apply list_inb_false_app_inv in IN0. des. ss.
  Qed.

  Lemma in_IdTSet_inv
        e0 idt0 vps
        (IN: IdTSet.In e0 (IdTSet.clear_idt idt0 vps))
        (NOTPHYS: idt0.(fst) <> Tag.physical)
    :
      <<CLEAR: proj_sumbool (IdT.eq_dec e0 idt0) = false>>
  .
  Proof.
    unfold IdTSet.clear_idt in IN.
    eapply IdTSetFacts.filter_iff in IN; [ | solve_compat_bool ].
    des; des_bool.
    des_sumbool. destruct idt0; ss. destruct e0; ss.
    unfold proj_sumbool. des_ifs.
  Qed.

End SET_INV.

Lemma cons_ghost_unary_spec
      conf st x0 i0 gv
      invst0 invmem0 gmax pubs inv0
      (GV: InvState.Unary.sem_expr
             conf st (InvState.Unary.clear_idt (Exprs.Tag.ghost, i0) invst0) x0 = Some gv)
      (VALID: MemProps.valid_ptrs (Mem.nextblock (Mem st)) gv)
      (SEM: InvState.Unary.sem conf st
                               (InvState.Unary.clear_idt (Exprs.Tag.ghost, i0) invst0)
                               invmem0 gmax pubs
                               (Hints.Invariant.clear_idt_unary (Exprs.Tag.ghost, i0) inv0))
  :
    <<SEM: InvState.Unary.sem
             conf st
             (cons_idt_unary (Exprs.Tag.ghost, i0) gv
                               (InvState.Unary.clear_idt (Exprs.Tag.ghost, i0) invst0))
             invmem0 gmax
             pubs
             (Hints.Invariant.update_lessdef
                ((Exprs.ExprPairSet.add
                   (Exprs.Expr.value (Exprs.ValueT.id (Exprs.Tag.ghost, i0)), x0))
                   <*>
                   (Exprs.ExprPairSet.add
                      (x0, Exprs.Expr.value (Exprs.ValueT.id (Exprs.Tag.ghost, i0)))))
                (Hints.Invariant.clear_idt_unary (Exprs.Tag.ghost, i0) inv0))>>
.
Proof.
  Local Opaque InvState.Unary.clear_idt.
  econs; eauto; try apply SEM.
  - inv SEM. clear - GV LESSDEF.
    ii. ss.
    apply ExprPairSetFacts.add_iff in H.
    des.
    { solve_leibniz. clarify. ss.
      compute in VAL1. des_ifs.
      erewrite cons_idt_expr_sim; eauto.
      esplits; eauto.
      apply GVs.lessdef_refl.
    }
    apply ExprPairSetFacts.add_iff in H. des.
    { clarify. ss.
      solve_leibniz. ss.
      erewrite cons_idt_expr_sim in VAL1; eauto. rewrite VAL1 in *. clarify.
      exists gv; splits; ss.
      - compute. des_ifs.
      - apply GVs.lessdef_refl.
    }
    destruct x as [e0 e1]; ss.
    exploit in_ExprPairSet_inv; try eassumption; ss. i; des.
    erewrite <- cons_idt_spec_expr in VAL1; cycle 1; ss.
    exploit LESSDEF; eauto. i; des.
    esplits; eauto.
    erewrite <- cons_idt_spec_expr; ss.
  - inv SEM. clear - GV NOALIAS.
    econs; eauto; ss.
    + inv NOALIAS. clear - GV DIFFBLOCK.
      i.
      apply ValueTPairSetFacts.mem_iff in MEM.
      exploit in_ValueTPairSet_inv; try eassumption; ss. i; des.
      apply ValueTPairSetFacts.mem_iff in MEM.
      erewrite <- cons_idt_spec_value in VAL1; cycle 1; ss.
      erewrite <- cons_idt_spec_value in VAL2; cycle 1; ss.
      eapply DIFFBLOCK; eauto.
    + inv NOALIAS. clear - GV NOALIAS0.
      i.
      apply PtrPairSetFacts.mem_iff in MEM.
      exploit in_PtrPairSet_inv; try eassumption; ss. i; des.
      apply PtrPairSetFacts.mem_iff in MEM.
      unfold Ptr.get_idTs in *. des_ifs_safe.
      erewrite <- cons_idt_spec_value in VAL1; cycle 1; ss.
      erewrite <- cons_idt_spec_value in VAL2; cycle 1; ss.
      eapply NOALIAS0; eauto.
  - inv SEM. clear - GV PRIVATE.
    ss.
    ii.
    exploit in_IdTSet_inv; try eassumption; ss. i; des.
    erewrite <- cons_idt_spec_id in VAL; cycle 1; ss.
    eapply PRIVATE; eauto.
  - inv SEM. clear - GV WF_GHOST VALID.
    ii. ss. des_ifs.
    + eapply WF_GHOST; eauto. 
Qed.
