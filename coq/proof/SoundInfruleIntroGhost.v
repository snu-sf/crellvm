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



Lemma list_inb_false_app
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
      (INB: list_inb IdTSetFacts.eq_dec [x0] idt0 = dec)
  :
    <<DEC: proj_sumbool (IdTSetFacts.eq_dec idt0 x0) = dec>>
.
Proof.
  unfold list_inb, is_some in *. ss.
  des_ifs.
Qed.

Definition cons_ghost (i0: id) (gv_src gv_tgt: GenericValue)
           (inv0: InvState.Rel.t): InvState.Rel.t :=
  InvState.Rel.mk (InvState.Unary.update_ghost
                     (fun idgs => (i0, gv_src) :: idgs) inv0.(InvState.Rel.src))
                  (InvState.Unary.update_ghost
                     (fun idgs => (i0, gv_tgt) :: idgs) inv0.(InvState.Rel.tgt))
.

Section CLEAR_IDTS.

  Lemma clear_idt_spec_id
        i0 idt0
        (CLEAR: proj_sumbool (IdTSetFacts.eq_dec i0 idt0) = false)
        st_src invst0
  :
    <<EQ: InvState.Unary.sem_idT st_src invst0 i0 =
          InvState.Unary.sem_idT st_src (InvState.Unary.clear_idt idt0 invst0) i0>>
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

  Lemma clear_idt_spec_inv_id
        i0 idt0 st_src invst0
        gv
        (SOME: InvState.Unary.sem_idT st_src (InvState.Unary.clear_idt idt0 invst0) i0
               = Some gv)
        (NOTPHYSICAL: idt0.(fst) <> Tag.physical)
    :
      (* <<NOTIN: idt0 <> i0>> *)
      <<CLEAR: proj_sumbool (IdTSetFacts.eq_dec i0 idt0) = false>>
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

  Lemma clear_idt_spec_value
        v0 idt0
        (CLEAR: list_inb IdTSetFacts.eq_dec (ValueT.get_idTs v0) idt0 = false)
        conf_src st_src invst0
    :
      <<EQ: InvState.Unary.sem_valueT conf_src st_src invst0 v0 =
            InvState.Unary.sem_valueT conf_src st_src (InvState.Unary.clear_idt idt0 invst0) v0>>
  .
  Proof.
    red. unfold InvState.Unary.sem_valueT. des_ifs.
    erewrite clear_idt_spec_id; eauto.
    apply list_inb_single in CLEAR. des. des_sumbool.
    unfold proj_sumbool. des_ifs.
  Qed.

  Lemma clear_idt_spec_list_value
        vs0 idt0
        (CLEAR: list_inb IdTSetFacts.eq_dec (filter_map ValueT.get_idTs (List.map snd vs0)) idt0 = false)
        conf_src st_src invst0
    :
      <<EQ: InvState.Unary.sem_list_valueT conf_src st_src invst0 vs0 =
            InvState.Unary.sem_list_valueT conf_src st_src (InvState.Unary.clear_idt idt0 invst0) vs0>>
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
        (CLEAR: list_inb IdTSetFacts.eq_dec (Expr.get_idTs x) idt0 = false)
        conf_src st_src invst0
    :
      <<EQ: InvState.Unary.sem_expr conf_src st_src invst0 x =
            InvState.Unary.sem_expr conf_src st_src (InvState.Unary.clear_idt idt0 invst0) x>>
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
        conf_src st_src invst0
    :
      <<EQ: InvState.Unary.sem_expr conf_src st_src invst0 ep.(fst) =
            InvState.Unary.sem_expr conf_src st_src (InvState.Unary.clear_idt idt0 invst0) ep.(fst)>> /\
            <<EQ: InvState.Unary.sem_expr conf_src st_src invst0 ep.(snd) =
                  InvState.Unary.sem_expr conf_src st_src (InvState.Unary.clear_idt idt0 invst0) ep.(snd)>>
  .
  Proof.
    unfold NW. destruct ep; ss.
    unfold ExprPairSet.clear_idt in *.
    apply ExprPairSetFacts.filter_iff in CLEAR; [| solve_compat_bool ].
    repeat (des; des_bool).
    apply list_inb_false_app in CLEAR0. des. ss.
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
        apply list_inb_false_app in MEM0. des.
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
        apply list_inb_false_app in MEM0. des.
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
      destruct (IdTSetFacts.eq_dec id0 (Tag.ghost, i0)).
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
