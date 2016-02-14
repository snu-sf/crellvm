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

Require Import FSetFacts.

Import Opsem.
Import syntax_ext.
Import hints.

Section HintSemEach.

  Definition hint_sem_each_md_inv md inv1 inv2
    alpha cfg1 cfg2 lc1 lc2 gmax li1 li2 mem1 mem2 iso1 iso2 : Prop :=
    exists olc1, exists olc2,
      (maydiff_sem lc1 lc2 alpha olc1 olc2 md) /\
      (invariant_sem cfg1 cfg2 lc1 lc2 mem1 mem2 olc1 olc2 gmax li1 li2
        (mkInvariant inv1 inv2 iso1 iso2)).

  Definition hint_sem_each_iso_als_gl_vm
    alpha gmax cfg1 cfg2 li1 pi1 li2 pi2 als1 als2 mem1 mem2 : Prop :=
    (allocas_equivalent alpha li1 li2 als1 als2) /\
    (globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2)) /\
    (valid_allocas mem1 mem2 als1 als2) /\
    (valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2).

  Definition hint_sem_each md inv1 inv2 iso1 iso2
    alpha gmax cfg1 cfg2 lc1 lc2 mem1 mem2
    li1 pi1 li2 pi2 als1 als2 vmem1 vmem2 : Prop :=
    hint_sem_each_md_inv md inv1 inv2 alpha cfg1 cfg2 lc1 lc2 gmax li1 li2
    mem1 mem2 iso1 iso2 /\
    hint_sem_each_iso_als_gl_vm alpha gmax cfg1 cfg2 li1 pi1 li2 pi2
    als1 als2 vmem1 vmem2.

End HintSemEach.

Lemma hint_sem_each_implies_hint_sem_insn:
  forall md inv1 inv2 iso1 iso2 alpha gmax cfg1 cfg2 mem1 mem2 li1 pi1 li2 pi2
    ir ec1 ec2 pecs1 pecs2 n1 pns1 n2 pns2
    (Hsem: hint_sem_each md inv1 inv2 iso1 iso2
      alpha gmax cfg1 cfg2 (Locals ec1) (Locals ec2) mem1 mem2
      li1 pi1 li2 pi2 (Allocas ec1) (Allocas ec2) mem1 mem2),
    (hint_sem_insn (mkInsnHint md (mkInvariant inv1 inv2 iso1 iso2) ir)
      pecs1 pecs2 pns1 pns2 pi1 pi2 li1 li2
      alpha gmax cfg1 (ec1::pecs1) mem1 (n1::pns1)
      cfg2 (ec2::pecs2) mem2 (n2::pns2)).
Proof.
  intros.
  destruct Hsem as
    [[olc1 [olc2 [Hmd [Hinv1 [Hinv2 [Hiso1 Hiso2]]]]]] [Hals [Hgl [Hva Hvm]]]].
  eapply hint_sem_insn_intro; eauto.
  exists olc1; exists olc2; done.
Qed.

Lemma hint_sem_insn_implies_hint_sem_each:
  forall md inv1 inv2 iso1 iso2 alpha gmax cfg1 cfg2 mem1 mem2 li1 pi1 li2 pi2
    ir ec1 ec2 pecs1 pecs2 n1 pns1 n2 pns2
    (Hinsn: hint_sem_insn (mkInsnHint md (mkInvariant inv1 inv2 iso1 iso2) ir)
      pecs1 pecs2 pns1 pns2 pi1 pi2 li1 li2
      alpha gmax cfg1 (ec1::pecs1) mem1 (n1::pns1)
      cfg2 (ec2::pecs2) mem2 (n2::pns2)),
    (hint_sem_each md inv1 inv2 iso1 iso2
      alpha gmax cfg1 cfg2 (Locals ec1) (Locals ec2) mem1 mem2
      li1 pi1 li2 pi2 (Allocas ec1) (Allocas ec2) mem1 mem2).
Proof.
  intros.
  inversion Hinsn; inversion Hsem as [olc1 [olc2 [Hmd Hinv]]];
    subst; simpl in *; clear Hinsn Hsem.
  split; [exists olc1; exists olc2; done|done].
Qed.

Ltac destruct_lstep_tac :=
  repeat
    match goal with
      | [H: pop_state_ocmd (?ec :: _) ?ns (ret _) |- _] =>
        let n1 := fresh "n" in
          let n2 := fresh "n" in
            let pop := fresh "pop" in
              simpl in H; destruct ns as [|n1 n2]; try done;
                remember (pop_one_X (CurCmds ec) n1) as pop;
                  destruct pop; try done; try subst
      | [H: match ?ns with
              | nil => False
              | hn :: _ =>
                match pop_one_X (CurCmds ?ec) _ with
                  | ret_pop_cmd _ _ _ => _
                  | ret_pop_terminator => _
                end
            end |- _] =>
        let n1 := fresh "n" in
          let n2 := fresh "n" in
            let pop := fresh "pop" in
              destruct ns as [|n1 n2]; try done;
                remember (pop_one_X (CurCmds ec) n1) as pop;
                  destruct pop; try done; try subst
      | [H: pop_state_ocmd (?ec :: _) ?ns merror |- _] =>
        let n1 := fresh "n" in
          let n2 := fresh "n" in
            let pop := fresh "pop" in
              simpl in H; destruct ns as [|n1 n2]; try done;
                remember (pop_one_X (CurCmds ec) n1) as pop;
                  destruct pop; try done; try subst
      | [H1: ret_pop_cmd (ret _) _ _ = pop_one_X (CurCmds ?ec) ?n,
        H2: logical_semantic_step _ _ {| ECS := ?ec :: _; Mem := _ |}
        _ (?n :: _) _ _ _ |- _] => inv H2
      | [H1: ret_pop_cmd merror _ _ = pop_one_X (CurCmds ?ec) ?n,
        H2: logical_semantic_step _ _ {| ECS := ?ec :: _; Mem := _ |}
        _ (?n :: _) _ _ _ |- _] => inv H2
      | [H: _ :: _ = _ :: _ |- _] => inv H
      | [H: ECS {| ECS := _ :: _; Mem := _ |} = _ :: _ |- _] => simpl in H; inv H
      | [H1: match ?pst with | pop_noop => _ | pop_cmd => _ | pop_terminator => _ end,
        H2: pop_one _ _ ?pst _ _ |- _] => destruct pst; inv H2
      | [H1: _ = pop_one_X ?x ?y, H2: pop_one_X ?x ?y = _ |- _] =>
        try by rewrite H2 in H1; inv H1; done
    end.

Lemma alpha_incr_preserves_hint_sem_each_md_inv:
  forall md inv1 inv2 alpha alpha' cfg1 cfg2 lc1 lc2 mem1 mem2 gmax li1 pi1 li2 pi2
    iso1 iso2
    (Hmi: hint_sem_each_md_inv md inv1 inv2 alpha cfg1 cfg2 lc1 lc2 gmax li1 li2
      mem1 mem2 iso1 iso2)
    (Hincr: inject_incr' alpha alpha' li1 pi1 li2 pi2),
    hint_sem_each_md_inv md inv1 inv2 alpha' cfg1 cfg2 lc1 lc2 gmax li1 li2
    mem1 mem2 iso1 iso2.
Proof.
  intros.
  destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
  exists olc1; exists olc2; splits; [|done]; clear Hinv.
  rr in Hmd; rr; intros; destruct x; destruct n;
    exploit Hmd; eauto; intro Hf; simpl in *.
  - destruct (lookupAL GVs olc1 i0); try done.
    destruct (lookupAL GVs olc2 i0); try done.
    inv Hincr; eapply gv_inject_incr; eauto.
  - destruct (lookupAL GVs lc1 i0); try done.
    destruct (lookupAL GVs lc2 i0); try done.
    inv Hincr; eapply gv_inject_incr; eauto.
Qed.

Lemma li1_incr_preserves_hint_sem_each_md_inv:
  forall md inv1 inv2 alpha cfg1 cfg2 lc1 lc2 mem1 mem2 gmax li1 li2
    iso1 iso2 mb
    (Hmi: hint_sem_each_md_inv md inv1 inv2 alpha cfg1 cfg2 lc1 lc2 gmax li1 li2
      mem1 mem2 iso1 iso2),
    hint_sem_each_md_inv md inv1 inv2 alpha cfg1 cfg2 lc1 lc2 gmax (mb::li1) li2
    mem1 mem2 iso1 iso2.
Proof.
  intros.
  destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
  exists olc1; exists olc2; splits; [done|]; clear Hmd.
  destruct Hinv as [Hinv1 [Hinv2 [Hiso1 Hiso2]]].
  rr; splits; try done.
  clear Hinv1 Hinv2 Hiso2; simpl in *.
  unfold isolated_sem, IdExtSetImpl.For_all in *; intros x Hxin.
  exploit Hiso1; eauto; intros [He|[xv [Hlookup Hin]]].
  - by left.
  - right; exists xv; split; [done|].
    destruct (GV2ptr (CurTargetData cfg1) (getPointerSize (CurTargetData cfg1)) xv);
      [|done].
    destruct v; try done.
    by right.
Qed.

Lemma li2_incr_preserves_hint_sem_each_md_inv:
  forall md inv1 inv2 alpha cfg1 cfg2 lc1 lc2 mem1 mem2 gmax li1 li2
    iso1 iso2 mb
    (Hmi: hint_sem_each_md_inv md inv1 inv2 alpha cfg1 cfg2 lc1 lc2 gmax li1 li2
      mem1 mem2 iso1 iso2),
    hint_sem_each_md_inv md inv1 inv2 alpha cfg1 cfg2 lc1 lc2 gmax li1 (mb::li2)
    mem1 mem2 iso1 iso2.
Proof.
  intros.
  destruct Hmi as [olc1 [olc2 [Hmd Hinv]]].
  exists olc1; exists olc2; splits; [done|]; clear Hmd.
  destruct Hinv as [Hinv1 [Hinv2 [Hiso1 Hiso2]]].
  rr; splits; try done.
  clear Hinv1 Hinv2 Hiso1; simpl in *.
  unfold isolated_sem, IdExtSetImpl.For_all in *; intros x Hxin.
  exploit Hiso2; eauto; intros [He|[xv [Hlookup Hin]]].
  - by left.
  - right; exists xv; split; [done|].
    destruct (GV2ptr (CurTargetData cfg2) (getPointerSize (CurTargetData cfg2)) xv);
      [|done].
    destruct v; try done.
    by right.
Qed.

Lemma li1_incr_preserves_allocas_equivalent:
  forall alpha mb li1 li2 als1 als2
    (Hnin: ~ In mb als1)
    (Hals: allocas_equivalent alpha li1 li2 als1 als2),
    allocas_equivalent alpha (mb::li1) li2 als1 als2.
Proof.
  intros; generalize dependent als2; induction als1; intros.
  - induction als2.
    + econstructor.
    + inv Hals; econstructor; eauto.
  - induction als2.
    + inv Hals; econstructor; eauto.
      * by right.
      * eapply IHals1; eauto.
        by intro Hcontr; elim Hnin; right.
    + inv Hals.
      * eapply allocas_equivalent_ignore_left; eauto.
          by right.
          eapply IHals1; eauto.
          by intro Hcontr; elim Hnin; right.
      * eapply allocas_equivalent_ignore_right; eauto.
      * eapply allocas_equivalent_map; eauto.
          intro Hcontr; elim Hbin1.
          simpl in Hcontr; destruct Hcontr as [Hcontr|Hres]; [|done].
          by subst mb; elim Hnin; left.
          eapply IHals1; eauto.
          by intro Hcontr; elim Hnin; right.
Qed.

Lemma li2_incr_preserves_allocas_equivalent:
  forall alpha mb li1 li2 als1 als2
    (Hnin: ~ In mb als2)
    (Hals: allocas_equivalent alpha li1 li2 als1 als2),
    allocas_equivalent alpha li1 (mb::li2) als1 als2.
Proof.
  intros; generalize dependent als1; induction als2; intros.
  - induction als1.
    + econstructor.
    + inv Hals; econstructor; eauto.
  - induction als1.
    + inv Hals; econstructor; eauto.
      * by right.
      * eapply IHals2; eauto.
        by intro Hcontr; elim Hnin; right.
    + inv Hals. 
      * eapply allocas_equivalent_ignore_left; eauto.
      * eapply allocas_equivalent_ignore_right; eauto.
          by right.
          eapply IHals2; eauto.
          by intro Hcontr; elim Hnin; right.
      * eapply allocas_equivalent_map; eauto.
          intro Hcontr; elim Hbin2.
          simpl in Hcontr; destruct Hcontr as [Hcontr|Hres]; [|done].
          by subst mb; elim Hnin; left.
          eapply IHals2; eauto.
          by intro Hcontr; elim Hnin; right.
Qed.

Lemma alpha_incr_preserves_allocas_equivalent:
  forall alpha alpha' li1 li2 pi1 pi2 als1 als2
    (Hals: allocas_equivalent alpha li1 li2 als1 als2)
    (Hincr: inject_incr' alpha alpha' li1 pi1 li2 pi2),
    allocas_equivalent alpha' li1 li2 als1 als2.
Proof.
  induction als1; induction als2; intros.
  - by econstructor.
  - by inv Hals; econstructor; eauto.
  - by inv Hals; econstructor; eauto.
  - inv Hals.
    + by eapply allocas_equivalent_ignore_left; eauto.
    + by eapply allocas_equivalent_ignore_right; eauto.
    + eapply allocas_equivalent_map; eauto.
      destruct Hincr as [Hmap _].
      eapply Hmap; eauto.
Qed.

Lemma alpha_incr_preserves_globals_equivalent:
  forall alpha alpha' gmax gl1 gl2 li1 pi1 li2 pi2
    (Hgl: globals_equivalent alpha gmax gl1 gl2)
    (Hincr: inject_incr' alpha alpha' li1 pi1 li2 pi2),
    globals_equivalent alpha' gmax gl1 gl2.
Proof.
  intros; inv Hgl; subst.
  by eapply globals_equivalent_intro with (gl:=gl2).
Qed.

Lemma locals_update_preserves_isolated_sem:
  forall td iso olc lc li1 i iv
    (Hi: isolated_sem td olc lc li1 iso)
    (Hnotin: false = IdExtSetImpl.mem (i, ntag_new) iso),
    isolated_sem td olc (updateAddAL GVs lc i iv) li1 iso.
Proof.
  intros; rr; rr in Hi; intros.
  assert (Hnix: x <> (i0, ntag_new)) by
    (intro; subst; apply IdExtSetFacts.mem_iff in H; rewrite H in Hnotin; done).
  exploit Hi; eauto; intros [He|[gvp [Hlook Hli]]].
  - left. destruct x as [x [|]]; simpl in *; [done|].
    rewrite <- lookupAL_updateAddAL_neq; eauto.
    intro Hcontr; elim Hnix; subst; done.
  - right; exists gvp; split; [|done].
    destruct x as [x [|]]; simpl in *; [done|].
    rewrite <- lookupAL_updateAddAL_neq; eauto.
    intro Hcontr; elim Hnix; subst; done.
Qed.

Lemma locals_left_update_preserves_isolated_sem:
  forall td iso olc lc mem li1 i mb typ5
    (Hi: isolated_sem td olc lc li1 iso)
    (Hfreeable: free td mem (blk2GV td mb) <> merror)
    (Hnotin: true = IdExtSetImpl.mem (i, ntag_new) iso),
    isolated_sem td olc (updateAddAL GVs lc i
      ($ blk2GV td mb # typ_pointer typ5 $)) (mb::li1) iso.
Proof.
  intros; rr; rr in Hi; intros.
  remember (id_ext_dec x (i0, ntag_new)) as xidec; destruct xidec.
  - subst; right; exists (blk2GV td mb); split.
    + by apply lookupAL_updateAddAL_eq.
    + by left.
  - exploit Hi; eauto; intros [He|[gvp [Hlook Hli]]].
    + left. destruct x as [x [|]]; simpl in *; [done|].
      rewrite <- lookupAL_updateAddAL_neq; eauto.
      intro Hcontr; elim n; subst; done.
    + right; exists gvp; split.
      * destruct x as [x [|]]; simpl in *; [done|].
        rewrite <- lookupAL_updateAddAL_neq; eauto.
        intro Hcontr; elim n; subst; done.
      * destruct (GV2ptr td (getPointerSize td) gvp); try done.
        destruct v; try done.
        by right.
Qed.
