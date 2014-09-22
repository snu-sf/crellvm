Require Import vgtac.
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

Section HintSemEach.

  Lemma add_neq_preserves_hint_sem_each_aux:
    forall cfg fn_al ec ec' ecs ecs' mem mem' gmax ns ns' na' tr inv ocmd olc gids
      (Hgids: is_global_ids gids (Globals cfg))

      (Hstep: logical_semantic_step cfg fn_al
        {| ECS := ec :: ecs; Mem := mem |}
        {| ECS := ec' :: ecs'; Mem := mem' |} ns ns' na' tr)
      (Hpop: pop_state_ocmd (ec::ecs) ns ocmd)
      (Hncall: forall rid, ~ is_general_call ocmd rid)
      (Hsu: self_use_check ocmd = true)
      (Hinv : eqs_sem cfg olc (Locals ec') mem gmax inv),
      eqs_sem cfg olc (Locals ec') mem gmax
      (vars_aux.add_pointer_non_equations inv ocmd gids).

  Proof.
    intros.
    destruct ocmd as [cmd|]; destruct_lstep_tac.
    destruct cmd; try done; destruct_step_tac; inv Hstep0.

    destruct inv as [ireg iheap inreg]; simpl in *.
    destruct Hinv as [Hireg [Hiheap Hinreg]].

    rr; splits; [done|done|]; clear Hiheap; simpl in *.

    exploit memory_props.MemProps.malloc_result; eauto; intro Hmb.
    unfold vars_aux.add_pointer_non_equations_mm in *.
    rewrite EqRegSetImpl.fold_1, <-fold_left_rev_right.
    unfold eqs_eq_reg_sem in Hireg.
    assert (Hireg_e:
      forall (x : id_ext) (r : rhs_ext),
        existsb (EqRegSetFacts.eqb (x, r)) (rev (EqRegSetImpl.elements ireg)) ->
        eq_reg_sem
        {|
          CurSystem := S;
          CurTargetData := TD;
          CurProducts := Ps;
          Globals := gl;
          FunTable := fs |} olc
        (updateAddAL GVs Locals0 id5
          ($ blk2GV TD mb # typ_pointer typ5 $)) mem0 gmax x r).
    - intros.
      rewrite <-AtomSetFacts2.existsb_rev in H.
      rewrite <-EqRegSetFacts.elements_b in H.
      exploit Hireg; eauto.
    clear Hireg.
    remember (rev (EqRegSetImpl.elements ireg)) as iregl; clear Heqiregl.
    induction iregl; [done|].

    intros; simpl.
    hexploit IHiregl.
    - intros; eapply Hireg_e; eauto.
      by simpl; apply orb_true_iff; right.
    intro Hbrd; clear IHiregl.
    remember (fold_right
      (fun (y : id_ext * rhs_ext) (x : NeqRegSetImpl.t) =>
        vars_aux.add_pointer_non_equations_mm_aux x id5 y) inreg iregl) as finv.
    clear Heqfinv.

    unfold vars_aux.add_pointer_non_equations_mm_aux.
    destruct a; try done.
    destruct r; try done.
    unfold eqs_neq_reg_sem in *; intros.
    rewrite NeqRegSetFacts.add_b in H; apply orb_true_iff in H.
    destruct H as [Hneq|H].

    - clear Hbrd; unfold NeqRegSetFacts.eqb in Hneq.
      destruct (NeqRegSetFacts.eq_dec (vars_aux.add_ntag id5, inl i0) (x, y)); [|done].
      inv e; clear Hneq.

      exploit Hireg_e.
      + instantiate (1:=rhs_ext_old_alloca); instantiate (1:=i0).
        simpl; apply orb_true_iff; left.
        unfold EqRegSetFacts.eqb.
        destruct (EqRegSetFacts.eq_dec
          (i0, rhs_ext_old_alloca) (i0, rhs_ext_old_alloca)); done.
      intro Hfact; inv Hfact; [by inv Hrhs|].
      simpl in Hptr.

      unfold neq_reg_sem; simpl.
      rewrite Hlookup.
      rewrite lookupAL_updateAddAL_eq; eauto.

      unfold GV2ptr in Hptr.
      destruct gvs; try done. destruct p; destruct v; try done.
      destruct gvs; try done; inv Hptr.
      assert (Hmb: $ blk2GV TD (Mem.nextblock mem0) # typ_pointer typ5 $
        = blk2GV TD (Mem.nextblock mem0)) by done.
      rewrite Hmb; clear Hmb.
      unfold blk2GV, ptr2GV, val2GV; split.
      + intro Hcontr.
        apply eq_gvs_implies_setoid_eq in Hcontr.
        inversion Hcontr; subst xblk; omega.
      + rr; splits; [|done|done].
        simpl; splits; try done.
        intro Hcontr; subst; omega.

    rewrite NeqRegSetFacts.add_b in H; apply orb_true_iff in H.
    destruct H as [Hneq|H].

    - clear Hbrd; unfold NeqRegSetFacts.eqb in Hneq.
      destruct (NeqRegSetFacts.eq_dec (i0, inl (vars_aux.add_ntag id5)) (x, y)); [|done].
      inv e; clear Hneq.

      exploit Hireg_e.
      + instantiate (1:=rhs_ext_old_alloca); instantiate (1:=x).
        simpl; apply orb_true_iff; left.
        unfold EqRegSetFacts.eqb.
        destruct (EqRegSetFacts.eq_dec
          (x, rhs_ext_old_alloca) (x, rhs_ext_old_alloca)); done.
      intro Hfact; inv Hfact; [by inv Hrhs|].
      simpl in Hptr.

      unfold neq_reg_sem; simpl.
      rewrite Hlookup.
      rewrite lookupAL_updateAddAL_eq; eauto.

      unfold GV2ptr in Hptr.
      destruct gvs; try done. destruct p; destruct v; try done.
      destruct gvs; try done; inv Hptr.
      assert (Hmb: $ blk2GV TD (Mem.nextblock mem0) # typ_pointer typ5 $
        = blk2GV TD (Mem.nextblock mem0)) by done.
      rewrite Hmb; clear Hmb.
      unfold blk2GV, ptr2GV, val2GV; split.
      + intro Hcontr.
        apply eq_gvs_implies_setoid_eq in Hcontr.
        inversion Hcontr; subst xblk; omega.
      + rr; splits; [|done|done].
        simpl; splits; try done.
        intro Hcontr; subst; omega.

    eapply Hbrd; eauto.

  Qed.

  Variable
    (cfg1 cfg2: Config) (fn_al1 fn_al2: AssocList noop_t)
    (ec1 ec1' ec2 ec2': @ExecutionContext DGVs)
    (ecs1 ecs1' ecs2 ecs2': @ECStack DGVs)
    (mem1 mem1' mem2 mem2': mem) (ns1 ns1' ns2 ns2': noop_stack_t)
    (na1' na2': new_alloca_t) (tr: trace) (li1 pi1 li2 pi2: list mblock)
    (ocmd1 ocmd2: option cmd).

  Hypothesis
    (Hstep1: logical_semantic_step cfg1 fn_al1
      (mkState (ec1::ecs1) mem1) (mkState (ec1'::ecs1') mem1')
      ns1 ns1' na1' tr)
    (Hstep2: logical_semantic_step cfg2 fn_al2
      (mkState (ec2::ecs2) mem2) (mkState (ec2'::ecs2') mem2')
      ns2 ns2' na2' tr)
    (Hpop1: pop_state_ocmd (ec1::ecs1) ns1 ocmd1)
    (Hpop2: pop_state_ocmd (ec2::ecs2) ns2 ocmd2)
    (Hncall1: forall rid, ~ is_general_call ocmd1 rid)
    (Hncall2: forall rid, ~ is_general_call ocmd2 rid)
    (Heqtd: CurTargetData cfg1 = CurTargetData cfg2).
  
  Definition r1 := Locals ec1.
  Definition r2 := Locals ec2.
  Definition r1' := Locals ec1'.
  Definition r2' := Locals ec2'.
  Definition als1 := Allocas ec1.
  Definition als2 := Allocas ec2.
  Definition als1' := Allocas ec1'.
  Definition als2' := Allocas ec2'.

  Lemma add_neq_preserves_hint_sem_each:
    forall md iso1 iso2 alpha' inv1 inv2 gmax gids1 gids2

      (Hsu1: self_use_check ocmd1 = true)
      (Hsu2: self_use_check ocmd2 = true)
      (Hgids1: is_global_ids gids1 (Globals cfg1))
      (Hgids2: is_global_ids gids2 (Globals cfg2))

      (Hsem: hint_sem_each md inv1 inv2 iso1 iso2
        alpha' gmax cfg1 cfg2 r1' r2' mem1 mem2
        li1 pi1 li2 pi2 als1' als2' mem1' mem2'),

      (hint_sem_each md 
        (vars_aux.add_pointer_non_equations inv1 ocmd1 gids1)
        (vars_aux.add_pointer_non_equations inv2 ocmd2 gids2) iso1 iso2
        alpha' gmax cfg1 cfg2 r1' r2' mem1 mem2
        li1 pi1 li2 pi2 als1' als2' mem1' mem2').
  Proof.
    intros.
    destruct Hsem as [[olc1 [olc2 [Hmd [Hinv1 [Hinv2 [Hiso1 Hiso2]]]]]] Hiav].
    split; try done.
    exists olc1; exists olc2; split; [done|].
    rr; splits; try done; simpl in *; eapply add_neq_preserves_hint_sem_each_aux; eauto.
  Qed.

End HintSemEach.

(* 
*** Local Variables: ***
***
*** coq-prog-args: ("-emacs" "-impredicative-set") ******
***
*** End: ***
 *)
