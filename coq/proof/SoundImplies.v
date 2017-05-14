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
Require Import Validator.
Require Import Exprs.
Require Import Hints.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.


(* TODO: move to somewhere *)
Ltac solve_bool_true :=
  repeat
    (try match goal with
         | [H: andb ?a ?b = true |- _] =>
           apply andb_true_iff in H; des
         | [H: orb ?a ?b = true |- _] =>
           apply orb_true_iff in H; des
         | [H: proj_sumbool (?dec ?a ?b) = true |- _] =>
           destruct (dec a b)
         end;
     try subst; ss; unfold is_true in *; unfold sflib.is_true in *).

Ltac solve_match_bool :=
  repeat (match goal with
          | [H:match ?c with _ => _ end = true |- _] =>
            let MATCH := fresh "MATCH" in
            destruct c eqn:MATCH; try done
          | [H:match ?c with _ => _ end = false |- _] =>
            let MATCH := fresh "MATCH" in
            destruct c eqn:MATCH; try done
          end).

Lemma list_forall2_refl
      X P (l: list X)
      (REFL: reflexive X P):
  <<REFL: list_forall2 P l l>>.
Proof.
  induction l; econs; eauto.
Qed.

Lemma list_forall2_trans
      X P
      (l1 l2 l3: list X)
      (FORALL1: list_forall2 P l1 l2)
      (FORALL2: list_forall2 P l2 l3)
      (IMPLIES: transitive X P):
  <<FORALL: list_forall2 P l1 l3>>.
Proof.
  revert l3 FORALL2.
  induction FORALL1; destruct l3; eauto.
  - i. inv FORALL2.
  - econs; inv FORALL2; try apply IHFORALL1; eauto.
Qed.

(* TODO: position *)
Program Instance PreOrder_GVs_lessdef: PreOrder GVs.lessdef.
Next Obligation.
  ii. apply list_forall2_refl. ss.
Qed.
Next Obligation.
  ii. unfold GVs.lessdef in *.
  eapply list_forall2_trans; eauto.
  ii. des.
  split.
  - eapply Values.Val.lessdef_trans; eauto.
  - etransitivity; eauto.
Qed.

Lemma implies_lessdef_sound
      ld0 ld1 invst conf st
      (IMPLIES_LESSDEF: Invariant.implies_lessdef ld0 ld1)
      (LESSDEF: ExprPairSet.For_all (InvState.Unary.sem_lessdef conf st invst) ld0):
    <<LESSDEF: ExprPairSet.For_all (InvState.Unary.sem_lessdef conf st invst) ld1>>.
Proof.
  ii. apply ExprPairSet.for_all_2 in IMPLIES_LESSDEF; eauto; cycle 1.
  { ii. subst. ss. }
  specialize (IMPLIES_LESSDEF x H). ss.
  apply ExprPairSet.exists_2 in IMPLIES_LESSDEF; eauto; cycle 1.
  { ii. subst. ss. }
  inv IMPLIES_LESSDEF. des. solve_bool_true.
  expl LESSDEF.
Qed.

Lemma implies_diffblock_sound
      inv0 conf st invst gmax
      val1 val2 gval1 gval2
      (UNIQUE : AtomSetImpl.For_all (InvState.Unary.sem_unique conf st gmax) (Invariant.unique inv0))
      (IMPLIES_ALIAS : Invariant.diffblock_by_unique inv0 val1 val2 = true)
      (GLOBALS : genericvalues_inject.wf_globals gmax (Globals conf))
      (VAL1: InvState.Unary.sem_valueT conf st invst val1 = Some gval1)
      (VAL2: InvState.Unary.sem_valueT conf st invst val2 = Some gval2)
  :
    <<DIFFBLOCK: InvState.Unary.sem_diffblock conf gval1 gval2>>
.
Proof.
  red.
  unfold Invariant.diffblock_by_unique in *.
  move IMPLIES_ALIAS at bottom.
  repeat (des_bool; des);
    unfold Invariant.is_unique_value in *; des_ifs;
      unfold Invariant.values_diffblock_from_unique in *; repeat (des_bool; des);
        destruct x; destruct t; ss.
  +
    clear IMPLIES_ALIAS0.
    des_ifs.
    * (* tag is physical *)
      clear IMPLIES_ALIAS1.

      apply AtomSetFacts.mem_iff in IMPLIES_ALIAS2.
      exploit UNIQUE; try eapply IMPLIES_ALIAS2; []; intros HUniq; des.
      inv HUniq. clear MEM GLOBALS.

      unfold InvState.Unary.sem_idT in *. ss.
      clarify.

      exploit UNIQUE; eauto; []; ii; des.
      eapply LOCALS with (reg := i1); eauto.
      {
        des_sumbool.
        ii.
        unfold not in IMPLIES_ALIAS.
        apply IMPLIES_ALIAS.
        subst.
        ss.
      }
    * (* const *)
      unfold AtomSetImpl.For_all in *.
      eapply AtomSetFacts.mem_iff in IMPLIES_ALIAS2.
      specialize (UNIQUE i0 IMPLIES_ALIAS2). clear IMPLIES_ALIAS2.

      eapply unique_const_diffblock; eauto.
  + (* exactly copied from above *)
    clear IMPLIES_ALIAS0.
    des_ifs.
    * (* tag is physical *)
      clear IMPLIES_ALIAS1.

      apply AtomSetFacts.mem_iff in IMPLIES_ALIAS2.
      exploit UNIQUE; try eapply IMPLIES_ALIAS2; []; intros HUniq; des.
      inv HUniq. clear MEM GLOBALS.

      unfold InvState.Unary.sem_idT in *. ss.
      clarify.

      exploit UNIQUE; eauto; []; ii; des.
      eapply LOCALS with (reg := i1); eauto.
      {
        des_sumbool.
        ii.
        unfold not in IMPLIES_ALIAS.
        apply IMPLIES_ALIAS.
        subst.
        ss.
      }
    * (* const *)
      unfold AtomSetImpl.For_all in *.
      eapply AtomSetFacts.mem_iff in IMPLIES_ALIAS2.
      specialize (UNIQUE i0 IMPLIES_ALIAS2). clear IMPLIES_ALIAS2.

      eapply InvState.Unary.diffblock_comm.
      eapply unique_const_diffblock; eauto.
Qed.

(* TODO: premise for unique *)
Lemma implies_alias_sound
      inv0 inv1 conf st invst gmax
      (UNIQUE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf st gmax) (Invariant.unique inv0))
      (IMPLIES_ALIAS: Invariant.implies_alias inv0 inv0.(Invariant.alias) inv1.(Invariant.alias) = true)
      (ALIAS: InvState.Unary.sem_alias conf st invst (Invariant.alias inv0))
      public mem invmem
      (MEM: InvMem.Unary.sem conf gmax public mem invmem)
  :
  <<ALIAS: InvState.Unary.sem_alias conf st invst (Invariant.alias inv1)>>.
Proof.
  inv MEM.
  clear WF PRIVATE_PARENT MEM_PARENT UNIQUE_PARENT_MEM
        UNIQUE_PARENT_GLOBALS UNIQUE_PRIVATE_PARENT NEXTBLOCK.
  inv ALIAS.
  unfold Invariant.implies_alias in *.
  solve_bool_true.
  econs.
  - clear IMPLIES_ALIAS NOALIAS.
    unfold Invariant.implies_diffblock, flip in *.
    i. apply ValueTPairSet.for_all_2 in IMPLIES_ALIAS0; cycle 1.
    { solve_compat_bool. }
    apply ValueTPairSet.mem_2 in MEM.
    specialize (IMPLIES_ALIAS0 (val1, val2) MEM). ss.
    des_bool.
    des; cycle 1.
    { eapply DIFFBLOCK; eauto. }
    eapply ValueTPairSetFacts.mem_iff in MEM.
    eapply implies_diffblock_sound; eauto.
  - clear IMPLIES_ALIAS0 DIFFBLOCK.
    unfold Invariant.implies_noalias, flip in *.
    i. apply PtrPairSet.for_all_2 in IMPLIES_ALIAS; cycle 1.
    { solve_compat_bool. }
    apply PtrPairSet.mem_2 in MEM.
    specialize (IMPLIES_ALIAS (ptr1, ptr2) MEM). ss.
    des_bool.
    des; cycle 1.
    { eapply NOALIAS; eauto. }
    eapply PtrPairSetFacts.mem_iff in MEM.
    eapply implies_diffblock_sound; eauto.
Qed.

Lemma implies_unique_sound
      inv0 inv1 conf st gmax
      (IMPLIES_UNIQUE:AtomSetImpl.subset (Invariant.unique inv1) (Invariant.unique inv0) = true)
      (UNIQUE : AtomSetImpl.For_all (InvState.Unary.sem_unique conf st gmax)
                                    (Invariant.unique inv0)):
  <<UNIQUE:
    AtomSetImpl.For_all
      (InvState.Unary.sem_unique conf st gmax)
      (Invariant.unique inv1)>>.
Proof.
  ii. apply AtomSetImpl.subset_2 in IMPLIES_UNIQUE; eauto.
Qed.

Lemma implies_private_sound
      inv0 inv1 conf st invst
      private_parent public
      (IMPLIES_PRIVATE : IdTSet.subset (Invariant.private inv1)
                                       (Invariant.private inv0) = true)
      (PRIVATE : IdTSet.For_all
                   (InvState.Unary.sem_private conf st invst private_parent public)
                   (Invariant.private inv0)):
  <<PRIVATE: IdTSet.For_all
               (InvState.Unary.sem_private conf st invst private_parent public)
               (Invariant.private inv1)>>.
Proof.
  intros id. apply IdTSet.subset_2 in IMPLIES_PRIVATE; eauto.
Qed.

Lemma implies_unary_sound
    inv0 inv1 invmem invst conf st gmax public
    mem
    (IMPLIES_UNARY: Invariant.implies_unary inv0 inv1 = true)
    (MEM: InvMem.Unary.sem conf gmax public mem invmem)
    (UNARY: InvState.Unary.sem conf st invst invmem gmax public inv0):
      <<UNARY: InvState.Unary.sem conf st invst invmem gmax public inv1>>.
Proof.
  i. inv UNARY.
  unfold Invariant.implies_unary in IMPLIES_UNARY.
  solve_bool_true.
  econs; eauto.
  - eapply implies_lessdef_sound; eauto.
  - eapply implies_alias_sound; eauto.
  - eapply implies_unique_sound; eauto.
  - eapply implies_private_sound; eauto.
Qed.

Lemma implies_sound
      m_src conf_src st_src
      m_tgt conf_tgt st_tgt
      invst invmem inv0 inv1
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (IMPLIES: Invariant.implies inv0 inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv1>>.
Proof.
  unfold Invariant.implies in IMPLIES.
  solve_bool_true.
  { exfalso. eapply has_false_False; eauto. }
  inv STATE. econs.
  - eapply implies_unary_sound; eauto. apply MEM.
  - eapply implies_unary_sound; eauto. apply MEM.
  - i. apply MAYDIFF.
    apply IdTSetFacts.not_mem_iff. ii.
    apply IdTSetFacts.not_mem_iff in NOTIN. apply NOTIN.
    eapply IdTSetFacts.subset_iff; eauto.
  - ss.
Qed.



(* TODO: more idiomatic way to do this? by tactic? *)
(* TODO: position *)
Lemma dependent_apply
      (A B G: Prop)
      (LEMMA: A -> B)
      (PREMISE: A)
      (GOAL: A /\ B -> G)
  :
    <<GOAL: G>>
.
Proof.
  apply GOAL.
  split; ss.
  apply LEMMA. ss.
Qed.

Global Program Instance PreOrder_implies_lessdef: PreOrder Invariant.implies_lessdef.
Next Obligation.
  ii.
  unfold Invariant.implies_lessdef. unfold flip.
  apply Exprs.ExprPairSetFacts.for_all_iff.
  { solve_compat_bool. }
  ii.
  apply Exprs.ExprPairSetFacts.exists_iff.
  { solve_compat_bool. }
  unfold Exprs.ExprPairSet.Exists.
  esplits; eauto.
  (* TODO: enhance des_bool *)
  (* TODO: enhance des_sumbool *)
  unfold proj_sumbool in *. des_ifs.
Qed.
Next Obligation.
  ii.
  rename x into inva.
  rename y into invb.
  rename z into invc.
  unfold Invariant.implies_lessdef in *. unfold flip in *.
  apply Exprs.ExprPairSetFacts.for_all_iff.
  { solve_compat_bool. }
  apply Exprs.ExprPairSetFacts.for_all_iff in H; cycle 1.
  (* TODO: why compat_bool appears late in this case? *)
  { solve_compat_bool. }
  apply Exprs.ExprPairSetFacts.for_all_iff in H0; cycle 1.
  { solve_compat_bool. }
  (* TODO: I want to write solve_compat_bool only once. *)
  (* push subgoal as premise of original goal when "apply"ing? *)
  ii.
  expl H0.
  erewrite <- ExprPairSetFacts.exists_iff in H2; cycle 1.
  { solve_compat_bool. }
  unfold ExprPairSet.Exists in *.
  des. des_sumbool. clarify.
  expl H.
Qed.

Lemma wrap_is_true_goal
      A
  (*     (WRAPPED: is_true A) *)
  (* : *)
  (*   <<GOAL: A = true>> *)
  :
    is_true A -> A = true
.
Proof. ss. Qed.
Lemma wrap_is_true_hyp
      A
  (*     (WRAPPED: is_true A) *)
  (* : *)
  (*   <<GOAL: A = true>> *)
  :
    A = true -> is_true A
.
Proof. ss. Qed.

Lemma is_unique_value_Subset
      inv0 inv1
      (SUBSET: Invariant.unique inv0 [<=] Invariant.unique inv1)
      v
      (DIFFBLOCK: Invariant.is_unique_value inv0 v)
  :
    <<DIFFBLOCK: Invariant.is_unique_value inv1 v>>
.
Proof.
  unfold Invariant.is_unique_value in *. des_ifs.
  unfold is_true in *. (* TODO: enhance des_bool *)
  des_bool. des.
  des_sumbool. destruct x; ss; clarify.
  apply andb_true_iff.
  splits; ss.
  exploit SUBSET; try eapply AtomSetFacts.mem_iff; eauto.
Qed.

Lemma diffblock_by_unique_Subset
      inv0 inv1
      (SUBSET: Invariant.unique inv0 [<=] Invariant.unique inv1)
      v1 v2
      (DIFFBLOCK: Invariant.diffblock_by_unique inv0 v1 v2)
  :
    <<DIFFBLOCK: Invariant.diffblock_by_unique inv1 v1 v2>>
.
Proof.
  unfold Invariant.diffblock_by_unique in *.
  unfold is_true in *.
  red. apply andb_true_iff.
  des_bool; des.
  splits; ss.
  apply orb_true_iff.
  repeat (des_bool; des).
  - left.
    apply andb_true_iff.
    splits; ss.
    eapply is_unique_value_Subset; eauto.
  - right.
    apply andb_true_iff.
    splits; ss.
    eapply is_unique_value_Subset; eauto.
Qed.

Global Program Instance PreOrder_implies_unary: PreOrder Invariant.implies_unary.
Next Obligation.
  ii.
  unfold Invariant.implies_unary.
  repeat (apply andb_true_iff; split); try apply wrap_is_true_goal.
  (* TODO: wrap_is_true. Can we do this without lemma? soley by tactic? *)
  - reflexivity.
  - unfold Invariant.implies_noalias.
    unfold flip.
    apply Exprs.PtrPairSetFacts.for_all_iff.
    { solve_compat_bool. }
    ii.
    destruct x0; ss. destruct t, t0; ss.
    apply orb_true_iff. right.
    apply Exprs.PtrPairSetFacts.mem_iff. ss.
  - unfold Invariant.implies_diffblock. unfold flip.
    apply Exprs.ValueTPairSetFacts.for_all_iff.
    { solve_compat_bool. }
    ii.
    apply orb_true_iff. right.
    apply Exprs.ValueTPairSetFacts.mem_iff.
    ss.
  - apply AtomSetFacts.subset_iff. ss.
  - apply Exprs.IdTSetFacts.subset_iff. ss.
Qed.
Next Obligation.
  ii. rename H into HA. rename H0 into HB.
  unfold Invariant.implies_unary in *.
  unfold is_true in HA, HB.
  repeat (des_bool; des).
  unfold Invariant.implies_alias in *. des_bool; des.
  apply_all_once wrap_is_true_hyp.
  repeat (apply andb_true_iff; split); try apply wrap_is_true_goal.
  - etransitivity; eauto.
  - clear - HA2 HB2 HA1 HB1.
    unfold Invariant.implies_noalias in *.
    unfold flip in *.
    apply Exprs.PtrPairSetFacts.for_all_iff.
    { solve_compat_bool. }
    apply Exprs.PtrPairSetFacts.for_all_iff in HA2; cycle 1.
    { solve_compat_bool. }
    apply Exprs.PtrPairSetFacts.for_all_iff in HB2; cycle 1.
    { solve_compat_bool. }
    ii.
    expl HB2 (try eassumption).
    apply orb_true_iff in HB0.
    apply orb_true_iff.
    destruct x0; ss. destruct t, t0; ss.
    des.
    + left.
      eapply diffblock_by_unique_Subset; eauto.
      apply AtomSetFacts.subset_iff. ss.
    + apply Exprs.PtrPairSetFacts.mem_iff in HB0.
      expl HA2. ss.
      des_bool. des.
      * left.
        eapply diffblock_by_unique_Subset; eauto.
        reflexivity.
      * right.
        apply Exprs.PtrPairSetFacts.mem_iff.
        apply Exprs.PtrPairSetFacts.mem_iff in HA0.
        eapply Exprs.PtrPairSetFacts.In_s_m; eauto.
        reflexivity.
  - clear - HA1 HB1 HA3 HB3.
    unfold Invariant.implies_diffblock in *.
    unfold flip in *.
    apply Exprs.ValueTPairSetFacts.for_all_iff.
    { solve_compat_bool. }
    apply Exprs.ValueTPairSetFacts.for_all_iff in HA3; cycle 1.
    { solve_compat_bool. }
    apply Exprs.ValueTPairSetFacts.for_all_iff in HB3; cycle 1.
    { solve_compat_bool. }
    ii.
    destruct x0; ss.
    expl HB3 (try eassumption).
    apply orb_true_iff in HB0.
    des.
    + apply orb_true_iff.
      left.
      eapply diffblock_by_unique_Subset; eauto.
      apply AtomSetFacts.subset_iff; ss.
    + apply Exprs.ValueTPairSetFacts.mem_iff in HB0.
      expl HA3.
  - apply AtomSetFacts.subset_iff; ss.
    apply_all_once AtomSetFacts.subset_iff.
    etransitivity; eauto.
  - apply Exprs.IdTSetFacts.subset_iff.
    apply_all_once Exprs.IdTSetFacts.subset_iff.
    etransitivity; eauto.
Qed.

Global Program Instance PreOrder_implies: PreOrder Invariant.implies.
Next Obligation.
  ii.
  unfold Invariant.implies.
  des_bool. (* TODO enhance des_bool *)
  apply orb_true_iff. right.
  do 2 (try apply andb_true_iff; try split); (* TODO: Can we do better? I want to rewrite at once.. *)
  (* Maybe hard to state in lemma at once. tactic is needed here? *)
    apply wrap_is_true_goal.
  - reflexivity.
  - reflexivity.
  - apply Exprs.IdTSetFacts.subset_iff. reflexivity.
Qed.
Next Obligation.
  ii.
  rename H into HA. rename H0 into HB.
  unfold Invariant.implies in *.
  unfold is_true in *. des_bool.
  destruct HA.
  { apply orb_true_iff. left. ss. }
  destruct HB.
  { apply orb_true_iff. left.
    repeat (des_bool; des).
    clear H2 H1.
    unfold Invariant.implies_unary in *.
    repeat (des_bool; des).
    unfold Invariant.has_false in *.
    rewrite <- ExprPairSetFacts.mem_iff in *.
    unfold Invariant.implies_lessdef in *. unfold flip in *.
    rewrite <- ExprPairSetFacts.for_all_iff in *; cycle 1.
    { solve_compat_bool. }
    expl H.
    rewrite <- ExprPairSetFacts.exists_iff in *; cycle 1.
    { solve_compat_bool. }
    unfold ExprPairSet.Exists in *. des.
    des_sumbool. clarify.
  }
  repeat (des_bool; des).
  apply orb_true_iff. right.
  do 2 (try apply andb_true_iff; try split); (* TODO: Can we do better? I want to rewrite at once.. *)
    apply wrap_is_true_goal.
  - etransitivity; eauto.
  - etransitivity; eauto.
  - apply Exprs.IdTSetFacts.subset_iff.
    apply_all_once Exprs.IdTSetFacts.subset_iff.
    etransitivity; eauto.
Qed.
