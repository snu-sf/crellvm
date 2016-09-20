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
Require Import Validator.
Require Import Postcond.
Require Import Exprs.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.
Require Import SoundImplies. (* for preorder GVs.lessdef *)
Require Import Inject. (* for simtac *)

Set Implicit Arguments.


(* TODO: lemma on tag.previous *)

(* TODO: Unify this snapshot_specs *)

(* Definition snapshot_as_previous st invst: Prop := *)
(*   forall x gvx *)
(*          (LOCAL: lookupAL _ st.(EC).(Locals) x = Some gvx), *)
(*     <<PREV: InvState.Unary.sem_idT st invst (Tag.previous, x) = Some gvx>>. *)

(* Definition snapshot_spec2 st invst: Prop := *)
(*   forall x gvx *)
(*          (PREV: InvState.Unary.sem_idT st invst (Tag.previous, x) = Some gvx), *)
(*     <<LOCAL: lookupAL _ st.(EC).(Locals) x = Some gvx>>. *)

Definition snapshot_previous st invst: Prop :=
  forall x,
    <<SNAPSHOT_PREV: InvState.Unary.sem_idT st invst (Tag.previous, x) =
    lookupAL _ st.(EC).(Locals) x>>.

Definition snapshot_ghost invst0 invst1: Prop :=
  <<SNAPSHOT_GHOST: invst0.(InvState.Unary.ghost) = invst1.(InvState.Unary.ghost)>>.

Lemma physical_previous_lessdef_spec
      e1 e2 inv
      (IN: ExprPairSet.In (e1, e2) (Snapshot.physical_previous_lessdef inv))
  :
    exists x,
      <<IN_UNARY: In (Tag.previous, x) (Hints.Invariant.get_idTs_unary inv)>> /\
      (<<EXPR1: e1 = Expr.value (ValueT.id (Tag.previous, x))>> /\
       <<EXPR2: e2 = Expr.value (ValueT.id (Tag.physical, x))>>
                         \/
       <<EXPR1: e2 = Expr.value (ValueT.id (Tag.previous, x))>> /\
       <<EXPR2: e1 = Expr.value (ValueT.id (Tag.physical, x))>>).
Proof.
Admitted.

(* TODO: move tactics to somewhere *)
Ltac solve_set_union :=
  match goal with
  | [H: ExprPairSet.In _ (ExprPairSet.union _ _) |- _] =>
    apply ExprPairSet.union_1 in H; destruct H as [IN|IN]
  end.

Ltac solve_sem_idT :=
  match goal with
  | [H: InvState.Unary.sem_idT _ _ (_, _) = _ |- _] =>
    unfold InvState.Unary.sem_idT in H; ss
  | [_:_ |- InvState.Unary.sem_idT _ _ (_, _) = _] =>
    unfold InvState.Unary.sem_idT; ss
  end.

Ltac solve_in_filter :=
  match goal with
  | [H: ExprPairSet.In _ (ExprPairSet.filter _ _) |- _] =>
    apply ExprPairSetFacts.filter_iff in H; try (ii;subst;ss;fail); destruct H as [IN FILTER]
  end.

Ltac solve_negb_liftpred :=
  match goal with
  | [H: (negb <*> LiftPred.ExprPair _) (_, _) = _ |- _] =>
    unfold compose, LiftPred.ExprPair in H; simtac; ss;
    apply orb_false_iff in H; destruct H as [FILTER1 FILTER2]
  end.

Lemma snapshot_unary_sound
      conf st invst0 invmem inv0
      (STATE: InvState.Unary.sem conf st invst0 invmem inv0)
  :
    exists invst1,
      <<STATE: InvState.Unary.sem conf st invst1 invmem (Snapshot.unary inv0)>> /\
      <<PREV: snapshot_previous st invst1>> /\
      <<GHOST: snapshot_ghost invst0 invst1>>.
Proof.
  exists (InvState.Unary.mk st.(EC).(Locals) invst0.(InvState.Unary.ghost)).
  splits; ss.
  inv STATE.
  econs; ss.
  - intros ep. ii.
    solve_set_union.
    + destruct ep as [e1 e2].
      apply physical_previous_lessdef_spec in IN. des.
      { subst; ss.
        solve_sem_idT.
        esplits; [eauto|reflexivity].
      }
      { subst; ss.
        solve_sem_idT.
        esplits; [eauto|reflexivity].
      }
    + destruct ep as [e1 e2].
      unfold Snapshot.ExprPairSet in IN. ss.
      solve_set_union.
      { solve_in_filter.
        solve_negb_liftpred.
        admit.
      }
      admit.
  - admit.
  - admit.
  - admit.
  (* { clear -NOALIAS. inv NOALIAS. *)
  (*   econs. *)
  (*   - i. *)

  
  (* -  *)
  (* Check (dom st.(EC).(Locals)). *)

  (* esplits. *)
Admitted.

(* TODO: move this *)
Lemma IdTSet_map_aux
      f tx (elems:list IdT.t)
  :
      <<REV: IdTSet.In tx (fold_right (IdTSet.add <*> f) IdTSet.empty (rev elems))
                          <-> IdTSet.In tx (fold_right (IdTSet.add <*> f) IdTSet.empty elems)>>.
Proof.
Admitted.

Lemma IdTSet_map_spec
      f s ty
      (IN: IdTSet.In ty (IdTSet_map f s))
  :
    exists tx, <<IN: IdTSet.In tx s>> /\
                    <<MAP: f tx = ty>>.
Proof.
  unfold IdTSet_map in *.
  rewrite IdTSet.fold_1 in *.
  remember (IdTSet.elements s) as elems.
  assert (INEQ: forall x, In x elems <-> In x (IdTSet.elements s)).
  { subst. eauto. }
  assert (NODUP: NoDup elems).
  { subst. apply push_iter.NoDupA__NoDup.
    apply IdTSet.elements_3w. }
  clear Heqelems.
  rewrite <- fold_left_rev_right in IN.
  assert (REV: forall ty, IdTSet.In ty (fold_right (IdTSet.add <*> f) IdTSet.empty (rev elems))
                          <-> IdTSet.In ty (fold_right (IdTSet.add <*> f) IdTSet.empty elems)).
  { i. apply IdTSet_map_aux. }
  rewrite REV in IN. clear REV.
  revert s ty IN INEQ NODUP.
  induction elems.
  { i. ss. exfalso. eapply IdTSetFacts.empty_iff; eauto. }
  i. ss.
  apply IdTSetFacts.add_iff in IN. des.
  { esplits; eauto.
    apply IdTSet.elements_2.
    specialize (INEQ a). des.
    exploit INEQ; eauto.
    i. apply InA_iff_In; eauto.
  }
  { specialize (IHelems (IdTSet.remove a s)).
    inv NODUP.
    exploit IHelems; eauto.
    { split.
      - i.
        specialize (INEQ x). des.
        exploit INEQ; eauto. i.
        rewrite <- InA_iff_In in *.
        apply IdTSetFacts.elements_iff.
        apply IdTSetFacts.remove_iff.
        split.
        + apply IdTSetFacts.elements_iff. eauto.
        + ii. subst. eauto.
      - i.
        rewrite <- InA_iff_In in H.
        apply IdTSetFacts.elements_iff in H.
        apply IdTSetFacts.remove_iff in H. des.
        apply IdTSet.elements_1 in H.
        rewrite InA_iff_In in H.
        apply INEQ in H. des; done.
    }
    i. des.
    esplits; eauto.
    eapply IdTSet.remove_3; eauto.
  }
Qed.

Lemma IdTSet_map_spec2
      f s tx
      (IN: IdTSet.In tx s)
  :
    <<IN: IdTSet.In (f tx) (IdTSet_map f s)>>.
Proof.
  unfold IdTSet_map.
  rewrite IdTSet.fold_1.
  rewrite <- fold_left_rev_right.
  apply IdTSet_map_aux.
  remember (IdTSet.elements s) as elems.
  assert (INEQ: forall x, In x elems <-> In x (IdTSet.elements s)).
  { subst. eauto. }
  assert (NODUP: NoDup elems).
  { subst. apply push_iter.NoDupA__NoDup.
    apply IdTSet.elements_3w. }
  clear Heqelems.
  
  revert s tx IN INEQ NODUP.
  induction elems.
  - i. ss.
    apply IdTSet.elements_1 in IN.
    apply InA_iff_In in IN.
    exfalso. eapply INEQ. eauto.
  - i. ss.
    specialize (IHelems (IdTSet.remove a s)).
    inv NODUP.
    apply IdTSetFacts.add_iff.
    destruct (IdT.eq_dec a tx).
    { subst. eauto. }
    right.
    exploit IHelems; eauto.
    + apply IdTSetFacts.remove_iff; eauto.
    + split.
      { i.
        rewrite <- InA_iff_In.
        apply IdTSetFacts.elements_iff.
        apply IdTSetFacts.remove_iff.
        split.
        - apply IdTSetFacts.elements_iff.
          rewrite InA_iff_In.
          apply INEQ; eauto.
        - ii. subst. done.
      }
      { i.
        rewrite <- InA_iff_In in H.
        apply IdTSetFacts.elements_iff in H.
        apply IdTSetFacts.remove_iff in H. des.
        apply IdTSetFacts.elements_iff in H.
        rewrite InA_iff_In in H.
        apply INEQ in H. des; done.
      }
Qed.

Lemma snapshot_maydiff_spec1
      md0 x t
      (IN: IdTSet.In (t, x) md0)
      (NOTPREV: t <> Tag.previous)
  :
    <<IN: IdTSet.In (t, x) (Snapshot.IdTSet md0)>>.
Proof.
  unfold Snapshot.IdTSet.
  apply IdTSet.union_2.
  apply IdTSet.filter_3; eauto.
  { ii. subst. ss. }
  destruct t; eauto.
Qed.

Lemma snapshot_maydiff_spec1_inv
      md0 x t
      (NOTIN: IdTSet.mem (t, x) (Snapshot.IdTSet md0) = false)
      (NOTPREV: t <> Tag.previous)
  :
    <<NOTIN: IdTSet.mem (t, x) md0 = false>>.
Proof.
  destruct (IdTSet.mem (t, x) md0) eqn:MEM; eauto.
  apply IdTSet.mem_2 in MEM.
  apply snapshot_maydiff_spec1 in MEM; eauto.
  des. apply IdTSet.mem_1 in MEM. clarify.
Qed.

(* Lemma snapshot_maydiff_spec2 *)
(*       md0 x *)
(*       (IN: IdTSet.In (Tag.previous, x) (Snapshot.IdTSet md0)) *)
(*   : *)
(*     <<IN: IdTSet.In (Tag.physical, x) md0 >>. *)
(* Proof. *)
(*   unfold Snapshot.IdTSet in IN. *)
(*   apply IdTSet.union_1 in IN. des. *)
(*   { apply IdTSetFacts.filter_iff in IN; cycle 1. *)
(*     { ii. subst. ss. } *)
(*     des. ss. *)
(*   } *)
(*   apply IdTSet_map_spec in IN. des. *)
(*   apply IdTSetFacts.filter_iff in IN0; cycle 1. *)
(*   { ii. subst. ss. } *)
(*   des. *)
(*   unfold compose in *. *)
(*   unfold Previousify.IdT in *. *)
(*   destruct tx. *)
(*   destruct t; ss. *)
(*   inv MAP; eauto. *)
(* Qed. *)

(* Lemma snapshot_maydiff_spec2_inv *)
(*       md0 x *)
(*       (NOTIN: ~ IdTSet.mem (Tag.physical, x) md0) *)
(*   : *)
(*     <<NOTIN: ~ IdTSet.mem (Tag.previous, x) (Snapshot.IdTSet md0) >>. *)
(* Proof. *)
(*   destruct (IdTSet.mem (Tag.previous, x) (Snapshot.IdTSet md0)) eqn:MEM; eauto. *)
(*   apply IdTSet.mem_2 in MEM. *)
(*   apply snapshot_maydiff_spec2 in MEM; try done. *)
(*   des. apply IdTSet.mem_1 in MEM. done. *)
(* Qed. *)

Lemma snapshot_maydiff_spec3
      md0 x
      (IN: IdTSet.In (Tag.physical, x) md0)
  :
    <<IN: IdTSet.In (Tag.previous, x) (Snapshot.IdTSet md0)>>.
Proof.
  unfold Snapshot.IdTSet.
  apply IdTSet.union_3.
  replace (Tag.previous, x) with (Previousify.IdT (Tag.physical, x)); eauto.
  apply IdTSet_map_spec2.
  apply IdTSetFacts.filter_iff.
  { ii. subst. ss. }
  split; eauto.
Qed.

Lemma snapshot_maydiff_spec3_inv
      md0 x
      (IN: IdTSet.mem (Tag.previous, x) (Snapshot.IdTSet md0) = false)
  :
    <<IN: IdTSet.mem (Tag.physical, x) md0 = false>>.
Proof.
  destruct (IdTSet.mem (Tag.physical, x) md0) eqn:MEM; eauto.
  apply IdTSet.mem_2 in MEM.
  apply snapshot_maydiff_spec3 in MEM; try done.
  des. apply IdTSet.mem_1 in MEM. clarify.
Qed.

Lemma snapshot_sound
      conf_src conf_tgt st_src st_tgt invst0 invmem inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv0):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem (Snapshot.t inv0)>> /\
    <<PREV_SRC: snapshot_previous st_src invst1.(InvState.Rel.src)>> /\
    <<PREV_TGT: snapshot_previous st_tgt invst1.(InvState.Rel.tgt)>>.
Proof.
  inv STATE.
  apply snapshot_unary_sound in SRC. des.
  apply snapshot_unary_sound in TGT. des.
  exists (InvState.Rel.mk invst1 invst2).
  esplits.
  - econs.
    + ss.
    + ss.
    + ss.
      i.
      destruct id0.
      destruct t.
      { hexploit snapshot_maydiff_spec1_inv; eauto; try done. i. des.
        hexploit MAYDIFF; eauto.
      }
      { hexploit snapshot_maydiff_spec3_inv; eauto. i. des.
        hexploit MAYDIFF; eauto. i.
        ii. ss.
        exploit PREV; eauto. i. des.
        exploit H0.
        { unfold InvState.Unary.sem_idT. ss.
          rewrite <- x. eauto.
        }
        i. des.
        esplits; eauto.
        exploit PREV0; eauto.
        i. des.
        rewrite x0; eauto.
      }
      { hexploit snapshot_maydiff_spec1_inv; eauto; try done. i. des.
        hexploit MAYDIFF; eauto. i.
        unfold snapshot_ghost in *.
        unfold InvState.Rel.sem_inject in *.
        unfold InvState.Unary.sem_idT in *. ss.
        rewrite <- GHOST. rewrite <- GHOST0. eauto.
      }
  - eauto.
  - eauto.
Qed.
