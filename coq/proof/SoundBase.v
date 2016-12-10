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
Require Import Decs.
Require Import Exprs.
Require Import Validator.
Require Import GenericValues.
Require Import Inject.
Require InvMem.
Require InvState.

Set Implicit Arguments.


(* TODO: position *)
Definition get_blocks (f:fdef): blocks :=
  let '(fdef_intro _ blocks) := f in
  blocks.

(* TODO: position *)
Lemma lookupBlockViaLabelFromFdef_spec
      fdef l:
  lookupBlockViaLabelFromFdef fdef l =
  lookupAL _ fdef.(get_blocks) l.
Proof. destruct fdef. ss. Qed.

(* TODO: position *)
Definition ite A (c:bool) (a b:A): A :=
  if c then a else b.

(* TODO: position *)
Lemma ite_spec A c (a b:A):
  ite c a b = if c then a else b.
Proof. ss. Qed.

(* TODO: position *)
Opaque ite.

(* TODO: position *)
Lemma lookupAL_ite
      X (l:AssocList X) decision l1 l2 v1 v2
      (V1: lookupAL _ l l1 = Some v1)
      (V2: lookupAL _ l l2 = Some v2):
  lookupAL _ l (ite decision l1 l2) = Some (ite decision v1 v2).
Proof. destruct decision; ss. Qed.

(* TODO: position *)
Definition return_locals
           (TD:TargetData)
           (retval:option GenericValue)
           (id:id) (noret:noret) (ct:typ)
           (lc:GVMap): option GVsMap :=
  match retval, noret with
  | Some retval, false =>
    match (fit_gv TD ct) retval with
    | Some retval' => Some (updateAddAL _ lc id retval')
    | _ => None
    end
  | _, true => Some lc
  | _, _ => None
  end.

Lemma return_locals_inject_locals
      TD id noret ty inv
      retval_src locals1_src locals2_src
      retval_tgt locals1_tgt
      (RETVAL: lift2_option (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) retval_src retval_tgt)
      (LOCAL: inject_locals inv locals1_src locals1_tgt)
      (SRC: return_locals TD retval_src id noret ty locals1_src = Some locals2_src):
  exists locals2_tgt,
    <<TGT: return_locals TD retval_tgt id noret ty locals1_tgt = Some locals2_tgt>> /\
    <<LOCAL: inject_locals inv locals2_src locals2_tgt>>.
Proof.
  unfold return_locals in *.
  simtac; try by esplits; eauto.
  exploit genericvalues_inject.simulation__fit_gv; eauto.
  { admit. (* wf_sb_mi *) }
  i. des. rewrite x0. esplits; eauto.
  apply updateAddAL_inject_locals; ss.
Admitted.

Lemma meminj_eq_inject_locals
      inv0 inv1 locals_src locals_tgt
      (LOCALS: inject_locals inv0 locals_src locals_tgt)
      (MEMINJ: inv0.(InvMem.Rel.inject) = inv1.(InvMem.Rel.inject))
  : inject_locals inv1 locals_src locals_tgt.
Proof.
  unfold inject_locals in *.
  rewrite <- MEMINJ.
  eauto.
Qed.

Lemma returnUpdateLocals_spec
      TD id noret clattrs ty va f args Result lc lc' gl:
  returnUpdateLocals TD (insn_call id noret clattrs ty va f args) Result lc lc' gl =
  match getOperandValue TD Result lc gl with
  | Some retval => return_locals TD (Some retval) id noret ty lc'
  | None => None
  end.
Proof.
  unfold returnUpdateLocals.
  destruct (getOperandValue TD Result lc gl); ss.
Qed.

Lemma exCallUpdateLocals_spec
      TD rt noret rid oResult lc:
  exCallUpdateLocals TD rt noret rid oResult lc =
  return_locals TD oResult rid noret rt lc.
Proof. destruct oResult; ss. Qed.

Lemma has_false_False
      conf_src conf_tgt st_src st_tgt invst invmem inv
      (HAS_FALSE: Hints.Invariant.has_false inv)
      (SEM: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv):
  False.
Proof.
  unfold Hints.Invariant.has_false in *.
  unfold Hints.Invariant.false_encoding in *.
  inv SEM. inv SRC.
  apply Exprs.ExprPairSet.mem_2 in HAS_FALSE.
  specialize (LESSDEF _ HAS_FALSE).
  clear -LESSDEF.
  unfold InvState.Unary.sem_lessdef in *. ss.
  admit.
Admitted.

Lemma inject_incr_inject_allocas
      (inv0 inv1 : InvMem.Rel.t)
      (allocas_src allocas_tgt : list mblock)
      (ALLOCAS: inject_allocas inv0 allocas_src allocas_tgt)
      (MEMINJ: memory_sim.MoreMem.inject_incr inv0.(InvMem.Rel.inject) inv1.(InvMem.Rel.inject))
  : inject_allocas inv1 allocas_src allocas_tgt.
Proof.
  unfold inject_allocas in *.
  eapply list_forall2_imply; eauto.
Qed.

(* inject_event_subset *)

Ltac inject_clarify :=
  repeat
    match goal with
    | [H1: getTypeAllocSize ?TD ?ty = Some ?tsz1,
           H2: getTypeAllocSize ?TD ?ty = Some ?tsz2 |- _] =>
      rewrite H1 in H2; inv H2
    | [H: proj_sumbool ?dec = true |- _] =>
      destruct dec; ss; subst
    | [H1: getOperandValue (CurTargetData ?conf) ?v (Locals (EC ?st)) ?GL = Some ?gv1,
           H2: InvState.Unary.sem_valueT ?conf ?st ?invst (Exprs.ValueT.lift Exprs.Tag.physical ?v) =
               Some ?gv2 |- _] =>
      let Hnew := fresh in
      assert (Hnew: InvState.Unary.sem_valueT conf st invst (Exprs.ValueT.lift Exprs.Tag.physical v) = Some gv1);
      [ destruct v; [ss; unfold Exprs.IdT.lift; unfold InvState.Unary.sem_idT in *; eauto | ss] | ];
      rewrite Hnew in H2; clear Hnew; inv H2
    | [H1: getOperandValue (CurTargetData ?conf) (value_id ?x) (Locals (EC ?st)) ?GL = Some ?gv1 |-
       InvState.Unary.sem_idT ?st ?invst (Exprs.Tag.physical, ?x) = Some ?gv2] =>
      let Hnew := fresh in
      assert (Hnew: InvState.Unary.sem_idT st invst (Exprs.Tag.physical, x) = Some gv1); [ss|];
      apply Hnew; clear Hnew
    end.

Lemma Subset_unary_sem
      conf st
      invst invmem gmax public
      inv0 inv1
      (STATE: InvState.Unary.sem conf st invst invmem gmax public inv1)
      (SUBSET: Hints.Invariant.Subset_unary inv0 inv1)
  : InvState.Unary.sem conf st invst invmem gmax public inv0.
Proof.
  inv STATE. inv SUBSET.
  econs; eauto.
  - ii. exploit LESSDEF; eauto.
  - inv NOALIAS. inv SUBSET_NOALIAS.
    econs.
    + ii. unfold sflib.is_true in *.
      exploit DIFFBLOCK; rewrite <- ValueTPairSetFacts.mem_iff in *; eauto.
    + ii. unfold sflib.is_true in *.
      exploit NOALIAS0; rewrite <- PtrPairSetFacts.mem_iff in *; eauto.
  - ii. exploit UNIQUE; eauto.
  - ii. exploit PRIVATE; eauto.
Qed.

Lemma Subset_sem
      conf_src st_src
      conf_tgt st_tgt
      invst invmem inv0 inv1
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv1)
      (SUBSET: Hints.Invariant.Subset inv0 inv1)
  : InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv0.
Proof.
  inv STATE. inv SUBSET.
  econs; try (eapply Subset_unary_sem; eauto).
  i. apply MAYDIFF.
  destruct (IdTSet.mem id0 (Hints.Invariant.maydiff inv1)) eqn:MEM1; ss.
  rewrite <- IdTSetFacts.not_mem_iff in *.
  rewrite <- IdTSetFacts.mem_iff in *.
  exploit SUBSET_MAYDIFF; eauto. i. congruence.
Qed.

Lemma postcond_cmd_inject_event_Subset cmd_src cmd_tgt inv0 inv1
      (INJECT_EVENT: Postcond.postcond_cmd_inject_event cmd_src cmd_tgt inv0)
      (SUBSET: Hints.Invariant.Subset inv0 inv1)
  :
    <<INJECT_EVENT: Postcond.postcond_cmd_inject_event cmd_src cmd_tgt inv1>>
.
Proof.
  red.
  destruct cmd_src; destruct cmd_tgt; ss;
    try by 
      (unfold is_true in *; repeat (des_bool; des);
       inject_clarify; try rewrite andb_true_r; try (rewrite andb_true_iff; split);
       eapply InvState.Subset.inject_value_Subset; eauto).
  - apply Exprs.ExprPairSet.exists_2 in INJECT_EVENT; try by solve_compat_bool.
    inv INJECT_EVENT. des.
    exploit Exprs.ExprPairSet.exists_1; try by solve_compat_bool.
    inv SUBSET. inv SUBSET_SRC.
    exploit SUBSET_LESSDEF; eauto. i.
    econs; eauto.
  - unfold Hints.Invariant.is_private in *. des_ifs.
    inv SUBSET. inv SUBSET_SRC.
    unfold is_true in *.
    InvState.Subset.conv_mem2In.
    exploit SUBSET_PRIVATE; eauto.
  - unfold is_true in *; repeat (des_bool; des).
    inject_clarify.
    rewrite andb_true_iff; split.
    + eapply InvState.Subset.inject_value_Subset; eauto.
    + eapply TODO.list_forallb2_implies; eauto.
      i. ss.
      repeat match goal with
             | [a: ?t * ?s |- _] => destruct a
             end.
      des_bool; des. clarify. ss.
      eapply InvState.Subset.inject_value_Subset; eauto.
Qed.

(* tactics from yoonseung *)
Ltac solve_match_bool :=
  repeat (let MATCH := fresh "MATCH" in
          match goal with
          | [H:match ?c with _ => _ end = true |- _] =>
            destruct c eqn:MATCH; try done
          | [H:match ?c with _ => _ end = false |- _] =>
            destruct c eqn:MATCH; try done
          | [H:match ?c with | Some _ => _ | None => _ end =
               Some _ |- _] =>
            destruct c eqn:MATCH; try done
          | [H:match ?c with | Some _ => _ | None => _ end =
               None |- _] =>
            destruct c eqn:MATCH; try done
          | [H:if ?c then Some _ else None = Some _ |- _] =>
            destruct c eqn:MATCH; try done
          | [H:if ?c then Some _ else None = None |- _] =>
            destruct c eqn:MATCH; try done
          | [H:if ?c then None else Some _ = Some _ |- _] =>
            destruct c eqn:MATCH; try done
          | [H:if ?c then None else Some _ = None |- _] =>
            destruct c eqn:MATCH; try done
          end).

Ltac solve_des_bool :=
  match goal with
  | [H: _ || _ = false |- _] =>
    apply orb_false_iff in H; des
  | [H: _ || _ = true |- _] =>
    apply orb_true_iff in H; des
  | [H: _ && _ = true |- _] =>
    apply andb_true_iff in H; des
  | [H: _ && _ = false |- _] =>
    apply andb_false_iff in H; des
  end.

Ltac solve_set_union :=
  match goal with
  | [H: Exprs.ExprPairSet.In _ (Exprs.ExprPairSet.union _ _) |- _] =>
    let IN := fresh "IN" in
    apply Exprs.ExprPairSet.union_1 in H; destruct H as [IN|IN]
  | [H: ?is_true (Exprs.ValueTPairSet.mem _ (Exprs.ValueTPairSet.union _ _)) |- _] =>
    unfold is_true in H;
    rewrite Exprs.ValueTPairSetFacts.union_b in H; solve_des_bool
  | [H: ?is_true (Exprs.PtrPairSet.mem _ (Exprs.PtrPairSet.union _ _)) |- _] =>
    unfold is_true in H;
    rewrite Exprs.PtrPairSetFacts.union_b in H; solve_des_bool
  end.

Ltac solve_sem_idT :=
  try match goal with
  | [H: InvState.Unary.sem_idT _ _ (_, _) = _ |- _] =>
    unfold InvState.Unary.sem_idT in *; ss
  | [_:_ |- InvState.Unary.sem_idT _ _ (_, _) = _] =>
    unfold InvState.Unary.sem_idT in *; ss
  end.

Ltac solve_in_filter :=
  match goal with
  | [H: Exprs.ExprPairSet.In _ (Exprs.ExprPairSet.filter _ _) |- _] =>
    let IN := fresh "IN" in
    let FILTER := fresh "FILTER" in
    apply Exprs.ExprPairSetFacts.filter_iff in H; try (ii;subst;ss;fail); destruct H as [IN FILTER]
  end.

Ltac solve_negb_liftpred :=
  match goal with
  | [H: (negb <*> Postcond.LiftPred.ExprPair _) (_, _) = _ |- _] =>
    unfold compose, Postcond.LiftPred.ExprPair in H; simtac; solve_des_bool
  | [H: (negb <*> Postcond.LiftPred.ValueTPair _) (_, _) = _ |- _] =>
    unfold compose, Postcond.LiftPred.ValueTPair in H; simtac; solve_des_bool
  | [H: (negb <*> Postcond.LiftPred.PtrPair _) (_, _) = _ |- _] =>
    unfold compose, Postcond.LiftPred.PtrPair in H; simtac; solve_des_bool
  end.

Ltac solve_sem_valueT :=
  repeat match goal with
         | [v: Exprs.ValueT.t |- _] =>
           match goal with
           | [Hv: InvState.Unary.sem_valueT _ _ _ v = _ |- _] =>
             destruct v
           end
         end;
  ss;
  repeat match goal with
         | [x:Exprs.IdT.t |- _] =>
           let xtag := fresh "xtag" in
           destruct x as [xtag x]; destruct xtag; ss
         end.

(* TODO: position *)
(* spec for AtomSetImpl_from_list *)

Lemma AtomSetImpl_spec_aux x l s
  : x `in` fold_left (flip add) l s <-> In x l \/ x `in` s.
Proof.
  split.
  - revert x s.
    induction l; eauto.
    i. ss.
    exploit IHl; eauto. i.
    unfold flip in *.
    des; eauto.
    rewrite -> AtomSetFacts.add_iff in *. des; eauto.
  - revert x s.
    induction l; i.
    + ss. des; done.
    + ss. des; (exploit IHl; [|eauto]); eauto;
            right; apply AtomSetFacts.add_iff; eauto.
Qed.

Lemma AtomSetImpl_from_list_spec1 x l
  : AtomSetImpl.In x (AtomSetImpl_from_list l) <-> In x l.
Proof.
  assert (EQUIV: In x l <-> In x l \/ x `in` empty).
  { split; eauto.
    i. des; eauto.
    apply AtomSetFacts.empty_iff in H. done.
  }
  rewrite EQUIV.
  apply AtomSetImpl_spec_aux.
Qed.

Lemma AtomSetImpl_from_list_spec2 x l
  : ~ AtomSetImpl.In x (AtomSetImpl_from_list l) <-> ~ In x l.
Proof.
  split; ii; apply AtomSetImpl_from_list_spec1 in H0; done.
Qed.

Lemma AtomSetImpl_singleton_mem_false x y
  : AtomSetImpl.mem x (AtomSetImpl_from_list [y]) = false -> x <> y.
Proof.
  i.
  apply AtomSetFacts.not_mem_iff in H.
  apply AtomSetImpl_from_list_spec2 in H.
  apply elim_not_In_cons in H. eauto.
Qed.


(* specs for equiv_except *)

Lemma sem_idT_eq_locals
      st0 st1 invst0 x
      (LOCALS_EQ : Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_idT st0 invst0 x = InvState.Unary.sem_idT st1 invst0 x.
Proof.
  destruct x as [[] x]; unfold InvState.Unary.sem_idT in *; ss.
  rewrite LOCALS_EQ; eauto.
Qed.

Lemma sem_valueT_eq_locals
      conf st0 st1 invst0 v
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_valueT conf st1 invst0 v = InvState.Unary.sem_valueT conf st0 invst0 v.
Proof.
  destruct v; eauto.
  eapply sem_idT_eq_locals; eauto.
Qed.

Lemma sem_list_valueT_eq_locals
      conf st0 st1 invst0 lsv
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
  : InvState.Unary.sem_list_valueT conf st1 invst0 lsv = InvState.Unary.sem_list_valueT conf st0 invst0 lsv.
Proof.
  induction lsv; ss; i.
  destruct a as [s v].
  exploit sem_valueT_eq_locals; eauto. intro EQ_VAL.
  rewrite EQ_VAL. rewrite IHlsv. eauto.
Qed.

Lemma sem_expr_eq_locals_mem
      conf st0 st1 invst0 e
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
      (MEM_EQ: Mem st0 = Mem st1)
  : InvState.Unary.sem_expr conf st1 invst0 e = InvState.Unary.sem_expr conf st0 invst0 e.
Proof.
  Ltac sem_value_st :=
      let H' := fresh in
      repeat
        match goal with
        | [LOCALS_EQ: Locals (EC ?st0) = Locals (EC ?st1) |-
           context[ InvState.Unary.sem_valueT ?conf ?st1 ?invst0 ?v ] ] =>
          exploit sem_valueT_eq_locals; try exact LOCALS_EQ; intro H';
          rewrite H'; clear H'
        | [LOCALS_EQ: Locals (EC ?st0) = Locals (EC ?st1) |-
           context[ InvState.Unary.sem_list_valueT ?conf ?st1 ?invst0 ?lsv ] ] =>
          exploit sem_list_valueT_eq_locals; try exact LOCALS_EQ; intro H';
          rewrite H'; clear H'
        end.
  destruct e; ss; try rewrite <- MEM_EQ; sem_value_st; eauto.
Qed.

Lemma unary_sem_eq_locals_mem
      conf st0 st1 invst0 invmem0 inv0 gmax public
      (LOCALS_EQ: Locals (EC st0) = Locals (EC st1))
      (MEM_EQ : Mem st0 = Mem st1)
      (STATE: InvState.Unary.sem conf st0 invst0 invmem0 gmax public inv0)
  : InvState.Unary.sem conf st1 invst0 invmem0 gmax public inv0.
Proof.
  inv STATE.
  econs.
  - ii.
    exploit LESSDEF; eauto.
    { erewrite sem_expr_eq_locals_mem; eauto. }
    i. des.
    esplits; eauto.
    erewrite sem_expr_eq_locals_mem; eauto.
  - inv NOALIAS.
    econs; i; [eapply DIFFBLOCK | eapply NOALIAS0];
      try erewrite sem_valueT_eq_locals; eauto.
  - ii. exploit UNIQUE; eauto. intro UNIQ_X. inv UNIQ_X.
    econs; try rewrite <- LOCALS_EQ; try rewrite <- MEM_EQ; eauto.
  - ii. exploit PRIVATE; eauto.
    { erewrite sem_idT_eq_locals; eauto. }
    rewrite <- MEM_EQ. eauto.
  - rewrite <- LOCALS_EQ. rewrite <- MEM_EQ. eauto.
  - rewrite <- MEM_EQ. eauto.
  - rewrite <- MEM_EQ. eauto.
  - rewrite <- LOCALS_EQ. eauto.
Qed.

Definition memory_blocks_of (conf: Config) lc ids : list mblock :=
  List.flat_map (fun x =>
                   match lookupAL _ lc x with
                   | Some gv =>
                     GV2blocks gv
                   | _ => []
                   end
                )
                (AtomSetImpl.elements ids).

Definition memory_blocks_of_t (conf: Config) st invst idts : list mblock :=
  (List.flat_map (fun x =>
                    match InvState.Unary.sem_idT st invst x with
                    | Some gv => GV2blocks gv
                    | _ => []
                    end)
                 (IdTSet.elements idts)).

Definition unique_is_private_unary inv : Prop :=
  forall x (UNIQUE: AtomSetImpl.mem x inv.(Hints.Invariant.unique) = true),
    IdTSet.mem (Tag.physical, x) inv.(Hints.Invariant.private) = true.

Lemma lift_unlift_le
      inv0 inv1
      mem_src uniqs_src privs_src
      mem_tgt uniqs_tgt privs_tgt
      (LE : InvMem.Rel.le (InvMem.Rel.lift mem_src mem_tgt uniqs_src uniqs_tgt privs_src privs_tgt inv0) inv1)
  : InvMem.Rel.le inv0 (InvMem.Rel.unlift inv0 inv1).
Proof.
  inv LE. ss.
  econs; eauto.
  - inv SRC. econs; eauto.
  - inv TGT. econs; eauto.
Qed.

Ltac des_matchH H :=
  repeat
    match goal with
    | [ H' : context[match ?X with _ => _ end] |- _ ] => check_equal H' H; destruct X
    end.

Lemma invmem_unlift
      conf_src mem_src uniqs_src privs_src mem1_src
      conf_tgt mem_tgt uniqs_tgt privs_tgt mem1_tgt
      inv0 inv1
      (MEM_CALLER : InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv0)
      (LIFT : InvMem.Rel.le (InvMem.Rel.lift mem_src mem_tgt uniqs_src uniqs_tgt privs_src privs_tgt inv0) inv1)
      (MEM_CALLEE : InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt inv1)
  : InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt (InvMem.Rel.unlift inv0 inv1).
Proof.
  inv MEM_CALLEE.
  rename SRC into CALLEE_SRC. rename TGT into CALLEE_TGT.
  rename INJECT into CALLEE_INJECT. rename WF into CALLEE_WF.
  inv MEM_CALLER.
  rename SRC into CALLER_SRC. rename TGT into CALLER_TGT.
  rename INJECT into CALLER_INJECT. rename WF into CALLER_WF.
  inv LIFT.
  rename SRC into LE_SRC. rename TGT into LE_TGT.

  econs; eauto; ss.
  - (* src *)
    inv CALLEE_SRC. inv CALLER_SRC.
    econs; eauto; ss.
    + rewrite GMAX. eauto.
    (* + i. apply PRIVATE_PARENT. *)
    (*   inv LE_SRC. *)
    (*   rewrite <- PRIVATE_PARENT_EQ. ss. *)
    (*   apply in_app. left. eauto. *)
    + i. apply PRIVATE_PARENT.
      inv LE_SRC.
      rewrite <- PRIVATE_PARENT_EQ. ss.
      apply in_app. right. eauto.
    + i. exploit MEM_PARENT0; eauto.
      intro MLOAD_EQ. rewrite MLOAD_EQ.
      inv LE_SRC. ss. subst.
      apply MEM_PARENT.
      rewrite <- PRIVATE_PARENT_EQ.
      apply in_app. right. eauto.
    + ii. exploit UNIQUE_PARENT_MEM; eauto.
      des. esplits; eauto.
      inv LE_SRC; ss.
      rewrite <- UNIQUE_PARENT_EQ.
      apply in_app. right. eauto.
  - (* tgt *)
    inv CALLEE_TGT. inv CALLER_TGT.
    econs; eauto; ss.
    + rewrite GMAX. eauto.
    (* + i. apply PRIVATE_PARENT. *)
    (*   inv LE_TGT. *)
    (*   rewrite <- PRIVATE_PARENT_EQ. ss. *)
    (*   apply in_app. left. eauto. *)
    + i. apply PRIVATE_PARENT.
      inv LE_TGT.
      rewrite <- PRIVATE_PARENT_EQ. ss.
      apply in_app. right. eauto.
    + i. exploit MEM_PARENT0; eauto.
      intro MLOAD_EQ. rewrite MLOAD_EQ.
      inv LE_TGT. ss. subst.
      apply MEM_PARENT.
      rewrite <- PRIVATE_PARENT_EQ.
      apply in_app. right. eauto.
    + ii. exploit UNIQUE_PARENT_MEM; eauto.
      des. esplits; eauto.
      inv LE_TGT; ss.
      rewrite <- UNIQUE_PARENT_EQ.
      apply in_app. right. eauto.
  - inv CALLEE_WF.
    econs; eauto.
    rewrite GMAX.
    eauto.
Qed.

Lemma invmem_lift
      conf_src mem_src uniqs_src privs_src
      conf_tgt mem_tgt uniqs_tgt privs_tgt
      inv
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (UNIQS_SRC : forall (mptr : mptr) (typ : typ) (align : align) (val : GenericValue),
                     mload conf_src.(CurTargetData) mem_src mptr typ align = Some val ->
                     InvMem.gv_diffblock_with_blocks conf_src val uniqs_src)
      (UNIQS_GLOBALS_SRC: forall b, In b uniqs_src -> (inv.(InvMem.Rel.gmax) < b)%positive)
      (UNIQS_TGT : forall (mptr : mptr) (typ : typ) (align : align) (val : GenericValue),
                     mload conf_tgt.(CurTargetData) mem_tgt mptr typ align = Some val ->
                     InvMem.gv_diffblock_with_blocks conf_tgt val uniqs_tgt)
      (UNIQS_GLOBALS_TGT: forall b, In b uniqs_tgt -> (inv.(InvMem.Rel.gmax) < b)%positive)
      (PRIVS_SRC: forall b, In b privs_src -> InvMem.private_block mem_src (InvMem.Rel.public_src inv.(InvMem.Rel.inject)) b)
      (PRIVS_TGT: forall b, In b privs_tgt -> InvMem.private_block mem_tgt (InvMem.Rel.public_tgt inv.(InvMem.Rel.inject)) b)
  : InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt
                   (InvMem.Rel.lift mem_src mem_tgt uniqs_src uniqs_tgt privs_src privs_tgt inv).
Proof.
  inv MEM.
  econs; eauto.
  - inv SRC.
    econs; eauto; ss.
    +  i. apply in_app in IN. des.
       * apply PRIVS_SRC; eauto.
       * exploit PRIVATE_PARENT; eauto.
    + ii. destruct H as [b [H0 H]]. apply in_app in H. des.
      * apply filter_In in H. des.
        exploit PRIVS_SRC; eauto. i. des.
        exploit UNIQS_SRC; eauto.
        rewrite existsb_exists in *. des.
        destruct (Values.eq_block b x0); ss.
        subst. eauto.
      * exploit UNIQUE_PARENT_MEM; eauto.
    + inv WF0.
      i. apply in_app in IN_UNIQUE_PARENT. des.
      * apply filter_In in IN_UNIQUE_PARENT. des.
        apply UNIQS_GLOBALS_SRC.
        rewrite existsb_exists in *. des.
        destruct (Values.eq_block b x); ss.
        subst. eauto.
      * exploit UNIQUE_PARENT_GLOBALS; eauto.
    + apply sublist_app; eauto.
      apply filter_sublist.
  - inv TGT.
    econs; eauto; ss.
    +  i. apply in_app in IN. des.
       * apply PRIVS_TGT; eauto.
       * exploit PRIVATE_PARENT; eauto.
    + ii. destruct H as [b [H0 H]]. apply in_app in H. des.
      * apply filter_In in H. des.
        exploit PRIVS_TGT; eauto. i. des.
        exploit UNIQS_TGT; eauto.
        rewrite existsb_exists in *. des.
        destruct (Values.eq_block b x0); ss.
        subst. eauto.
      * exploit UNIQUE_PARENT_MEM; eauto.
    + inv WF0.
      i. apply in_app in IN_UNIQUE_PARENT. des.
      * apply filter_In in IN_UNIQUE_PARENT. des.
        apply UNIQS_GLOBALS_TGT.
        rewrite existsb_exists in *. des.
        destruct (Values.eq_block b x); ss.
        subst. eauto.
      * exploit UNIQUE_PARENT_GLOBALS; eauto.
    + apply sublist_app; eauto.
      apply filter_sublist.
Qed.
