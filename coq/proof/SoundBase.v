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
      conf_src conf_tgt mem_src mem_tgt
      (RETVAL: lift2_option (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) retval_src retval_tgt)
      (LOCAL: inject_locals inv locals1_src locals1_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (SRC: return_locals TD retval_src id noret ty locals1_src = Some locals2_src):
  exists locals2_tgt,
    <<TGT: return_locals TD retval_tgt id noret ty locals1_tgt = Some locals2_tgt>> /\
    <<LOCAL: inject_locals inv locals2_src locals2_tgt>>.
Proof.
  unfold return_locals in *.
  simtac; try by esplits; eauto.
  inv MEM. clear SRC TGT INJECT.
  exploit genericvalues_inject.simulation__fit_gv; eauto; []; ii; des.
  rewrite x0. esplits; eauto.
  apply updateAddAL_inject_locals; ss.
Qed.

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
  compute in LESSDEF.
  exploit LESSDEF; eauto; []; ii; des.
  inv x. inv x0. inv H4. inv H2. inv H0. inv H.
Qed.

Lemma inject_incr_fully_inject_allocas
      (inv0 inv1 : InvMem.Rel.t)
      (allocas_src allocas_tgt : list mblock)
      (ALLOCAS: fully_inject_allocas inv0 allocas_src allocas_tgt)
      (MEMINJ: memory_sim.MoreMem.inject_incr inv0.(InvMem.Rel.inject) inv1.(InvMem.Rel.inject))
  : fully_inject_allocas inv1 allocas_src allocas_tgt.
Proof.
  unfold fully_inject_allocas in *.
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
  - i. apply MAYDIFF.
    destruct (IdTSet.mem id0 (Hints.Invariant.maydiff inv1)) eqn:MEM1; ss.
    rewrite <- IdTSetFacts.not_mem_iff in *.
    rewrite <- IdTSetFacts.mem_iff in *.
    exploit SUBSET_MAYDIFF; eauto. i. congruence.
  - eauto.
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
  - unfold is_true in *. des_bool; des.
    apply andb_true_iff.
    split; ss.
    + apply Exprs.ExprPairSet.exists_2 in INJECT_EVENT; try by solve_compat_bool.
      inv INJECT_EVENT. des.
      exploit Exprs.ExprPairSet.exists_1; try by solve_compat_bool.
      inv SUBSET. inv SUBSET_SRC.
      exploit SUBSET_LESSDEF; eauto. i.
      econs; eauto.
    + destruct value1; ss. des_bool. apply negb_true_iff.
      apply IdTSetFacts.not_mem_iff.
      apply IdTSetFacts.not_mem_iff in INJECT_EVENT0.
      ii.
      apply INJECT_EVENT0.
      inv SUBSET.
      expl SUBSET_MAYDIFF.
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
      (EQ_FUNC: st0.(EC).(CurFunction) = st1.(EC).(CurFunction))
      (EQ_ALLOCAS: st0.(EC).(Allocas) = st1.(EC).(Allocas))
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
  - rewrite <- EQ_ALLOCAS. ss.
  - rpapply ALLOCAS_VALID.
    + rewrite MEM_EQ. eauto.
    + rewrite EQ_ALLOCAS. eauto.
  - rewrite <- LOCALS_EQ. rewrite <- MEM_EQ. eauto.
  - rewrite <- MEM_EQ. eauto.
  - rewrite <- MEM_EQ. eauto.
  - rewrite <- LOCALS_EQ. eauto.
  - rewrite <- EQ_FUNC. ss.
Qed.

Definition memory_blocks_of (conf: Config) lc ids : list mblock :=
  List.flat_map (fun x =>
                   match lookupAL _ lc x with
                   | Some gv => GV2blocks gv
                   | _ => []
                   end)
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

Lemma lift_unlift_le_unary
      inv0 inv1 mem
      uniqs privs
      (LE: InvMem.Unary.le (InvMem.Unary.lift mem uniqs privs inv0) inv1)
  :
    InvMem.Unary.le inv0 (InvMem.Unary.unlift inv0 inv1)
.
Proof.
  inv LE.
  econs; eauto.
Qed.

(* "InvMem.Rel" is repeated a lot; how about moving this into InvMem? *)
Lemma lift_unlift_le
      inv0 inv1
      mem_src uniqs_src privs_src
      mem_tgt uniqs_tgt privs_tgt
      (NB_LE_SRC: (Mem.nextblock (InvMem.Unary.mem_parent inv0.(InvMem.Rel.src)) <=
                   Mem.nextblock mem_src)%positive)
      (NB_LE_TGT: (Mem.nextblock (InvMem.Unary.mem_parent inv0.(InvMem.Rel.tgt)) <=
                   Mem.nextblock mem_tgt)%positive)
      (* above two can be achieved from InvMem.Unary.sem NEXTBLOCK_PARENT *)
      (LE: InvMem.Rel.le (InvMem.Rel.lift mem_src mem_tgt uniqs_src uniqs_tgt privs_src privs_tgt inv0) inv1)
  : InvMem.Rel.le inv0 (InvMem.Rel.unlift inv0 inv1).
Proof.
  inv LE. ss.
  econs; eauto.
  - eapply lift_unlift_le_unary; eauto.
  - eapply lift_unlift_le_unary; eauto.
  - eapply InvMem.Rel.frozen_shortened; eauto.
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
    + etransitivity.
      { instantiate (1:= mem_src.(Mem.nextblock)). eauto. }
      inv LE_SRC. ss. clarify. Undo 1.
      {
        subst mem_src.
        rewrite NEXTBLOCK_PARENT. reflexivity.
      }
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
    + etransitivity.
      { instantiate (1:= mem_tgt.(Mem.nextblock)). eauto. }
      inv LE_TGT. ss. clarify.
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
    + ii. apply in_app in INB. des.
      * apply filter_In in INB. des.
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
    + reflexivity.
  - inv TGT.
    econs; eauto; ss.
    +  i. apply in_app in IN. des.
       * apply PRIVS_TGT; eauto.
       * exploit PRIVATE_PARENT; eauto.
    + ii. apply in_app in INB. des.
      * apply filter_In in INB. des.
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
    + reflexivity.
Qed.

Lemma positive_lt_plus_one
      y gmax
      (POS1: (y < gmax + 1)%positive)
      (POS2: (gmax < y)%positive)
  :
    False.
Proof.
  replace (gmax + 1)%positive with (Pos.succ gmax)%positive in *; cycle 1.
  { rewrite Pos.add_comm. ss. destruct gmax; ss. }
  rewrite Pos.lt_succ_r in POS1.
  apply Pos.le_lteq in POS1; eauto.
  des.
  + exploit Pos.lt_trans; eauto. ii.
    apply Pos.lt_irrefl in x0; ss.
  + clarify.
    apply Pos.lt_irrefl in POS2; ss.
Qed.

Lemma unique_const_diffblock
      gval1 gval2 conf gmax st i0 cnst
      (UNIQUE: InvState.Unary.sem_unique conf st gmax i0)
      (GLOBALS: genericvalues_inject.wf_globals gmax (Globals conf))
      (VAL1: lookupAL GenericValue (Locals (EC st)) i0 = Some gval1)
      (VAL2: const2GV (CurTargetData conf) (Globals conf) cnst = Some gval2)
      :
  <<DIFFBLOCK: InvState.Unary.sem_diffblock conf gval1 gval2>>
.
Proof.
  red.
  eapply TODOProof.wf_globals_const2GV in VAL2; eauto. des.

  inv UNIQUE. clear LOCALS MEM. clarify.

  {
    generalize dependent gval1.
    induction gval2; i; ss.
    hexploit IHgval2; eauto.
    { des_ifs; ss. des; ss. }
    i.
    des_ifs.
    ii. clarify.
    cbn in H1.
    des.
    - clarify. exploit GLOBALS0; eauto; []; ii; des.
      eapply positive_lt_plus_one; eauto.
    - exploit H; eauto.
  }
Qed.

Lemma valid_ptr_globals_diffblock
  conf gmax val val'
  (GLOBALS : forall b : Values.block, In b (GV2blocks val) -> (gmax < b)%positive)
  (VALID_PTR : memory_props.MemProps.valid_ptrs (gmax + 1)%positive val')
  :
  <<DIFFBLOCK: InvState.Unary.sem_diffblock conf val val' >>
.
Proof.
  ii.
  exploit GLOBALS; eauto; []; intro GMAX; des.
  {
    clarify.
    induction val'; ss.
    exploit IHval'; eauto.
    { des_ifs. des. ss. }
    des_ifs.
    des.
    cbn in *. des.
    - clarify. exfalso. eapply positive_lt_plus_one; eauto.
    - ss.
  }
Qed.

Lemma valid_ptr_globals_diffblock2
  conf gmax val val'
  (GLOBALS : forall b : Values.block, In b (GV2blocks val') -> (gmax < b)%positive)
  (VALID_PTR : memory_props.MemProps.valid_ptrs (gmax + 1)%positive val')
  :
  <<DIFFBLOCK: InvState.Unary.sem_diffblock conf val val' >>
.
Proof.
  ii.
  exploit GLOBALS; eauto; []; intro GMAX; des.
  {
    clarify.
    induction val'; ss.
    destruct a; ss. destruct v; ss; try (by exploit IHval'; eauto).
    des.
    - clarify. eapply positive_lt_plus_one; eauto.
    - ss. exploit IHval'; eauto.
  }
Qed.

Lemma valid_ptr_globals_diffblock_with_blocks
  conf gmax val blocks
  (GLOBALS : forall b : Values.block, In b blocks -> (gmax < b)%positive)
  (VALID_PTR : memory_props.MemProps.valid_ptrs (gmax + 1)%positive val)
  :
  <<DIFFBLOCK: InvMem.gv_diffblock_with_blocks conf val blocks>>
.
Proof.
  ii.
  exploit GLOBALS; eauto; []; intro GMAX; des.
  induction val; ss.
  cbn in *. destruct a; ss. cbn in *.
  unfold compose in *. ss.
  destruct v; ss; try (eapply IHval; eauto; fail).
  des; clarify.
  + rewrite <- Pplus_one_succ_r in VALID_PTR.
    apply Plt_succ_inv in VALID_PTR.
    des.
    * exploit Plt_trans; eauto. ii.
      exploit dom_libs.PositiveSet.MSet.Raw.L.MO.lt_irrefl; eauto.
    * clarify.
      exploit dom_libs.PositiveSet.MSet.Raw.L.MO.lt_irrefl; eauto.
  + eapply IHval; eauto.
Qed.

Lemma const2GV_mc2undefs
      TD gl ty val
      (CONST2GV_UNDEF: const2GV TD gl (const_undef ty) = Some val)
  : exists mcs, flatten_typ TD ty = Some mcs /\ val = mc2undefs mcs.
Proof.
  unfold const2GV, _const2GV, gundef in *. des_ifs.
  esplits; eauto.
Qed.

Lemma mc2undefs_vundef
      mcs val
      (VAL: val = mc2undefs mcs)
  : List.Forall (eq Values.Vundef) (List.map fst val) /\
    List.map snd val = mcs.
Proof.
  split.
  - revert val VAL.
    induction mcs; i; ss.
    { subst. econs. }
    subst. ss.
    econs; eauto.
  - revert val VAL.
    induction mcs; i; ss.
    { subst. eauto. }
    subst. ss.
    exploit IHmcs; eauto.
    i. rewrite x. reflexivity.
Qed.

Lemma const2GV_undef
      TD gl ty val
      (CONST2GV_UNDEF: const2GV TD gl (const_undef ty) = Some val)
  : exists mcs, flatten_typ TD ty = Some mcs /\
                List.Forall (eq Values.Vundef) (List.map fst val) /\
                List.map snd val = mcs.
Proof.
  exploit const2GV_mc2undefs; eauto. i. des.
  exploit mc2undefs_vundef; eauto.
Qed.

Lemma all_undef_lessdef_aux
      gv1 gv2
      (VUNDEFS : Forall (eq Values.Vundef) (List.map fst gv1))
      (CHUNKS : List.map snd gv1 = List.map snd gv2)
  : GVs.lessdef gv1 gv2.
Proof.
  revert gv2 CHUNKS.
  induction gv1; i; ss.
  - destruct gv2; ss. econs.
  - destruct gv2; ss.
    inv CHUNKS. inv VUNDEFS.
    econs.
    { split; eauto.
      rewrite <- H3. eauto. }
    eapply IHgv1; eauto.
Qed.

Lemma fit_gv_chunks_aux
      g1 g2 typ TD
      (FITGV : fit_gv TD typ g1 = Some g2)
  : exists mcs : list AST.memory_chunk,
    flatten_typ TD typ = Some mcs /\ List.map snd g2 = mcs.
Proof.
  exploit genericvalues_props.fit_gv__matches_chunks.
  { symmetry; eauto. }
  intro CHUNKS_MATCH_TYP.
  unfold gv_chunks_match_typ in *. des_ifs.
  esplits; eauto.
  clear -CHUNKS_MATCH_TYP.
  revert dependent l0.
  induction g2; i.
  { inv CHUNKS_MATCH_TYP. eauto. }
  inv CHUNKS_MATCH_TYP.
  unfold vm_matches_typ in *. des. subst. ss.
  exploit IHg2; eauto.
  i. congruence.
Qed.

Lemma vellvm_no_alias_is_diffblock
      conf gv1 gv2
  : MemProps.no_alias gv1 gv2 <->
    InvState.Unary.sem_diffblock conf gv1 gv2.
Proof.
  assert (NOALIAS_BLK_AUX:
            forall gv b,
              MemProps.no_alias_with_blk gv b <->
              ~ In b (GV2blocks gv)).
  { clear.
    induction gv; ss.
    destruct a. i.
    destruct v; ss.
    split.
    - ii. des; eauto.
      rewrite IHgv in *. eauto.
    - i. split.
      + ii. subst. eauto.
      + rewrite IHgv. eauto.
  }
  split; i.
  { unfold InvState.Unary.sem_diffblock.
    revert dependent gv1.
    induction gv2; i; ss.
    destruct a. unfold GV2blocks in *.
    destruct v; eauto.
    ss.
    cut (~ In b (filter_map (val2block <*> fst) gv1) /\
         list_disjoint (filter_map (val2block <*> fst) gv1)
                       (filter_map (val2block <*> fst) gv2)).
    { i. des.
      unfold list_disjoint in *.
      i. ss.
      des; subst; eauto.
      ii. clarify.
    }
    des.
    split; eauto.
    apply NOALIAS_BLK_AUX. eauto.
  }
  { unfold InvState.Unary.sem_diffblock in *.
    revert dependent gv1.
    induction gv2; i; ss.
    destruct a.
    destruct v; eauto.
    split.
    - apply NOALIAS_BLK_AUX.
      ii. unfold list_disjoint in *.
      exploit H; eauto. ss. eauto.
    - apply IHgv2.
      unfold list_disjoint in *.
      i.
      ii; clarify.
      exploit H; eauto. ss. right. eauto.
  }
Qed.

Lemma invmem_free_invmem_unary
      conf_src inv m x lo hi m' TD inv_unary
      (BOUNDS: Mem.bounds m x = (lo, hi))
      (FREE: free TD m (blk2GV TD x) = Some m')
      (PARENT: list_disjoint [x] inv_unary.(InvMem.Unary.private_parent))
      (pub_unary: mblock -> Prop)
      (UNARY: InvMem.Unary.sem conf_src (InvMem.Rel.gmax inv) pub_unary m inv_unary)
  :
    <<INVMEM: InvMem.Unary.sem conf_src (InvMem.Rel.gmax inv) pub_unary m' inv_unary>>
.
Proof.
  inv UNARY.
  assert(NEXTBLOCK_EQ: Mem.nextblock m' = Mem.nextblock m).
  {
    unfold free in *. des_ifs.
    expl Mem.nextblock_free.
  }
  econs; eauto.
  + eapply memory_props.MemProps.free_preserves_wf_Mem; eauto.
  + ii.
    expl PRIVATE_PARENT.
    inv PRIVATE_PARENT0.
    econs; eauto.
    rewrite NEXTBLOCK_EQ in *. ss.
  + ii.
    expl MEM_PARENT.
    rewrite MEM_PARENT0.
    rename b into __b__.
    clear - FREE IN PARENT.
    abstr (InvMem.Unary.private_parent inv_unary) private_parent.
    move mc at top.
    revert_until mc.
    induction mc; ii; ss.
    {
      expl IHmc.
      rewrite IHmc0. clear IHmc0 IHmc.
      assert(Mem.load a m __b__ o = Mem.load a m' __b__ o).
      {
        cbn in *. des_ifs.
        symmetry.
        eapply Mem.load_free; eauto.
        left. ii. clarify.
        exploit PARENT; eauto. left. ss.
      }
      des_ifs.
    }
  + ii.
    expl UNIQUE_PARENT_MEM.
    exploit memory_props.MemProps.free_preserves_mload_inv; eauto.
    Show Existentials. (* It can give some info whether there is Unshelved goals or not *)
    Unshelve. Undo 2.
    (* Just using hexploit/exploit && eauto gives Unshelved goals. *)
    (* It seems when lemma's goal is exactly same with current goal, exploit; eauto approach *)
    (* does not care on premises, just putting all the premises in the unshelved goal. *)
    (* In this case, by using eapply, this problem can be avoided. *)
    eapply memory_props.MemProps.free_preserves_mload_inv; eauto.
  + rewrite NEXTBLOCK in *.
    rewrite NEXTBLOCK_EQ in *. ss.
  + rewrite NEXTBLOCK_EQ in *. ss.
Qed.

Lemma invmem_free_invmem_rel
      conf_src conf_tgt inv
      m0 m1
      (MEM: InvMem.Rel.sem conf_src conf_tgt m0 m1 inv)
      x0 x1 lo hi
      (BOUNDS0: Mem.bounds m0 x0 = (lo, hi))
      (BOUNDS1: Mem.bounds m1 x1 = (lo, hi))
      m0' m1'
      TD
      (FREE0 : free TD m0 (blk2GV TD x0) = Some m0')
      (INJECT: inv.(InvMem.Rel.inject) x0 = Some (x1, 0))
      (FREE1 : free TD m1 (blk2GV TD x1) = Some m1')
      (PARENT_SRC: list_disjoint [x0] inv.(InvMem.Rel.src).(InvMem.Unary.private_parent))
      (PARENT_TGT: list_disjoint [x1] inv.(InvMem.Rel.tgt).(InvMem.Unary.private_parent))
  :
    <<MEM: InvMem.Rel.sem conf_src conf_tgt m0' m1' inv>>
.
Proof.
  inv MEM.
  econs; eauto.
  - clear INJECT INJECT0 WF TGT PARENT_TGT BOUNDS1 FREE1. clear_tac.
    abstr (InvMem.Rel.src inv) inv_unary.
    abstr (InvMem.Rel.public_src (InvMem.Rel.inject inv)) pub_unary.
    eapply invmem_free_invmem_unary; try eassumption.
  - clear INJECT INJECT0 WF SRC PARENT_SRC BOUNDS0 FREE0. clear_tac.
    abstr (InvMem.Rel.tgt inv) inv_unary.
    abstr (InvMem.Rel.public_tgt (InvMem.Rel.inject inv)) pub_unary.
    eapply invmem_free_invmem_unary; try eassumption.
  - cbn in *. des_ifs.
    expl genericvalues_inject.mem_inj__free.
    repeat rewrite Z.add_0_r in *. clarify.
  - cbn in *. des_ifs.
    expl genericvalues_inject.mem_inj__free.
    repeat rewrite Z.add_0_r in *. clarify.
Qed.

Global Program Instance PreOrder_inject_incr: PreOrder memory_sim.MoreMem.inject_incr.
Next Obligation.
  ii.
  expl H.
Qed.


Lemma fully_inject_allocas_cons_inv
      a0 a1 Allocas0 Allocas1 inv
      (ALLOCAS: fully_inject_allocas inv (a0 :: Allocas0) (a1 :: Allocas1))
  :
    <<ALLOCAS: fully_inject_allocas inv Allocas0 Allocas1 /\
               InvMem.Rel.inject inv a0 = Some (a1, 0)>>
.
Proof.
  inv ALLOCAS.
  splits; ss.
Qed.

Lemma fully_inject_allocas_mem_le
      Allocas0 Allocas1 inv inv'
      (MEMLE: InvMem.Rel.le inv inv')
      (ALLOCAS: fully_inject_allocas inv Allocas0 Allocas1)
  :
    <<ALLOCAS: fully_inject_allocas inv' Allocas0 Allocas1>>
.
Proof.
  inv MEMLE.
  eapply list_forall2_imply; eauto.
Qed.

(* Mem.nextblock_free *)
Lemma unchecked_free_nextblock
      m0 b lo hi m1
      (FREE: Mem.unchecked_free m0 b lo hi = m1)
  :
    <<NB: Mem.nextblock m1 = Mem.nextblock m0>>
.
Proof.
  unfold Mem.unchecked_free in *.
  destruct m0; ss. clarify.
Qed.

(* Mem.load_free_2 *)
Lemma load_unchecked_free2
      m0 bf lo hi m1
      (FREE: Mem.unchecked_free m0 bf lo hi = m1)
      mc b ofs v
      (LOAD: Mem.load mc m1 b ofs = Some v)
  :
    <<LOAD: Mem.load mc m0 b ofs = Some v>>
.
Proof.
Admitted.

(* MemProps.free_preserves_mload_aux_inv *)
Lemma unchecked_free_preserves_mload_aux_inv
      m0 bf lo hi m1
      (FREE: Mem.unchecked_free m0 bf lo hi = m1)
      mc b ofs v
      (LOAD: mload_aux m1 mc b ofs = Some v)
  :
    <<LOAD: mload_aux m0 mc b ofs = Some v>>
.
Proof.
Admitted.

(* MemProps.free_preserves_mload_inv: *)
Lemma unchecked_free_preserves_mload_inv
      m0 b lo hi m1
      (FREE: Mem.unchecked_free m0 b lo hi = m1)
      TD gptr ty al v
      (LOAD: mload TD m1 gptr ty al = Some v)
  :
    <<LOAD: mload TD m0 gptr ty al = Some v>>
.
Proof.
  unfold mload in *. des_ifs. clear_tac.
  unfold GV2ptr in *. des_ifs.
  eapply unchecked_free_preserves_mload_aux_inv; eauto.
Qed.

(* MemProps.free_preserves_mload_aux *)
Lemma unchecked_free_preserves_mload_aux
      m0 bf lo hi m1
      (FREE: Mem.unchecked_free m0 bf lo hi = m1)
      b
      (DIFFBLOCK: bf <> b)
      mc ofs gv
      (LOAD: mload_aux m0 mc b ofs = Some gv)
  :
    <<LOAD: mload_aux m1 mc b ofs = Some gv>>
.
Proof.
Admitted.

(* MemProps.free_preserves_mload *)
Lemma unchecked_free_preserves_mload
      m0 b lo hi m1
      (FREE: Mem.unchecked_free m0 b lo hi = m1)
      TD gptr ty al v
      (LOAD: mload TD m0 gptr ty al = Some v)
      (NOALIAS: MemProps.no_alias_with_blk gptr b)
  :
    <<LOAD: mload TD m1 gptr ty al = Some v>>
.
Proof.
  unfold mload in *. des_ifs.
  eapply unchecked_free_preserves_mload_aux; eauto.
  ii. clarify.
  unfold GV2ptr in *. des_ifs. ss. des; ss.
Qed.

(* MemProps.free_preserves_wf_Mem *)
Lemma unchecked_free_preserves_wf_Mem
      m0 maxb TD
      (WF: MemProps.wf_Mem maxb TD m0)
      b lo hi m1
      (FREE: Mem.unchecked_free m0 b lo hi = m1)
  :
    <<WF: MemProps.wf_Mem maxb TD m1>>
.
Proof.
  unfold MemProps.wf_Mem in *. des.
  expl unchecked_free_nextblock.
  splits; ss; cycle 1.
  { rewrite unchecked_free_nextblock0. ss. }
  i.
  exploit WF; eauto.
  { erewrite unchecked_free_preserves_mload_inv; eauto. }
  i; ss.
  unfold MemProps.valid_ptrs in *. des_ifs.
Qed.

(* mem_inj__pfree *)
Lemma mem_inj__psrc_unchecked_free
      mi m_src0 m_tgt0 m_src1 mgb
      (WASABI: wf_sb_mi mgb mi m_src0 m_tgt0)
      (MOREINJ: MoreMem.mem_inj mi m_src0 m_tgt0)
      b lo hi
      (FREE: Mem.unchecked_free m_src0 b lo hi = m_src1)
      (BOUNDS: (lo, hi) = Mem.bounds m_src0 b)
      (PRIV_SRC: mi b = None)
  :
    <<WASABI: wf_sb_mi mgb mi m_src1 m_tgt0>> /\ <<MOREINJ: MoreMem.mem_inj mi m_src1 m_tgt0>>
.
Proof.
Admitted.

(* no matching here *)
Lemma mem_inj__ptgt_unchecked_free
      mi m_src0 m_tgt0 m_tgt1 mgb
      (WASABI: wf_sb_mi mgb mi m_src0 m_tgt0)
      (MOREINJ: MoreMem.mem_inj mi m_src0 m_tgt0)
      b lo hi
      (FREE: Mem.unchecked_free m_tgt0 b lo hi = m_tgt1)
      (BOUNDS: (lo, hi) = Mem.bounds m_tgt0 b)
      (PRIV_TGT: forall b_src delta, mi b_src <> Some (b, delta))
  :
    <<WASABI: wf_sb_mi mgb mi m_src0 m_tgt1>> /\ <<MOREINJ: MoreMem.mem_inj mi m_src0 m_tgt1>>
.
Proof.
Admitted.

Lemma unchecked_free_preserves_sem_unary
      conf_src gmax inv0 m0 pub
      (SEM: InvMem.Unary.sem conf_src gmax pub m0 inv0)
      b lo hi m1
      (FREE: Mem.unchecked_free m0 b lo hi = m1)
      (DISJOINT: list_disjoint [b] (InvMem.Unary.private_parent inv0))
  :
    <<SEM: InvMem.Unary.sem conf_src gmax pub m1 inv0>>
.
Proof.
  econs; ss; eauto; try apply SEM.
  - eapply unchecked_free_preserves_wf_Mem; eauto. apply SEM.
  - inv SEM. clear - PRIVATE_PARENT. i.
    expl PRIVATE_PARENT.
  - inv SEM. clear - MEM_PARENT DISJOINT. i.
    destruct (peq b b0); ss.
    { clarify. exfalso. eapply DISJOINT; eauto. ss. left; ss. }
    expl MEM_PARENT. rewrite MEM_PARENT0. symmetry.
    clear MEM_PARENT0.
    destruct (mload_aux m0 mc b0 o) eqn:T; ss.
    + eapply unchecked_free_preserves_mload_aux; eauto.
    + destruct (mload_aux (Mem.unchecked_free m0 b lo hi) mc b0 o) eqn:T2; ss.
      exfalso.
      expl unchecked_free_preserves_mload_aux_inv. clarify.
  - inv SEM. clear - UNIQUE_PARENT_MEM DISJOINT. i.
    hexploit UNIQUE_PARENT_MEM; eauto.
    eapply unchecked_free_preserves_mload_inv; eauto.
  - inv SEM. clear - NEXTBLOCK.
    clarify.
  - inv SEM. clear - NEXTBLOCK_PARENT.
    clarify.
Qed.

Lemma invmem_free_allocas_invmem_rel
  TD Allocas1 m_tgt0 Allocas0 m_src0 inv m_src1 m_tgt1
  (ALLOCAS_DISJOINT_SRC: list_disjoint Allocas0 (InvMem.Unary.private_parent (InvMem.Rel.src inv)))
  (ALLOCAS_DISJOINT_TGT: list_disjoint Allocas1 (InvMem.Unary.private_parent (InvMem.Rel.tgt inv)))
  (ALLOC_SRC: free_allocas TD m_src0 Allocas0 = Some m_src1)
  (ALLOC_TGT: free_allocas TD m_tgt0 Allocas1 = Some m_tgt1)
  conf_src conf_tgt
  (MEM: InvMem.Rel.sem conf_src conf_tgt m_src0 m_tgt0 inv)
  (INJECT_ALLOCAS: InvState.Rel.inject_allocas inv.(InvMem.Rel.inject) Allocas0 Allocas1)
  :
    <<INVMEM: InvMem.Rel.sem conf_src conf_tgt m_src1 m_tgt1 inv>>
.
(* Note that TD is not used at all *)
(* It can even be different from conf_src/conf_tgt's CurTargetData *)
Proof.
  ginduction INJECT_ALLOCAS; ii; ss.
  - clarify.
  - des_ifs. apply list_disjoint_cons_inv in ALLOCAS_DISJOINT_SRC. des.
    exploit mem_inj__psrc_unchecked_free; eauto; try apply MEM; []; i; des.
    exploit IHINJECT_ALLOCAS; eauto.
    econs; eauto; try apply MEM.
    + eapply unchecked_free_preserves_sem_unary; eauto. apply MEM.
  - des_ifs. apply list_disjoint_cons_inv in ALLOCAS_DISJOINT_TGT. des.
    exploit mem_inj__ptgt_unchecked_free; eauto; try apply MEM; []; i; des.
    exploit IHINJECT_ALLOCAS; eauto.
    econs; eauto; try apply MEM.
    + eapply unchecked_free_preserves_sem_unary; eauto. apply MEM.
  - des_ifs.
    apply list_disjoint_cons_inv in ALLOCAS_DISJOINT_SRC. des.
    apply list_disjoint_cons_inv in ALLOCAS_DISJOINT_TGT. des.
    exploit mem_inj__unchecked_free; [apply MEM|apply MEM|..]; eauto; []; i; des.
    do 2 rewrite Z.add_0_r in *. clarify.
    assert(z = z1 /\ z0 = z2).
    { inv x1. expl mi_bounds. ss. rewrite Heq in *. rewrite Heq0 in *. clarify. } des; clarify.
    exploit IHINJECT_ALLOCAS; eauto.
    econs; eauto; try apply MEM.
    + eapply unchecked_free_preserves_sem_unary; eauto. apply MEM.
    + eapply unchecked_free_preserves_sem_unary; eauto. apply MEM.
Qed.

Lemma mem_le_private_parent
      inv0 inv1
      (MEMLE: InvMem.Rel.le inv0 inv1)
  :
    <<PRIVATE_PARENT_EQ:
    InvMem.Unary.private_parent (InvMem.Rel.src inv0) = InvMem.Unary.private_parent (InvMem.Rel.src inv1)
    /\
    InvMem.Unary.private_parent (InvMem.Rel.tgt inv0) = InvMem.Unary.private_parent (InvMem.Rel.tgt inv1)>>
.
Proof.
  splits; apply MEMLE.
Qed.

Lemma fully_inject_allocas_inject_allocas
      inv0 als_src als_tgt
      (FULLY_INJECT: fully_inject_allocas inv0 als_src als_tgt)
  :
    <<INJECT: InvState.Rel.inject_allocas inv0.(InvMem.Rel.inject) als_src als_tgt>>
.
Proof.
  ginduction FULLY_INJECT; ii; ss.
  - econs; eauto.
  - econs 4; eauto.
Qed.
