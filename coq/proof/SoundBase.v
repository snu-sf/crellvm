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

Lemma return_locals_fully_inject_locals
      TD id noret ty inv
      retval_src locals1_src locals2_src
      retval_tgt locals1_tgt
      conf_src conf_tgt mem_src mem_tgt
      (RETVAL: lift2_option (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) retval_src retval_tgt)
      (LOCAL: fully_inject_locals inv.(InvMem.Rel.inject) locals1_src locals1_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (SRC: return_locals TD retval_src id noret ty locals1_src = Some locals2_src):
  exists locals2_tgt,
    <<TGT: return_locals TD retval_tgt id noret ty locals1_tgt = Some locals2_tgt>> /\
    <<LOCAL: fully_inject_locals inv.(InvMem.Rel.inject) locals2_src locals2_tgt>>
.
Proof.
  unfold return_locals in *.
  destruct noret; ss.
  { assert(locals1_src = locals2_src).
    { des_ifs. }
    clarify. clear SRC.
    esplits; eauto.
    - des_ifs. }
  des_ifs_safe ss. clarify.
  exploit genericvalues_inject.simulation__fit_gv; eauto.
  { apply MEM. }
  intro FIT_GV; des.
  rewrite FIT_GV.
  esplits; eauto.
  eapply fully_inject_locals_update; eauto.
Qed.

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
  eapply MemAux.wf_globals_const2GV in VAL2; eauto. des.

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

Lemma unchecked_free_block:
   forall (m1 : mem) (bf : Values.block) 
     (lo hi : Z) (m2 : mem),
   Mem.unchecked_free m1 bf lo hi = m2 ->
   forall b : Values.block,
   Mem.valid_block m1 b -> Mem.valid_block m2 b.
 Proof. 
   intros. rewrite <- H. assumption. 
 Qed.

(*Mem.bounds_free_3 *)
Lemma bounds_unchecked_free : 
forall (m1 : mem) (bf : Values.block) (lo hi : Z) (m2 : mem), 
  Mem.unchecked_free m1 bf lo hi = m2 -> 
forall b : Values.block,
Mem.bounds m2 b = Mem.bounds m1 b.
Proof. 
  intros. rewrite <- H. simpl. auto. 
Qed.

Lemma load_unchecked_free:  
  forall (m1 : mem) (bf : Values.block) (lo hi : Z) (m2 : mem) (ofs : Z) (b : Values.block) (chunk : AST.memory_chunk),
  m2 = Mem.unchecked_free m1 bf lo hi -> 
   b <> bf  ->
  Mem.load chunk m2 b ofs = Mem.load chunk m1 b ofs.
Proof. 
  intros. 
  Transparent Mem.load.
  unfold Mem.load.
  destruct (Mem.valid_access_dec m2 chunk b ofs Readable). 
  rewrite pred_dec_true. 
  rewrite H. auto.
  rewrite H in v.   
  eapply MoreMem.valid_access_unchecked_free_before; eauto. 
  rewrite pred_dec_false; auto. 
  red; intros; elim n. 
  rewrite H. apply MoreMem.valid_access_diffblock_free_after. auto. 
  auto.
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
  destruct m0;ss. rewrite <- FREE in LOAD. 
  Transparent Mem.load.
  unfold Mem.load. rewrite pred_dec_true.   
  rewrite (Mem.load_result _ _ _ _ _ LOAD ). auto. 
  eapply MoreMem.valid_access_unchecked_free_before. 
  apply Mem.load_valid_access in LOAD. eauto. 
Qed.

Lemma perm_unchecked_free_1
     : forall (m1 : mem) (bf : Values.block)
         (lo hi : Z) (m2 : mem),
       Mem.unchecked_free m1 bf lo hi = m2 ->
       forall (b : Values.block) 
         (ofs : Z) (k : perm_kind)
         (p : permission),
       b <> bf \/ ofs < lo \/ hi <= ofs ->
       Mem.perm m1 b ofs k p ->
       Mem.perm m2 b ofs k p.
Proof. 
  intros. rewrite <- H.  
  unfold Mem.perm, Mem.unchecked_free; simpl. 
  rewrite Maps.PMap.gsspec.
  destruct (peq b bf). subst b. 
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto. auto.
Qed.

Lemma perm_unchecked_free_3 :
  forall (m1 : mem) (bf : Values.block) (lo hi : Z) (m2 : mem),
       Mem.unchecked_free m1 bf lo hi = m2 ->
       forall (b : Values.block) 
         (ofs : Z) (k : perm_kind)
         (p : permission),
       Mem.perm m2 b ofs k p ->
       Mem.perm m1 b ofs k p.
Proof.
  intros until p. rewrite <- H. 
  unfold Mem.perm, Mem.unchecked_free; simpl. 
  rewrite Maps.PMap.gsspec.
  destruct (peq b bf). 
  subst b. 
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto. 
  auto. auto. auto.
Qed.

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
  generalize dependent ofs.  generalize dependent v.  
  induction mc; simpl; auto. 
  intros. simpl in LOAD. guardH FREE.       
  Vellvm.Vellvm.vellvm_tactics.inv_mbind'.  
  symmetry in HeqR0. unguardH FREE. 
  apply IHmc in HeqR0.
  rewrite HeqR0. 
  erewrite load_unchecked_free2; eauto. 
Qed. 

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
  generalize dependent ofs. generalize dependent gv. 
  induction mc; simpl; intros;  auto. 
  guardH FREE.  
  Vellvm.Vellvm.vellvm_tactics.inv_mbind'.  
  unguardH FREE. 
  symmetry in HeqR0. 
  apply IHmc in HeqR0. 
  rewrite HeqR0. 
  erewrite load_unchecked_free; eauto. rewrite <- HeqR. 
  auto. 
Qed.

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

(*MoreMem.free_left_nonmap_inj memory_sim *) 
Lemma unchecked_free_left_nonmap_inj
     : forall (f : MoreMem.meminj) (m1 m2 : Memory.mem) (b : Values.block) 
         (lo hi : Z) (m1' : Memory.mem),
       f b = None -> MoreMem.mem_inj f m1 m2 -> Mem.unchecked_free m1 b lo hi =  m1' -> MoreMem.mem_inj f m1' m2.
Proof.  
  intros. inversion H0. constructor. 
  intros. eapply MoreMem.mi_access; eauto. 
  rewrite <- H1 in H3.  
  eapply MoreMem.valid_access_unchecked_free_before; eauto.  
  intros. rewrite <- H1; simpl. 
  assert (b=b1 /\ lo <= ofs < hi \/ (b<> b1 \/ ofs<lo \/ hi <= ofs))
    by (assert (lo <= ofs < hi \/ ofs<lo \/ hi <= ofs) by omega; tauto). 
  destruct H4. destruct H4. subst b1. 
  Vellvm.Vellvm.vellvm_tactics.uniq_result. 
  apply mi_memval; auto.
  eapply perm_unchecked_free_3; eauto.
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
  split. 
  SCase "wasabi".  
  clear - PRIV_SRC FREE WASABI.
  inversion_clear WASABI. 
  split; eauto with mem. 
  intros. erewrite unchecked_free_nextblock in H; eauto. 
  intros.   
  apply mi_freeblocks. eauto using unchecked_free_block. 
  intros.  
  apply mi_bounds in H. erewrite bounds_unchecked_free; eauto.   

  SCase "moreinj".   
  clear - MOREINJ WASABI FREE PRIV_SRC. 
  guardH FREE. 
  inv WASABI. 
  unguardH FREE.  
  apply  unchecked_free_left_nonmap_inj with m_src0 b lo hi; eauto. 
Qed.

Lemma unchecked_free_right_inj:
      forall (f : Values.meminj) (m1 m2 : mem) (b : Values.block)
         (lo hi : Z) (m2' : mem),
       MoreMem.mem_inj f m1 m2 ->  Mem.unchecked_free m2 b lo hi = m2' ->
       (forall (b' : Values.block) (delta ofs : Z) (k : perm_kind)
          (p : permission),
        f b' = Some (b, delta) -> Mem.perm m1 b' ofs k p ->
        lo <= ofs + delta < hi -> False) ->
       MoreMem.mem_inj f m1 m2'.
Proof. 
  intros. inversion H. constructor. 

  intros. exploit MoreMem.mi_access; eauto. intros [RG AL].
  split; auto. 
  red; intros. eapply perm_unchecked_free_1; eauto. 
  destruct (peq b2 b); auto. subst b. right.
  destruct (zlt ofs0 lo); auto. destruct (zle hi ofs0); auto.
  elimtype False. eapply H1 with (ofs := ofs0 - delta). eauto. 
  apply H3. omega. omega.

  intros. rewrite <- H0; simpl. 
  specialize (mi_memval _ _ _ _ H2 H3).
  assert (b=b2 /\ lo <= ofs+delta < hi \/ (b<>b2 \/ ofs+delta<lo \/ hi <= ofs+delta)).
  {
    assert (lo <= ofs+delta < hi \/ ofs + delta < lo \/ hi <= ofs + delta) by omega.
    destruct (peq b b2); tauto.
  }
  destruct H4. destruct H4. subst b2.
  specialize (H1 _ _ _ _ _ H2 H3). elimtype False; auto.
  auto. 
Qed.

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
 split. 
{
  clear - PRIV_TGT FREE WASABI. 
  inversion_clear WASABI.
  split; eauto with mem.  
  intros. apply Hmap2 in H. 
  eapply unchecked_free_nextblock in FREE. rewrite FREE. auto. 
  intros. apply mi_mappedblocks in H. 
  eapply unchecked_free_block; eauto.  
  intros. apply mi_bounds in H.
  rewrite H. 
  symmetry. 
  erewrite bounds_unchecked_free; eauto. 
}
{
  clear - MOREINJ WASABI FREE PRIV_TGT. 
  guardH FREE. 
  inv WASABI. 
  unguardH FREE.
  eapply unchecked_free_right_inj; eauto. 
  intros. eapply PRIV_TGT. eapply H; eauto.
} 
Qed.

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
