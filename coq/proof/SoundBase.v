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
