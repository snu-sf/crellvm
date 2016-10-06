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
Require Import Hints.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Require Import Inject. (* TODO: for simtac *)

Set Implicit Arguments.

Definition locals_equiv_except (ids:AtomSetImpl.t) (locals0 locals1:GVsMap): Prop :=
  forall id (NOT_MEM: AtomSetImpl.mem id ids = false),
    lookupAL _ locals0 id = lookupAL _ locals1 id.

Inductive state_equiv_except (ids:AtomSetImpl.t) (st0 st1: State): Prop :=
| state_eq_except_intro
    (MEM: st0.(Mem) = st1.(Mem))
    (LOCALS: locals_equiv_except ids st0.(EC).(Locals) st1.(EC).(Locals))
.

Ltac inv_state_equiv_except :=
  repeat match goal with
  | [H: state_equiv_except ?ids ?st0 ?st1 |- _] =>
    inv H; unfold locals_equiv_except in *
  end;
  repeat match goal with
  | [_:_ |- state_equiv_except ?ids ?st0 ?st1] =>
    econs; unfold locals_equiv_except in *
      end.

Program Instance Equivalence_state_equiv_except ids
  : Equivalence (state_equiv_except ids).
Next Obligation.
  ss.
Qed.
Next Obligation.
  ii. inv_state_equiv_except; symmetry; eauto.
Qed.
Next Obligation.
  ii. inv_state_equiv_except; eauto using eq_trans.
Qed.

Lemma sem_idT_equiv_except
      ids st0 st1 invst id gv
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_idT st0 invst (Tag.physical, id) = Some gv)
      (NOTIN: AtomSetImpl.mem id ids = false)
  : <<STATE: InvState.Unary.sem_idT st1 invst (Tag.physical, id) = Some gv>>.
Proof.
  unfold InvState.Unary.sem_idT in *.
  inv EQUIV.
  unfold locals_equiv_except in LOCALS.
  red. rewrite <- STATE.
  symmetry. eapply LOCALS; eauto.
Qed.

Lemma sem_valueT_equiv_except
      ids st0 st1 invst v gv
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_valueT conf st0 invst v = Some gv)
      (NOTIN: (LiftPred.ValueT (flip IdTSet.mem (lift_physical_atoms_idtset ids))) v = false)
  : <<STATE: InvState.Unary.sem_valueT conf st1 invst v = Some gv>>.
Proof.
  unfold flip in NOTIN.
  destruct v; ss. destruct x. destruct t; ss.
  rewrite lift_physical_atoms_idtset_spec1 in *.
  eapply sem_idT_equiv_except; eauto.
Qed.

Lemma sem_list_valueT_equiv_except
      ids st0 st1 invst lsv gvs
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_list_valueT conf st0 invst lsv = Some gvs)
      (NOTIN: existsb (LiftPred.ValueT (flip IdTSet.mem (lift_physical_atoms_idtset ids)) <*> snd) lsv = false)
  : <<STATE: InvState.Unary.sem_list_valueT conf st1 invst lsv = Some gvs>>.
Proof.
  unfold flip in NOTIN.
  revert gvs STATE NOTIN.
  induction lsv; ss.
  i. simtac.
  apply orb_false_iff in NOTIN. des.
  exploit sem_valueT_equiv_except; eauto. i. des.
  des_ifs; exploit IHlsv; eauto; i; des; clarify.
Qed.

Ltac solve_equiv_except_val st0 :=
  (* apply orb_false_iff in FILTER; des; *)
  repeat match goal with
       | [H: _ || LiftPred.ValueT _ _ = false |- _] =>
         apply orb_false_iff in H;des
       | [H: LiftPred.ValueT _ _ || _ = false |- _] =>
         apply orb_false_iff in H;des
       end;
  repeat match goal with
         | [H: InvState.Unary.sem_valueT _ st0 _ _ = Some _ |- _] =>
           eapply sem_valueT_equiv_except in H; eauto; rewrite H
         end.

Lemma sem_expr_equiv_except
      conf invst
      ids st0 st1 e val
      (EQUIV: state_equiv_except ids st0 st1)
      (FILTER: (LiftPred.Expr (flip IdTSet.mem (lift_physical_atoms_idtset ids))) e = false)
      (SEM_EXPR: InvState.Unary.sem_expr conf st0 invst e = Some val)
  : <<SEM_EXPR: InvState.Unary.sem_expr conf st1 invst e = Some val>>.
Proof.
  unfold compose in FILTER.
  destruct e; ss; simtac;
    try (solve_equiv_except_val st0; eauto).
  - erewrite sem_list_valueT_equiv_except; eauto.
  - rewrite COND2. eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
Qed.

Definition unique_preserved_except conf inv st1 defs leaks : Prop :=
  forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true)
         (NO_LEAK: AtomSetImpl.mem u (AtomSetImpl.union defs leaks) = false),
    InvState.Unary.sem_unique conf st1 u.

(* monotonic features of Forget *)
(* useful lemmas for postcond *)
Lemma not_in_maydiff_forget_monotone
      def_src use_src
      def_tgt use_tgt
      inv0 v
      (NOT_MD: Invariant.not_in_maydiff (Forget.t def_src def_tgt use_src use_tgt inv0) v = true)
  : Invariant.not_in_maydiff inv0 v = true.
Proof.
  unfold Invariant.not_in_maydiff in *.
  destruct v; eauto.
  rewrite negb_true_iff in *.
  
  unfold Forget.t in *. ss.
  rewrite IdTSetFacts.union_b in *.
  solve_des_bool. eauto.
Qed.

Lemma inject_value_forget_monotone
      v1 def_src use_src
      v2 def_tgt use_tgt
      inv0
      (INJECT: Invariant.inject_value
                 (Forget.t def_src def_tgt use_src use_tgt inv0) v1 v2)
  : Invariant.inject_value inv0 v1 v2.
Proof.
  unfold Invariant.inject_value in *.
  unfold is_true in *.
  simtac.
  repeat rewrite orb_true_iff in INJECT.
  repeat rewrite orb_true_iff.
  des.
  - left. left. left.
    solve_des_bool.
    apply andb_true_iff; split; eauto using not_in_maydiff_forget_monotone.
  - left. left. right.
    solve_des_bool.
    apply andb_true_iff; split; eauto using not_in_maydiff_forget_monotone.
    rewrite ExprPairSetFacts.filter_b in *; try by solve_compat_bool.
    solve_des_bool. eauto.
  - left. right.
    solve_des_bool.
    apply andb_true_iff; split; eauto using not_in_maydiff_forget_monotone.
    rewrite ExprPairSetFacts.filter_b in *; try by solve_compat_bool.
    solve_des_bool. eauto.
  - right.
    rewrite <- ExprPairSetFacts.exists_iff in *;try by solve_compat_bool.
    unfold ExprPairSet.Exists in *. des.
    apply InvState.get_rhs_in_spec in INJECT. des.
    esplits.
    + eapply ExprPairSetFacts.filter_iff in INJECT1; try by solve_compat_bool. des.
      eapply InvState.get_rhs_in_spec2; eauto.
    + solve_des_bool.
      apply andb_true_iff.
      split.
      * rewrite ExprPairSetFacts.filter_b in *; try by solve_compat_bool.
        solve_des_bool. eauto.
      * unfold Invariant.not_in_maydiff_expr in *.
        apply forallb_forall. i.
        eapply forallb_forall in INJECT2; eauto.
        eapply not_in_maydiff_forget_monotone; eauto.
Qed.

(* soundness *)

Lemma forget_unique_leak_disjoint
      defs leaks inv0
  : AtomSetImpl.disjoint (Invariant.unique (Forget.unary defs leaks inv0)) leaks.
Proof.
  unfold Forget.unary. ss.
  unfold AtomSetImpl.disjoint.
  unfold AtomSetImpl.Equal.
  i.
  rewrite AtomSetFacts.empty_iff.
  split; try done.
  i. apply AtomSetFacts.inter_iff in H. des.
  apply AtomSetFacts.filter_iff in H; [| solve_compat_bool]. des.
  apply negb_true_iff in H1.
  rewrite AtomSetFacts.union_b in H1. solve_des_bool.
  apply AtomSetFacts.mem_iff in H0. clarify.
Qed.

Lemma forget_unary_sound
      defs leaks st0 st1
      conf invst invmem inv0
      (EQUIV: state_equiv_except defs st0 st1)
      (UNIQUE_PRSV: unique_preserved_except conf inv0 st1 defs leaks)
      (STATE: InvState.Unary.sem conf st0 invst invmem inv0)
  : <<STATE: InvState.Unary.sem conf st1 invst invmem (Forget.unary defs leaks inv0)>>.
Proof.
  inv STATE.
  assert (EQUIV_REV: state_equiv_except defs st1 st0).
  { symmetry. eauto. }
  econs.
  - ii.
    destruct x as [e1 e2]. ss.
    apply ExprPairSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    solve_negb_liftpred.
    exploit sem_expr_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto.
    i. des.

    exploit LESSDEF; eauto.
    i. des. ss.
    exploit sem_expr_equiv_except; try exact EQUIV; try exact VAL2; eauto.
  - inv NOALIAS.
    econs.
    + i. ss.
      rewrite ValueTPairSetFacts.filter_b in MEM; [| solve_compat_bool]. des_ifs.
      unfold sflib.is_true in MEM.
      solve_negb_liftpred.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL2; eauto.
    + i. ss.
      rewrite PtrPairSetFacts.filter_b in MEM; [| solve_compat_bool]. des_ifs.
      unfold sflib.is_true in MEM.
      solve_negb_liftpred.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL2; eauto.
  - ii. ss.
    apply AtomSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    apply negb_true_iff in H0.

    unfold unique_preserved_except in *.

    apply UNIQUE_PRSV; eauto.
    apply AtomSetFacts.mem_iff; eauto.
  - ii. ss.
    apply IdTSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    unfold flip, compose in *.
    apply negb_true_iff in H0.

    destruct x as [t x].
    destruct t; try (exploit PRIVATE; eauto; fail).

    exploit sem_idT_equiv_except; eauto.
    { rewrite <- lift_physical_atoms_idtset_spec1. eauto. }
    i. des.
    exploit PRIVATE; eauto.
Qed.

Lemma forget_sound
      conf_src st0_src
      conf_tgt st0_tgt
      st1_src st1_tgt
      invst invmem inv0
      s_src s_tgt
      l_src l_tgt
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst invmem inv0)
      (EQUIV_SRC: state_equiv_except s_src st0_src st1_src)
      (EQUIV_TGT: state_equiv_except s_tgt st0_tgt st1_tgt)
      (UNIQUE_SRC: unique_preserved_except conf_src inv0.(Invariant.src) st1_src s_src l_src)
      (UNIQUE_TGT: unique_preserved_except conf_tgt inv0.(Invariant.tgt) st1_tgt s_tgt l_tgt)
  : <<STATE_FORGET: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt
                            invst invmem (Forget.t s_src s_tgt l_src l_tgt inv0)>>.
Proof.
  inv STATE.
  exploit forget_unary_sound; try exact EQUIV_SRC; eauto. i. des.
  exploit forget_unary_sound; try exact EQUIV_TGT; eauto. i. des.
  esplits; eauto.
  econs.
  - eapply forget_unary_sound; eauto.
  - eapply forget_unary_sound; eauto.
  - i. ss.
    rewrite IdTSetFacts.union_b in NOTIN.
    solve_des_bool.
    destruct id0. destruct t; ss.
    + rewrite lift_physical_atoms_idtset_spec1 in *.
      rewrite AtomSetFacts.union_b in NOTIN.
      solve_des_bool.
      ii. symmetry in EQUIV_SRC.
      exploit sem_idT_equiv_except; try exact EQUIV_SRC; eauto. i. des.
      exploit MAYDIFF; eauto. i. des.
      exploit sem_idT_equiv_except; try exact EQUIV_TGT; eauto.
    + ii. exploit MAYDIFF; eauto.
    + ii. exploit MAYDIFF; eauto.
Qed.
