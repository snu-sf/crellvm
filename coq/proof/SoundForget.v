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


(* Forget *)

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

Lemma forget_unary_Subset
      defs leaks inv0
  : Invariant.Subset_unary (Forget.unary defs leaks inv0) inv0.
Proof.
  unfold Forget.unary.
  econs; ss; ii.
  - eapply ExprPairSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
  - econs; ii.
    + eapply ValueTPairSetFacts.filter_iff in H; try by solve_compat_bool.
      des. eauto.
    + eapply PtrPairSetFacts.filter_iff in H; try by solve_compat_bool.
      des. eauto.
  - eapply AtomSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
  - eapply IdTSetFacts.filter_iff in H; try by solve_compat_bool.
    des. eauto.
Qed.

Lemma forget_Subset
      def_src def_tgt inv0
      leaks_src leaks_tgt
  : Invariant.Subset (Forget.t def_src def_tgt leaks_src leaks_tgt inv0) inv0.
Proof.
  unfold Forget.t.
  econs; ss;
    try apply forget_unary_Subset.
  ii.
  apply IdTSet.union_3. eauto.
Qed.

(* soundness *)

Definition unique_preserved_except conf inv st1 except_for : Prop :=
  forall u (MEM: AtomSetImpl.mem u inv.(Invariant.unique) = true)
         (NO_LEAK: AtomSetImpl.mem u except_for = false),
    InvState.Unary.sem_unique conf st1 u.

Lemma forget_unary_sound
      conf defs leaks st0 st1
      inv invst invmem
      (EQUIV : state_equiv_except defs st0 st1)
      (UNIQUE : unique_preserved_except conf inv st1 (AtomSetImpl.union defs leaks))
      (STATE : InvState.Unary.sem conf st0 invst invmem inv)
      (WF_LC: memory_props.MemProps.wf_lc st1.(Mem) st1.(EC).(Locals))
  : InvState.Unary.sem conf st1 invst invmem (Forget.unary defs leaks inv).
Proof.
  inv STATE.
  assert (EQUIV_REV: state_equiv_except defs st1 st0).
  { symmetry. eauto. }
  econs; eauto.
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
      rewrite ValueTPairSetFacts.filter_b in MEM; try by solve_compat_bool. des_ifs.
      unfold sflib.is_true in MEM.
      solve_negb_liftpred.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL2; eauto.
    + i. ss.
      rewrite PtrPairSetFacts.filter_b in MEM; try by solve_compat_bool. des_ifs.
      unfold sflib.is_true in MEM.
      solve_negb_liftpred.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact EQUIV_REV; try exact VAL2; eauto.
  - ii. ss.
    apply AtomSetFacts.filter_iff in H; [| solve_compat_bool]. des.
    apply negb_true_iff in H0.

    unfold unique_preserved_except in *.

    apply UNIQUE; eauto.
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
      defs_src defs_tgt
      leaks_src leaks_tgt
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst invmem inv0)
      (EQUIV_SRC: state_equiv_except defs_src st0_src st1_src)
      (EQUIV_TGT: state_equiv_except defs_tgt st0_tgt st1_tgt)
      (UNIQUE_SRC: unique_preserved_except conf_src inv0.(Invariant.src) st1_src (AtomSetImpl.union defs_src leaks_src))
      (UNIQUE_TGT: unique_preserved_except conf_tgt inv0.(Invariant.tgt) st1_tgt (AtomSetImpl.union defs_tgt leaks_tgt))
      (WF_LC_SRC: memory_props.MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_LC_TGT: memory_props.MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))
  : <<STATE_FORGET: InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt
                            invst invmem (Forget.t defs_src defs_tgt leaks_src leaks_tgt inv0)>>.
Proof.
  inv STATE.
  econs; ss.
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

(* unused *)

(* (* ForgetUnique *) *)

(* Lemma forget_unique_sound *)
(*       conf_src st0_src d_src l_src *)
(*       conf_tgt st0_tgt d_tgt l_tgt *)
(*       invst invmem inv0 *)
(*       (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst invmem inv0) *)
(*   : <<STATE_FORGET_UNIQUE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt *)
(*                                             invst invmem (ForgetUnique.t d_src d_tgt l_src l_tgt inv0)>>. *)
(* Proof. *)
(*   red. unfold ForgetUnique.t. *)
(*   inv STATE. *)
(*   econs; eauto; [inv SRC | inv TGT]; *)
(*     econs; eauto; *)
(*     intros x IN; apply UNIQUE; ss; *)
(*     apply AtomSetFacts.filter_iff in IN; try by solve_compat_bool; *)
(*     des; eauto. *)
(* Qed. *)

(* Definition unary_no_leaks defs leaks inv0: Prop := *)
(*   forall x, *)
(*     AtomSetImpl.mem x (AtomSetImpl.union defs leaks) = true -> *)
(*     AtomSetImpl.mem x inv0.(Invariant.unique) = false. *)
(* (* TODO: forall x (LEAKS: mem ...) (UNIQUE: mem ...), False. *) *)

(* Lemma forget_unique_unary_no_leaks defs leaks inv0: *)
(*   unary_no_leaks defs leaks (ForgetUnique.unary defs leaks inv0). *)
(*   (* TODO: unary_no_leaks (AtomSetImpl.union defs leaks) (ForgetUnique.unary defs leaks inv0). *) *)
(* Proof. *)
(*   unfold unary_no_leaks. ii. *)
(*   ss. rewrite AtomSetFacts.filter_b; try by solve_compat_bool. *)
(*   apply andb_false_iff. right. *)
(*   apply negb_false_iff. eauto. *)
(* Qed. *)

(* Lemma unary_no_leaks_Subset *)
(* (* TODO: Lemma unary_no_leaks_mon *) *)
(*       defs leaks inv0 inv1 *)
(*       (SUBSET: Invariant.Subset_unary inv1 inv0) *)
(*       (NO_LEAKS: unary_no_leaks defs leaks inv0) *)
(*   : unary_no_leaks defs leaks inv1. *)
(* Proof. *)
(*   unfold unary_no_leaks in *. *)
(*   i. exploit NO_LEAKS; eauto. i. *)
(*   inv SUBSET. eauto. *)
(*   destruct (AtomSetImpl.mem x (Invariant.unique inv1)) eqn:MEM; ss. *)
(*   apply AtomSetFacts.mem_iff in MEM. *)
(*   apply SUBSET_UNIQUE in MEM. *)
(*   apply AtomSetFacts.mem_iff in MEM. *)
(*   congruence. *)
(* Qed. *)

(* (* TODO: if not needed, delete *) *)

(* Lemma forget_unique_unary_Subset *)
(*       defs leaks inv0 *)
(*   : Invariant.Subset_unary (ForgetUnique.unary defs leaks inv0) inv0. *)
(* Proof. *)
(*   unfold ForgetUnique.unary. *)
(*   econs; ss; ii. *)
(*   - split; ss. *)
(*   - eapply AtomSetFacts.filter_iff in H; try by solve_compat_bool. *)
(*     des. eauto. *)
(* Qed. *)

(* Lemma forget_unique_Subset *)
(*       def_src leaks_src *)
(*       def_tgt leaks_tgt *)
(*       inv0 *)
(*   : Invariant.Subset (ForgetUnique.t def_src def_tgt leaks_src leaks_tgt inv0) inv0. *)
(* Proof. *)
(*   unfold ForgetUnique.t. *)
(*   econs; ss; *)
(*     try apply forget_unique_unary_Subset. *)
(* Qed. *)

