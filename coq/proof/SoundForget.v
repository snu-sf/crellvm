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

Definition locals_equiv_except (ids:IdTSet.t) (locals0 locals1:GVsMap): Prop :=
  forall id (NOT_IN: ~ IdTSet.In (Tag.physical, id) ids),
    lookupAL _ locals0 id = lookupAL _ locals1 id.

Inductive state_equiv_except (ids:IdTSet.t) (st0 st1: State): Prop :=
| state_eq_except_intro
    (MEM: st0.(Mem) = st1.(Mem))
    (LOCALS: locals_equiv_except ids st0.(EC).(Locals) st1.(EC).(Locals))
.

(* TODO: not sure if needed *)
(* Lemma forget_unary_reduce_lessdef *)
(*       s inv0 inv1 ld *)
(*       (FORGET: Forget.unary s inv0 = inv1) *)
(*       (MEM: ExprPairSet.mem ld inv1.(Invariant.lessdef)): *)
(*   <<MEM: ExprPairSet.mem ld inv0.(Invariant.lessdef)>>. *)
(* Proof. *)
(*   (* unfold Forget.unary in *. *) *)
(* Admitted. *)

Lemma state_equiv_except_symm
      ids st0 st1
  :
    state_equiv_except ids st0 st1 -> state_equiv_except ids st1 st0.
Proof.
  i. inv H. econs; eauto.
  unfold locals_equiv_except in *.
  symmetry. eauto.
Qed.

Lemma sem_idT_equiv_except
      ids st0 st1 invst id gv
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_idT st0 invst id = Some gv)
      (NOTIN: ~ IdTSet.In id ids)
  :
    <<STATE: InvState.Unary.sem_idT st1 invst id = Some gv>>.
Proof.
  unfold InvState.Unary.sem_idT in *.
  inv EQUIV.
  unfold locals_equiv_except in LOCALS.
  red. rewrite <- STATE.
  destruct id.
  destruct t; ss.
  symmetry. eapply LOCALS; eauto.
Qed.

Lemma sem_valueT_equiv_except
      ids st0 st1 invst v gv
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_valueT conf st0 invst v = Some gv)
      (NOTIN: (LiftPred.ValueT (flip IdTSet.mem ids)) v = false)
  :
    <<STATE: InvState.Unary.sem_valueT conf st1 invst v = Some gv>>.
Proof.
  unfold flip in NOTIN.
  destruct v; ss.
  eapply sem_idT_equiv_except; eauto.
  apply IdTSetFacts.not_mem_iff; eauto.
Qed.

Lemma sem_list_valueT_equiv_except
      ids st0 st1 invst lsv gvs
      conf
      (EQUIV: state_equiv_except ids st0 st1)
      (STATE: InvState.Unary.sem_list_valueT conf st0 invst lsv = Some gvs)
      (NOTIN: existsb (LiftPred.ValueT (flip IdTSet.mem ids) <*> snd) lsv = false)
  :
    <<STATE: InvState.Unary.sem_list_valueT conf st1 invst lsv = Some gvs>>.
Proof.
  unfold flip in NOTIN.
  revert gvs STATE NOTIN.
  induction lsv; ss.
  i. simtac.
  apply orb_false_iff in NOTIN. des.
  exploit sem_valueT_equiv_except; eauto.
  i.
  des_ifs.
(*   - ss. *)

(*   destruct v; ss. *)
(*   eapply sem_idT_equiv_except; eauto. *)
(*   apply IdTSetFacts.not_mem_iff; eauto. *)
(* Qed. *)
Admitted.

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
      (FILTER: (LiftPred.Expr (flip IdTSet.mem ids)) e = false)
      (SEM_EXPR: InvState.Unary.sem_expr conf st0 invst e = Some val)
  :
    <<SEM_EXPR: InvState.Unary.sem_expr conf st1 invst e = Some val>>.
Proof.
  unfold compose in FILTER.
  destruct e; ss; simtac;
    try (solve_equiv_except_val st0; eauto).
  - admit. (* lsv *)
  - rewrite COND2. eauto.
  - inv EQUIV. rewrite <- MEM. eauto.
Admitted.

Lemma forget_unary_sound
      ids st0 st1
      conf invst invmem inv0
      (EQUIV : state_equiv_except ids st0 st1)
      (STATE : InvState.Unary.sem conf st0 invst invmem inv0)
  :
    <<STATE: InvState.Unary.sem conf st1 invst invmem (Forget.unary ids inv0)>>.
Proof.
  inv STATE.
  econs.
  - ss.
    ii.
    match goal with
    | [H: ExprPairSet.In x (ExprPairSet.filter _ _) |- _] =>
      apply ExprPairSetFacts.filter_iff in H; [| ii; subst; eauto ]; destruct H as [IN FILTER]
    end.
    unfold compose, LiftPred.ExprPair in FILTER.
    rewrite negb_orb in FILTER.
    apply andb_true_iff in FILTER.
    repeat rewrite negb_true_iff in FILTER. des.
    apply state_equiv_except_symm in EQUIV.
    exploit sem_expr_equiv_except; try exact VAL1; eauto.
    i. des.
    specialize (LESSDEF x IN).
    exploit LESSDEF; eauto. i. des.
    apply state_equiv_except_symm in EQUIV.
    exploit sem_expr_equiv_except; try exact VAL2; eauto.
  - ss.
    inv NOALIAS.
    econs.
    + i. ss.
      rewrite ValueTPairSetFacts.filter_b in MEM; [| ii; subst; ss].
      des_ifs.
      unfold compose, LiftPred.ValueTPair in MEM.
      rewrite negb_orb in MEM. des_ifs.
      unfold sflib.is_true in *.
      rewrite negb_true_iff in *. ss.
      apply state_equiv_except_symm in EQUIV.
      exploit sem_valueT_equiv_except; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact VAL2; eauto.
    + i. ss.
      rewrite PtrPairSetFacts.filter_b in MEM; [| ii; subst; ss].
      des_ifs.
      unfold compose, LiftPred.PtrPair in MEM.
      rewrite negb_orb in MEM. des_ifs.
      unfold sflib.is_true in *.
      rewrite negb_true_iff in *. ss.
      apply state_equiv_except_symm in EQUIV.
      unfold LiftPred.Ptr in *.
      exploit sem_valueT_equiv_except; try exact VAL1; eauto. i. des.
      exploit sem_valueT_equiv_except; try exact VAL2; eauto.
  - ii. ss.
    rewrite AtomSetFacts.filter_iff in *; [| ii; subst; ss]. des.
    simtac.
    rewrite <- IdTSetFacts.not_mem_iff in *.
    exploit UNIQUE; eauto. intro SEM0.
    inv SEM0.
    exploit sem_idT_equiv_except; eauto.
    { unfold InvState.Unary.sem_idT. ss. eauto. }
    i. des.
    econs; eauto.
    + (* IdTSet.In (P, x) ids -> *)
      (* lookupAL _ st1.(EC).(Locals) x = Some gv -> *)
      (* InvState.Unary.sem_diffblock conf  *)
      admit. (* need ids diffblock unique *)
    + inv EQUIV.
      rewrite <- MEM0. eauto.
  - ii. ss.
    unfold flip, compose in *.
    rewrite IdTSetFacts.filter_iff in *; [| ii; subst; ss]. des.
    simtac.
    exploit PRIVATE; eauto.
    eapply sem_idT_equiv_except; eauto.
    + apply state_equiv_except_symm; eauto.
    + apply IdTSetFacts.not_mem_iff; eauto.
Admitted.

Lemma forget_sound
      conf_src st_src0
      conf_tgt st_tgt0
      st_src1 st_tgt1
      invst invmem inv0
      s_src s_tgt
      (EQUIV_SRC: state_equiv_except s_src st_src0 st_src1)
      (EQUIV_TGT: state_equiv_except s_tgt st_tgt0 st_tgt1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src0 st_tgt0
                               invst invmem inv0):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src1 st_tgt1
                            invst invmem (Forget.t s_src s_tgt inv0)>>.
Proof.
  inv STATE.
  econs.
  - eapply forget_unary_sound; eauto.
  - eapply forget_unary_sound; eauto.
  - i. ss.
    unfold sflib.is_true in NOTIN.
    apply not_true_is_false in NOTIN.
    apply IdTSetFacts.not_mem_iff in NOTIN.
    rewrite IdTSetFacts.union_iff in NOTIN.
    apply not_or_and in NOTIN. des.
    rewrite IdTSetFacts.union_iff in NOTIN.
    apply not_or_and in NOTIN. des.
    apply IdTSetFacts.not_mem_iff in NOTIN0.
    ii. apply state_equiv_except_symm in EQUIV_SRC.
    exploit sem_idT_equiv_except; try exact EQUIV_SRC; eauto. i. des.
    exploit MAYDIFF; eauto.
    { congruence. }
    i. des.
    exploit sem_idT_equiv_except; try exact EQUIV_TGT; eauto.
Qed.
