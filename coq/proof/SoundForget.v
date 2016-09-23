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

Definition unique_preserved_except conf invst1 inv st1 defs uses : Prop :=
  forall x u gvx gvy
         (IN_X: IdTSet.In x defs)
         (IN_Y: AtomSetImpl.In u inv.(Invariant.unique))
         (NOT_IN_USE: ~ IdTSet.In (Tag.physical, u) uses)
         (VAL_X: InvState.Unary.sem_idT st1 invst1 x = Some gvx)
         (VAL_Y: lookupAL _ st1.(EC).(Locals) u = Some gvy),
    InvState.Unary.sem_diffblock conf gvx gvy.

Lemma forget_unary_sound
      defs uses st0 st1
      conf invst invmem inv0
      (EQUIV: state_equiv_except defs st0 st1)
      (UNIQUE: unique_preserved_except conf invst inv0 st1 defs uses)
      (STATE: InvState.Unary.sem conf st0 invst invmem inv0)
  : <<STATE: InvState.Unary.sem conf st1 invst invmem (Forget.unary defs uses inv0)>>.
Proof.
Admitted.

Lemma forget_sound
      conf_src st_src0
      conf_tgt st_tgt0
      st_src1 st_tgt1
      invst invmem inv0
      s_src s_tgt
      u_src u_tgt
      (EQUIV_SRC: state_equiv_except s_src st_src0 st_src1)
      (EQUIV_TGT: state_equiv_except s_tgt st_tgt0 st_tgt1)
      (UNIQUE_SRC: unique_preserved_except conf_src invst.(InvState.Rel.src) inv0.(Invariant.src) st_src1 s_src u_src)
      (UNIQUE_TGT: unique_preserved_except conf_tgt invst.(InvState.Rel.tgt) inv0.(Invariant.tgt) st_tgt1 s_tgt u_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src0 st_tgt0
                               invst invmem inv0):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src1 st_tgt1
                            invst invmem (Forget.t s_src s_tgt u_src u_tgt inv0)>>.
Proof.
  inv STATE.
  econs.
  - eapply forget_unary_sound; eauto.
  - eapply forget_unary_sound; eauto.
  - i. ss.
    apply IdTSetFacts.not_mem_iff in NOTIN.
    rewrite IdTSetFacts.union_iff in NOTIN.
    apply not_or_and in NOTIN. des.
    rewrite IdTSetFacts.union_iff in NOTIN.
    apply not_or_and in NOTIN. des.
    apply IdTSetFacts.not_mem_iff in NOTIN0.
    ii. apply state_equiv_except_symm in EQUIV_SRC.
    exploit sem_idT_equiv_except; try exact EQUIV_SRC; eauto. i. des.
    exploit MAYDIFF; eauto. i. des.
    exploit sem_idT_equiv_except; try exact EQUIV_TGT; eauto.
Qed.