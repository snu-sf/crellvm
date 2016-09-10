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
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require Import SimulationLocal.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.

Ltac solve_compat_bool := repeat red; ii; subst; eauto.

Lemma get_lhs_in_spec
      ld (rhs: Exprs.Expr.t) x
  (LHS: Exprs.ExprPairSet.In x (Hints.Invariant.get_lhs ld rhs)):
  (snd x) = rhs /\ Exprs.ExprPairSet.In x ld.
Proof.
  destruct x. ss.
  unfold Hints.Invariant.get_lhs in *.
  unfold flip in *.
  rewrite Exprs.ExprPairSetFacts.filter_iff in LHS; cycle 1.
  { solve_compat_bool. }
  ss. des.
  apply proj_sumbool_true in LHS0.
  auto.
Qed.

Lemma get_rhs_in_spec
      ld (lhs: Exprs.Expr.t) x
  (RHS: Exprs.ExprPairSet.In x (Hints.Invariant.get_rhs ld lhs)):
  (fst x) = lhs /\ Exprs.ExprPairSet.In x ld.
Proof.
  destruct x. ss.
  unfold Hints.Invariant.get_rhs in *.
  unfold flip in *.
  rewrite Exprs.ExprPairSetFacts.filter_iff in RHS; cycle 1.
  { solve_compat_bool. }
  ss. des.
  apply proj_sumbool_true in RHS0.
  auto.
Qed.

Lemma reduce_maydiff_lessdef_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst invmem inv
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem
                            (reduce_maydiff_lessdef inv)>> /\
  <<MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem>>.
Proof.
  assert(STATE_DUP := STATE).
  inv STATE.
  split; red; try by eauto.
  econs; eauto.
  ii.
  specialize (MAYDIFF id0).

  ss.
  rewrite Exprs.IdTSetFacts.filter_b in NOTIN; cycle 1.
  { repeat red. ii. subst. eauto. }
  rewrite negb_andb in NOTIN.
  rewrite negb_involutive in NOTIN.
  apply orb_true_iff in NOTIN.
  des.
  { try exploit MAYDIFF; eauto. }

  apply Exprs.ExprPairSetFacts.exists_iff in NOTIN; cycle 1.
  { repeat red. ii. subst. eauto. }
  inv NOTIN.
  des.

  apply Exprs.ExprPairSetFacts.exists_iff in H0; cycle 1.
  { repeat red. ii. subst. eauto. }
  inv H0.
  des.

  apply get_lhs_in_spec in H1.
  apply get_rhs_in_spec in H.
  destruct x, x0; des; ss; subst.
  rename id0 into __ID__.

  (* show existance of val_tgt *)
  (* src lessdef x, t0 --> t0's result exists *)
  (* inject_expr t0, t1 --> t1's result exists *)
  (* tgt t1, x --> x's result exists *)
  (* put x's result as val_tgt *)

  (* src lessdef x, t0 --> t0's result exists *)
  inv SRC.
  clear NOALIAS UNIQUE PRIVATE.
  unfold Exprs.ExprPairSet.For_all in *.
  specialize (LESSDEF (Exprs.Expr.value (Exprs.ValueT.id __ID__), t0)).
  apply LESSDEF in H3.
  clear LESSDEF.

  unfold InvState.Unary.sem_lessdef in *. ss.
  exploit H3; eauto. ii; des.

  (* inject_expr t0, t1 --> t1's result exists *)
  exploit InvState.Rel.inject_expr_spec; eauto. (* uses STATE_DUP *) ii; des.

  (* tgt t1, x --> x's result exists *)
  inv TGT.
  clear NOALIAS UNIQUE PRIVATE.
  specialize (LESSDEF (t1, Exprs.Expr.value (Exprs.ValueT.id __ID__))).
  apply LESSDEF in H2.
  clear LESSDEF.

  unfold InvState.Unary.sem_lessdef in *. ss.
  exploit H2; eauto. ii; des.

  esplits; eauto.
  {
    clear VAL0 VAL_TGT VAL2 H2 H3 H0 VAL_SRC MAYDIFF.
    rename val0 into val_a.
    rename val2 into val_b.
    (* val_src >= val_a >= val_tgt >= val_b *)
    exploit GVs.inject_lessdef_compose; eauto. ii; des.
    exploit GVs.lessdef_inject_compose; cycle 1; eauto.
  }
Qed.

Lemma reduce_maydiff_non_physical_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem inv
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem
                              (reduce_maydiff_non_physical inv)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem>>.
Proof.
Admitted.

Lemma reduce_maydiff_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem inv
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem
                              (reduce_maydiff inv)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem>>.
Proof.
  unfold reduce_maydiff.
  exploit reduce_maydiff_lessdef_sound; eauto. i. des.
  exploit reduce_maydiff_non_physical_sound; eauto.
Qed.
