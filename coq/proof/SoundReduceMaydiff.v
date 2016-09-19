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
Require InvMem.
Require InvState.

Set Implicit Arguments.

Lemma get_lhs_in_spec
      ld (rhs: Exprs.Expr.t) x
  (LHS: Exprs.ExprPairSet.In x (Hints.Invariant.get_lhs ld rhs)):
  (snd x) = rhs /\ Exprs.ExprPairSet.In x ld.
Proof.
  unfold Hints.Invariant.get_lhs, flip in *.
  rewrite Exprs.ExprPairSetFacts.filter_iff in LHS; cycle 1.
  { solve_compat_bool. }
  des. des_sumbool. ss.
Qed.

Lemma get_rhs_in_spec
      ld (lhs: Exprs.Expr.t) x
  (RHS: Exprs.ExprPairSet.In x (Hints.Invariant.get_rhs ld lhs)):
  (fst x) = lhs /\ Exprs.ExprPairSet.In x ld.
Proof.
  unfold Hints.Invariant.get_rhs, flip in *.
  rewrite Exprs.ExprPairSetFacts.filter_iff in RHS; cycle 1.
  { solve_compat_bool. }
  des. des_sumbool. ss.
Qed.

Lemma reduce_maydiff_lessdef_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst invmem inv
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem
                            (reduce_maydiff_lessdef inv)>>.
Proof.
  inversion STATE. econs; eauto. ii.
  ss. rewrite Exprs.IdTSetFacts.filter_b in NOTIN; [|solve_compat_bool].
  repeat (des_bool; des); ss; cycle 2.
  { exploit MAYDIFF; eauto. } clear MAYDIFF.
  apply Exprs.ExprPairSetFacts.exists_iff in NOTIN; [|solve_compat_bool].
  red in NOTIN; des.
  apply Exprs.ExprPairSetFacts.exists_iff in NOTIN0; [|solve_compat_bool].
  red in NOTIN0; des.
  apply get_lhs_in_spec in NOTIN0.
  apply get_rhs_in_spec in NOTIN.
  destruct x, x0. ss. des. subst.
  rename id0 into idt.

  (* src lessdef x, t0 --> t0's result exists *)
  inv SRC. clear NOALIAS UNIQUE PRIVATE.
  exploit LESSDEF; eauto; []; ii; des. clear LESSDEF.

  (* inject_expr t0, t1 --> t1's result exists *)
  exploit InvState.Rel.inject_expr_spec; eauto; []; ii; des.

  (* tgt t1, x --> x's result exists *)
  inv TGT. clear NOALIAS UNIQUE PRIVATE.
  exploit LESSDEF; eauto; []; ii; des. clear LESSDEF.

  (* val_src >= val_a >= val_tgt >= val_b *)
  esplits; eauto.
  exploit GVs.inject_lessdef_compose; eauto; []; ii; des.
  exploit GVs.lessdef_inject_compose; try exact x0; eauto.
Qed.

(* TODO
 * preserved: same
 * otherwise: none
 *)

Lemma reduce_maydiff_preserved_sem_idT st_src st_tgt
      invst inv id val_src val_tgt
  (VAL_SRC: InvState.Unary.sem_idT st_src
              (InvState.Unary.filter (reduce_maydiff_preserved inv) (InvState.Rel.src invst)) id =
            Some val_src)
  (VAL_TGT: InvState.Unary.sem_idT st_tgt (InvState.Rel.tgt invst) id = Some val_tgt):
  <<VAL_TGT: InvState.Unary.sem_idT st_tgt
    (InvState.Unary.filter (reduce_maydiff_preserved inv) (InvState.Rel.tgt invst)) id = Some val_tgt>>.
Proof.
  destruct id. rename i0 into id.
  unfold InvState.Unary.sem_idT in *. ss.
  unfold InvState.Unary.sem_tag in *. ss.
  unfold compose in *.
  destruct t; ss.
  - rewrite <- VAL_TGT.
    rewrite lookup_AL_filter_spec in *.
    rewrite lookup_AL_filter_spec in VAL_SRC. (* WHY SHOULD I WRITE IT ONCE AGAIN?? *)
    des_ifs.
  - rewrite <- VAL_TGT.
    rewrite lookup_AL_filter_spec in *.
    rewrite lookup_AL_filter_spec in VAL_SRC. (* WHY SHOULD I WRITE IT ONCE AGAIN?? *)
    des_ifs.
Qed.

Lemma reduce_maydiff_non_physical_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem inv
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem
                              (reduce_maydiff_non_physical inv)>>.
Proof.
  exists (InvState.Rel.filter (reduce_maydiff_preserved inv) invst0). red.
  inv STATE.
  econs; ss; cycle 2.
  - ii. ss.
    rewrite Exprs.IdTSetFacts.filter_b in NOTIN; [|solve_compat_bool].
    des_bool. des.
    + exploit MAYDIFF; eauto.
      { exploit InvState.Unary.filter_subset_idT; eauto. }
      i. des. esplits; eauto.
      eapply reduce_maydiff_preserved_sem_idT; eauto.
    + destruct id0.
      rename t into __t__, i0 into __i__.
      unfold InvState.Unary.sem_idT in VAL_SRC. ss.
      unfold InvState.Unary.sem_tag in VAL_SRC. ss.
      unfold compose in *.
      destruct __t__; inv NOTIN.
      * rewrite lookup_AL_filter_spec in VAL_SRC.
        unfold Exprs.Tag.t in *. rewrite H0 in VAL_SRC. ss.
      * rewrite lookup_AL_filter_spec in VAL_SRC.
        unfold Exprs.Tag.t in *. rewrite H0 in VAL_SRC. ss.
  - apply InvState.Unary.filter_spec; ss. i.
    unfold reduce_maydiff_preserved. apply orb_true_iff. right.
    rewrite find_app.
    match goal with
    | [|- context[match ?g with | Some _ => _ | None => _ end]] =>
      let COND := fresh "COND" in
      destruct g eqn:COND
    end; ss.
    eapply find_none in COND; [|eauto].
    destruct (Exprs.IdT.eq_dec id0 id0); ss.
  - apply InvState.Unary.filter_spec; ss. i.
    unfold reduce_maydiff_preserved. apply orb_true_iff. right.
    rewrite find_app.
    match goal with
    | [|- context[match ?g with | Some _ => _ | None => _ end]] =>
      let COND := fresh "COND" in
      destruct g eqn:COND
    end; ss.
    apply In_eq_find. ss.
Grab Existential Variables.
  { eauto. }
Qed.

Lemma reduce_maydiff_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem inv
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem
                              (reduce_maydiff inv)>>.
Proof.
  unfold reduce_maydiff.
  exploit reduce_maydiff_lessdef_sound; eauto. i. des.
  exploit reduce_maydiff_non_physical_sound; eauto.
Qed.
