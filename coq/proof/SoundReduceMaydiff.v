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

(* TODO rename H2 into H(original name)? *)
Ltac des_is_true :=
  repeat
    match goal with
    | [H: sflib.is_true ?x |- _] =>
      let H2 := fresh H in
      destruct x eqn:H2; cycle 1; inversion H; clear H
    (* Intended not to use inv here, because it contains subst, changing other premises  *)
    end.

Ltac des_bool :=
  repeat
    match goal with
    | [ H: ?x && ?y = true |- _ ] => apply andb_true_iff in H
    | [ H: ?x && ?y = false |- _ ] => apply andb_false_iff in H
    | [ H: ?x || ?y = true |- _ ] => apply orb_true_iff in H
    | [ H: ?x || ?y = false |- _ ] => apply orb_false_iff in H
    | [ H: context[ ?x && false ] |- _ ] => rewrite andb_false_r in H
    | [ H: context[ false && ?x ] |- _ ] => rewrite andb_false_l in H
    | [ H: context[ ?x || true ] |- _ ] => rewrite orb_true_r in H
    | [ H: context[ true || ?x ] |- _ ] => rewrite orb_true_l in H
    | [ H: context[ negb (?x && ?y) ] |- _ ] => rewrite negb_andb in H
    | [ H: context[ negb (?x || ?y) ] |- _ ] => rewrite negb_orb in H
    | [ H: context[ negb (negb ?x) ] |- _ ] => rewrite negb_involutive in H
    end.

Lemma proj_sumbool_false: forall (P Q : Prop) (a : {P} + {Q}),
    proj_sumbool a = false -> Q.
Proof. ii. destruct a; auto. inv H. Qed.

Ltac des_sumbool :=
  repeat
    match goal with
    | [ H: proj_sumbool ?x = true |- _ ] => apply proj_sumbool_true in H
    | [ H: proj_sumbool ?x = false |- _ ] => apply proj_sumbool_false in H
    end.
(* check InvBooleans tactic *)

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
  des_sumbool.
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
  des_sumbool.
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
                            (reduce_maydiff_lessdef inv)>>.
Proof.
  assert(STATE_DUP := STATE).
  inv STATE.
  red.
  econs; eauto.
  ii.
  specialize (MAYDIFF id0).

  ss.
  rewrite Exprs.IdTSetFacts.filter_b in NOTIN; cycle 1.
  { repeat red. ii. subst. eauto. }
  des_is_true.
  des_bool.
  des.
  { try exploit MAYDIFF; eauto. }

  apply Exprs.ExprPairSetFacts.exists_iff in NOTIN0; cycle 1.
  { repeat red. ii. subst. eauto. }
  inv NOTIN0.
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
                              (reduce_maydiff_non_physical inv)>>.
Proof.
  inv STATE.
  unfold reduce_maydiff_non_physical.
  remember (safe_to_remove inv) as safe_to_remove.
  remember (fun k: (Exprs.Tag.t_ * (id * GenericValue)) =>
              safe_to_remove (k.(fst), k.(snd).(fst))) as safe_to_remove_fit_type.
  remember (fun ks => List.map snd (List.filter safe_to_remove_fit_type ks))
    as safe_to_remove_fit_type2.
  exists (InvState.Rel.update_both
            (InvState.Unary.update_both safe_to_remove_fit_type2) invst0).
  red.
  econs; eauto; ss; cycle 2.
  {
    i. ii. (* VAL_SRC (sem_idT) is from ii *) (* sem_inject from MAYDIFF *) ss. des.
    rewrite Exprs.IdTSetFacts.filter_b in NOTIN; cycle 1.
    { solve_compat_bool. }
    des_is_true.
    des_bool.
    des.
    - apply MAYDIFF in NOTIN0.
      unfold InvState.Rel.sem_inject in NOTIN0.
      specialize (NOTIN0 val_src).
      exploit NOTIN0; eauto.
      (* ok because it is subset *)
      admit.
      ii; des.
      esplits; eauto.
      (* ok because it is safe *)
      admit.
    - des_bool; des.
      destruct id0; ss.
      (* TODO do not explicitly write this *)
      rewrite Heqsafe_to_remove in NOTIN0.
      unfold Postcond.safe_to_remove in NOTIN0. ss.
      destruct
        (find (fun y : Exprs.IdT.t => Exprs.IdT.eq_dec (t, i0) y)
              (Hints.Invariant.get_idTs_unary
                 (Hints.Invariant.src inv) ++
                 (Hints.Invariant.get_idTs_unary (Hints.Invariant.tgt inv)))) eqn:T;
        inversion NOTIN0; clear NOTIN0; des_bool; try by inv H0.
      des.
      rename t into __t__.
      rename i0 into __i__.
      exfalso.
      clear H1 MAYDIFF TGT SRC MEM CONF invmem.
      subst. ss.
      unfold safe_to_remove in VAL_SRC.
      unfold InvState.Unary.sem_idT in VAL_SRC. ss.
      unfold InvState.Unary.sem_tag in VAL_SRC. ss.
      destruct invst0; ss.
      destruct src, tgt; ss.
      destruct __t__; inv H0.
      + induction previous; ss; try by inv VAL_SRC.
        apply IHprevious. clear IHprevious.
        destruct a as [aid atag].
        destruct (eq_dec __i__ aid); ss.
        * subst.
          (* rewrite T in VAL_SRC. *)
          (* IDK why this does not work. I checked with Set Printing All. *)
          replace (find (fun y : Exprs.IdT.t => Exprs.IdT.eq_dec (Exprs.Tag.previous, aid) y)
                      (Hints.Invariant.get_idTs_unary (Hints.Invariant.src inv) ++
                       Hints.Invariant.get_idTs_unary (Hints.Invariant.tgt inv))) with
          (@None Exprs.IdT.t) in VAL_SRC.
          ss.
        * destruct (find (fun y : Exprs.IdT.t => Exprs.IdT.eq_dec (Exprs.Tag.previous, aid) y)
                      (Hints.Invariant.get_idTs_unary (Hints.Invariant.src inv) ++
                       Hints.Invariant.get_idTs_unary (Hints.Invariant.tgt inv))) eqn:T2; ss.
          (* TODO automatize this *)
          (* Set Printing All. idtac. *)
          destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) __i__ aid).
          { subst. unfold not in n. exfalso; apply n; auto. }
          clear n0 n.
          apply VAL_SRC.
      (* COPIED FROM ABOVE. EXACTLY SAME PROOF *)
      + induction ghost; ss; try by inv VAL_SRC.
        apply IHghost. clear IHghost.
        destruct a as [aid atag].
        destruct (eq_dec __i__ aid); ss.
        * subst.
          (* rewrite T in VAL_SRC. *)
          (* IDK why this does not work. I checked with Set Printing All. *)
          replace (find (fun y : Exprs.IdT.t => Exprs.IdT.eq_dec (Exprs.Tag.ghost, aid) y)
                      (Hints.Invariant.get_idTs_unary (Hints.Invariant.src inv) ++
                       Hints.Invariant.get_idTs_unary (Hints.Invariant.tgt inv))) with
          (@None Exprs.IdT.t) in VAL_SRC.
          ss.
        * destruct (find (fun y : Exprs.IdT.t => Exprs.IdT.eq_dec (Exprs.Tag.ghost, aid) y)
                      (Hints.Invariant.get_idTs_unary (Hints.Invariant.src inv) ++
                       Hints.Invariant.get_idTs_unary (Hints.Invariant.tgt inv))) eqn:T2; ss.
          (* TODO automatize this *)
          (* Set Printing All. idtac. *)
          destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) __i__ aid).
          { subst. unfold not in n. exfalso; apply n; auto. }
          clear n0 n.
          apply VAL_SRC.
  }
  - inv SRC.
    econs; eauto.
    + clear NOALIAS UNIQUE PRIVATE.
      unfold Exprs.ExprPairSet.For_all in *.
      i.
      specialize (LESSDEF x H).
      (* if x survived safe_to_remove, ok. *)
      (* if it didn't, x must not appear in SRC/TGT, contradiction to LESSDEF *)
      admit.
    + admit.
    + admit.
    + admit.
  - admit.
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
                              (reduce_maydiff inv)>>.
Proof.
  unfold reduce_maydiff.
  exploit reduce_maydiff_lessdef_sound; eauto. i. des.
  exploit reduce_maydiff_non_physical_sound; eauto.
Qed.
