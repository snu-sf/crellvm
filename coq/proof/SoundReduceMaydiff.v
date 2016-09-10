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
      let H2 := fresh H in destruct x eqn:H2; cycle 1; inv H
    end.

Ltac des_bool :=
  repeat
    match goal with
    | [ H: ?x && ?y = true |- _ ] => apply andb_true_iff in H
    | [ H: ?x && ?y = false |- _ ] => apply andb_false_iff in H
    | [ H: ?x || ?y = true |- _ ] => apply orb_true_iff in H
    | [ H: ?x || ?y = false |- _ ] => apply orb_false_iff in H
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
  (* assert(ABC: InvState.Rel.t) by admit. *)
  (* exists ABC. *)
  exists invst0.
  red.
  (* econs; eauto; ss; cycle 2. *)
  econs; eauto.
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
    - des_bool; des.
      destruct id0; ss.
      (* TODO do not explicitly write this *)
      destruct
        (find (fun y : Exprs.IdT.t => Exprs.IdT.eq_dec (t, i0) y)
              (Hints.Invariant.get_idTs_unary
                 (Hints.Invariant.src inv) ++
                 (Hints.Invariant.get_idTs_unary (Hints.Invariant.tgt inv)))) eqn:T;
        inv NOTIN1.
      unfold InvState.Unary.sem_idT in VAL_SRC; ss.
      (* exploit MAYDIFF; eauto. *)
      (* TODO
 Don't select  invst0, rather select subset of it.
 Enforce VAL_SRC to return NONE. exfalso.
       *)
      (* destruct t; inv NOTIN0; ss. *)
      (* { *)
      (*   + (* prev *) *)
      (*     esplits; eauto. *)
      (*     unfold InvState.Unary.sem_idT; ss. *)
      (*     eauto. *)
      (*   + (* ghost *) *)
      (* } *)
      (* { *)
      (*   exfalso. *)
      (*   destruct t; inv NOTIN0; ss. *)
      (*   unfold InvState.Unary.sem_tag in *. *)
      (* } *)
      admit.
  }
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
