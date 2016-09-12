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
    | [ H: negb ?x = true |- _ ] => apply negb_true_iff in H
    | [ H: negb ?x = false |- _ ] => apply negb_false_iff in H
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
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem
                            (reduce_maydiff_lessdef inv)>>.
Proof.
  inversion STATE. econs; eauto. ii.
  specialize (MAYDIFF id0). ss.
  rewrite Exprs.IdTSetFacts.filter_b in NOTIN; cycle 1.
  { repeat red. ii. subst. eauto. }
  des_is_true. des_bool. des; [by eapply MAYDIFF; eauto|].
  des_bool.
  apply Exprs.ExprPairSetFacts.exists_iff in NOTIN; cycle 1.
  { repeat red. ii. subst. eauto. }
  inv NOTIN. des.
  apply Exprs.ExprPairSetFacts.exists_iff in H0; cycle 1.
  { repeat red. ii. subst. eauto. }
  inv H0. des.
  apply get_lhs_in_spec in H1.
  apply get_rhs_in_spec in H.
  destruct x, x0. ss. des. subst.
  rename id0 into __ID__.

  (* src lessdef x, t0 --> t0's result exists *)
  inv SRC. clear NOALIAS UNIQUE PRIVATE.
  unfold Exprs.ExprPairSet.For_all in *.
  specialize (LESSDEF (Exprs.Expr.value (Exprs.ValueT.id __ID__), t0)).
  apply LESSDEF in H3. clear LESSDEF.
  exploit H3; eauto. i. des.

  (* inject_expr t0, t1 --> t1's result exists *)
  exploit InvState.Rel.inject_expr_spec; eauto. i. des.

  (* tgt t1, x --> x's result exists *)
  inv TGT. clear NOALIAS UNIQUE PRIVATE.
  specialize (LESSDEF (t1, Exprs.Expr.value (Exprs.ValueT.id __ID__))).
  apply LESSDEF in H2. clear LESSDEF.
  exploit H2; eauto. i. des.

  (* val_src >= val_a >= val_tgt >= val_b *)
  esplits; eauto.
  clear VAL0 VAL_TGT VAL2 H2 H3 H0 VAL_SRC MAYDIFF.
  rename val0 into val_a.
  rename val2 into val_b.
  exploit GVs.inject_lessdef_compose; eauto. i. des.
  exploit GVs.lessdef_inject_compose; cycle 1; eauto.
Qed.

Definition reduce_maydiff_preserved_fit_type inv ks :=
  List.map snd (List.filter (fun k: (Exprs.Tag.t_ * (id * GenericValue)) =>
     reduce_maydiff_preserved inv (k.(fst), k.(snd).(fst))) ks).

Lemma reduce_maydiff_preserved_fit_type_spec1
      inv conf_src conf_tgt invst0 invmem st_src st_tgt
      (SRC: InvState.Unary.sem conf_src st_src (InvState.Rel.src invst0)
                                (InvMem.Rel.src invmem) (Hints.Invariant.src inv))
      (TGT: InvState.Unary.sem conf_tgt st_tgt (InvState.Rel.tgt invst0)
                               (InvMem.Rel.tgt invmem) (Hints.Invariant.tgt inv)):
  InvState.Unary.sem conf_src st_src
                     (InvState.Unary.update_both (reduce_maydiff_preserved_fit_type inv) (InvState.Rel.src invst0))
                     (InvMem.Rel.src invmem) (Hints.Invariant.src inv) /\
  InvState.Unary.sem conf_tgt st_tgt
                     (InvState.Unary.update_both (reduce_maydiff_preserved_fit_type inv) (InvState.Rel.src invst0))
                     (InvMem.Rel.tgt invmem) (Hints.Invariant.tgt inv).
Proof.
  (* SPEC: an element satisfies reduce_maydiff_preserved condition -> ~ B-2 {for LESSDEF, NOALIAS ..) *)
  splits.
  - inv SRC. econs; eauto.
    + clear - LESSDEF TGT.
      unfold Exprs.ExprPairSet.For_all in *. i.
      (* B-2: Exprs.ExprPairSet.In x (Hints.Invariant.lessdef (Hints.Invariant.src inv)) *)
      specialize (LESSDEF x H).
      unfold InvState.Unary.sem_lessdef in *.
      (* A: if x survived reduce_maydiff_preserved, ok. *)
      (* B: if it didn't, B-1: x must not appear in SRC/TGT, B-2: contradiction to LESSDEF *)
      admit.
    + clear - NOALIAS TGT. inv NOALIAS. econs; i.
      (* B-2: MEM *)
      * admit.
      (* A: use VAL1 / VAL2, eapply DIFFBLOCK *)
      * admit.
    (* A: use VAL1 / VAL2, eapply NOALIAS0 *)
    + clear - UNIQUE TGT. ii.
      (* Set Printing All. idtac. *)
      (* B-2: H *)
      specialize (UNIQUE x H).
      admit.
    + clear - PRIVATE TGT.
      unfold Exprs.IdTSet.For_all. i.
      specialize (PRIVATE x H).
      (* B-2: H *)
      admit.
  - admit.
Admitted.

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
  exists (InvState.Rel.update_both
       (InvState.Unary.update_both (reduce_maydiff_preserved_fit_type inv)) invst0).
  red.
  econs; eauto; ss; cycle 2.
  { ii. (* VAL_SRC (sem_idT) is from ii *) (* sem_inject from MAYDIFF *) ss.
    rewrite Exprs.IdTSetFacts.filter_b in NOTIN; cycle 1.
    { solve_compat_bool. }
    des_is_true. des_bool. des.
    - apply MAYDIFF in NOTIN.
      unfold InvState.Rel.sem_inject in NOTIN.
      exploit (NOTIN val_src); eauto.
      { (* ok because it is subset *)
        admit.
      }
      i. des.
      esplits; eauto.
      (* ok because it is safe *)
      admit.
    - destruct id0.
      (* TODO do not explicitly write this *)
      unfold Postcond.reduce_maydiff_preserved in NOTIN. ss.
      des_bool. des.
      match goal with
      | [H: bool_of_option ?o = false |- _] => destruct o eqn:T
      end; inv NOTIN0.
      rename t into __t__, i0 into __i__.
      exfalso. clear MAYDIFF TGT SRC MEM CONF invmem.
      unfold InvState.Unary.sem_idT in VAL_SRC. ss.
      unfold InvState.Unary.sem_tag in VAL_SRC. ss.
      destruct invst0. ss.
      destruct src, tgt. ss.
      destruct __t__; inv NOTIN.
      + induction previous; ss; try by inv VAL_SRC.
        apply IHprevious. clear IHprevious.
        destruct a as [aid atag].
        unfold reduce_maydiff_preserved_fit_type, reduce_maydiff_preserved in *. ss.
        destruct (eq_dec __i__ aid); ss.
        * subst.
          unfold Exprs.Tag.t in *. rewrite T in VAL_SRC. ss.
        * match goal with
          | [H: context[bool_of_option ?o] |- _] => destruct o eqn:T2; ss
          end.
          unfold id in *. destruct (__i__ == aid); ss.
      + (* COPIED FROM ABOVE. EXACTLY SAME PROOF *)
        (* NOTE(jeehoon.kang): if you want to avoid this duplication, you can change some definitions.  *)
        induction ghost; ss; try by inv VAL_SRC.
        apply IHghost. clear IHghost.
        destruct a as [aid atag].
        unfold reduce_maydiff_preserved_fit_type, reduce_maydiff_preserved in *. ss.
        destruct (eq_dec __i__ aid); ss.
        * subst.
          unfold Exprs.Tag.t in *. rewrite T in VAL_SRC. ss.
        * match goal with
          | [H: context[bool_of_option ?o] |- _] => destruct o eqn:T2; ss
          end.
          unfold id in *. destruct (__i__ == aid); ss.
  }
  - exploit reduce_maydiff_preserved_fit_type_spec1; eauto. i. des. ss.
  - exploit reduce_maydiff_preserved_fit_type_spec1; eauto. i. des. ss.
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
