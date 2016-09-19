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

Definition clear_locals
           (preserved: id -> bool)
           (locals: GVsMap): GVsMap :=
  filter_AL_atom (preserved) locals.

Definition clear_unary
           (preserved: Exprs.Tag.t * id -> bool)
           (inv: InvState.Unary.t): InvState.Unary.t :=
  InvState.Unary.update_ghost
    (clear_locals (fun id => preserved (Exprs.Tag.ghost, id)))
    (InvState.Unary.update_previous
       (clear_locals (fun id => preserved (Exprs.Tag.previous, id)))
       inv).

Lemma clear_locals_spec
      pred gvs i:
  lookupAL _ (clear_locals pred gvs) i =
  if pred i
  then lookupAL _ gvs i
  else None.
Proof.
  unfold clear_locals. destruct (pred i) eqn:PRED.
  - apply lookup_AL_filter_true. ss.
  - apply lookup_AL_filter_false. ss.
Qed.

Definition clear_rel
           (preserved: Exprs.Tag.t * id -> bool)
           (inv: InvState.Rel.t): InvState.Rel.t :=
  InvState.Rel.update_both (clear_unary preserved) inv.

Lemma clear_unary_subset_idT st_unary f id invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_idT
                   st_unary (clear_unary f invst_unary) id =
                 Some val)):
  <<VAL: (InvState.Unary.sem_idT st_unary invst_unary id =
          Some val)>>.
Proof.
  red.
  unfold InvState.Unary.sem_idT in *.
  unfold clear_unary, clear_locals in *.
  unfold InvState.Unary.update_ghost, InvState.Unary.update_previous in *. ss.
  unfold InvState.Unary.sem_tag in *. ss.
  destruct id. rename i0 into id. ss.
  destruct invst_unary. ss.
  destruct t; ss.
  - exploit (@lookup_AL_filter_some GenericValue); eauto.
  - exploit (@lookup_AL_filter_some GenericValue); eauto.
Qed.

Lemma clear_unary_subset_valueT conf_unary st_unary f vt invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_valueT conf_unary
                   st_unary (clear_unary f invst_unary) vt =
                 Some val)):
  <<VAL: (InvState.Unary.sem_valueT conf_unary st_unary invst_unary vt =
          Some val)>>.
Proof.
  red.
  destruct vt; ss.
  exploit clear_unary_subset_idT; eauto.
Qed.

Lemma clear_unary_subset_list_valueT conf_unary st_unary f vts invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_list_valueT conf_unary
                   st_unary (clear_unary f invst_unary) vts =
                 Some val)):
  <<VAL: (InvState.Unary.sem_list_valueT conf_unary st_unary invst_unary vts =
          Some val)>>.
Proof.
  red.
  generalize dependent val.
  induction vts; i; ss.
  destruct a; ss.
  Ltac exploit_with H x :=
    (exploit H; [exact x|]; eauto; ii; des).
  des_ifs; ss; (all_once exploit_with clear_unary_subset_valueT); (exploit IHvts; eauto; ii; des); clarify.
Qed.

Lemma clear_unary_subset_expr conf_unary st_unary f expr invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_expr conf_unary
                   st_unary (clear_unary f invst_unary) expr =
                 Some val)):
  <<VAL: (InvState.Unary.sem_expr conf_unary st_unary invst_unary expr =
          Some val)>>.
Proof.
  red.
  Ltac exploit_clear_unary_subset_with x :=
    match (type of x) with
    | (InvState.Unary.sem_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_subset_valueT; [exact x|]; eauto; ii; des)
    | (InvState.Unary.sem_list_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_subset_list_valueT; [exact x|]; eauto; ii; des)
    end.
  Time destruct expr; ss;
    des_ifs; ss; (all_once exploit_clear_unary_subset_with); clarify.
  (* exploit_with: Finished transaction in 25.39 secs (25.194u,0.213s) (successful) *)
  (* exploit_with_fast: Finished transaction in 7.575 secs (7.536u,0.044s) (successful) *)
Qed.

Lemma reduce_maydiff_preserved_sem_idT st_src st_tgt
      invst inv id val_src val_tgt
  (VAL_SRC: InvState.Unary.sem_idT st_src
              (clear_unary (reduce_maydiff_preserved inv) (InvState.Rel.src invst)) id =
            Some val_src)
  (VAL_TGT: InvState.Unary.sem_idT st_tgt (InvState.Rel.tgt invst) id = Some val_tgt):
  <<VAL_TGT: InvState.Unary.sem_idT st_tgt
    (clear_unary (reduce_maydiff_preserved inv) (InvState.Rel.tgt invst)) id = Some val_tgt>>.
Proof.
  destruct id. rename i0 into id.
  unfold InvState.Unary.sem_idT in *. ss.
  unfold InvState.Unary.sem_tag in *. ss.
  remember (fun id0 : LLVMsyntax.id => reduce_maydiff_preserved
                                         inv (Exprs.Tag.previous, id0)) as fnc.
  destruct t; ss.
  - rewrite <- VAL_TGT.
    rewrite clear_locals_spec in *.
    des_ifs.
  - rewrite <- VAL_TGT.
    rewrite clear_locals_spec in *.
    des_ifs.
Qed.

(* TODO put this in FSetExtra *)
Lemma In_list {A} (f: Exprs.ExprPair.t -> list A) x xs
      (IN: Exprs.ExprPairSet.In x xs):
  <<IN: List.incl (f x) (List.concat (List.map f (Exprs.ExprPairSet.elements xs)))>>.
Proof.
  red.
  exploit Exprs.ExprPairSetFacts.elements_iff; eauto; []; ii; des.
  specialize (x1 IN). clear x0.
  exploit InA_iff_In; eauto. ii; des.
  specialize (x2 x1). clear x0. clear x1.
  assert(G: In (f x) (List.map f (Exprs.ExprPairSet.elements xs))).
  { eapply In_map; eauto. }
  exploit (@In_concat A Exprs.ExprPair.t (list A)); eauto.
Qed.

Lemma clear_unary_preserved_valueT
      conf_unary st_unary invst_unary vt val f
      (VAL: InvState.Unary.sem_valueT conf_unary st_unary invst_unary vt = Some val)
      (PRESERVED: (sflib.is_true (List.forallb f (Exprs.ValueT.get_idTs vt)))):
  <<VAL: InvState.Unary.sem_valueT conf_unary st_unary (clear_unary f invst_unary) vt = Some val>>.
Proof.
  red.
  destruct vt; ss.
  repeat (des_bool; des). clear PRESERVED0.
  unfold InvState.Unary.sem_idT in *.
  destruct x; ss.
  unfold clear_unary.
  destruct invst_unary; ss.
  unfold Exprs.Tag.t in *. (* TODO doing left unfold is a bit annoying *)
  destruct t; ss; rewrite clear_locals_spec in *; des_ifs.
Qed.

Lemma clear_unary_preserved_list_valueT
      conf_unary st_unary invst_unary vts val f
      (VAL: InvState.Unary.sem_list_valueT conf_unary st_unary invst_unary vts = Some val)
      (PRESERVED: sflib.is_true (List.forallb
                     (fun x => (List.forallb f (Exprs.ValueT.get_idTs x)))
                     (List.map snd vts))):
  <<VAL: InvState.Unary.sem_list_valueT conf_unary st_unary (clear_unary f invst_unary) vts = Some val>>.
Proof.
  generalize dependent PRESERVED.
  generalize dependent val.
  induction vts; ii; ss; red.
  destruct a; ss.
  repeat (des_bool; des).
  des_ifs; ss.
  - (exploit clear_unary_preserved_valueT; [exact Heq1| |]; eauto; ii; des).
    exploit IHvts; eauto; []; ii; des.
    clarify.
  - (exploit clear_unary_preserved_valueT; [exact Heq1| |]; eauto; ii; des).
    clarify.
    exploit IHvts; eauto; []; ii; des.
    clarify.
  - (exploit clear_unary_preserved_valueT; [exact Heq0| |]; eauto; ii; des).
    exploit IHvts; eauto; []; ii; des.
    clarify.
Qed.

Lemma clear_unary_preserved_expr
      conf_unary st_unary invst_unary expr val f
      (VAL: InvState.Unary.sem_expr conf_unary st_unary invst_unary expr = Some val)
      (PRESERVED: List.forallb f (Exprs.Expr.get_idTs expr)):
  <<VAL: InvState.Unary.sem_expr conf_unary st_unary (clear_unary f invst_unary) expr = Some val>>.
Proof.
  red.
  unfold Exprs.Expr.get_idTs in *.
  eapply forallb_filter_map in PRESERVED. des.
  unfold is_true in PRESERVED. (* des_bool should kill it!!!!!!! KILL ALL is_true *)

  Ltac exploit_clear_unary_preserved_with x :=
    match (type of x) with
    | (InvState.Unary.sem_valueT _ _ (clear_unary _ _) _ = _) => fail 1
    | (InvState.Unary.sem_list_valueT _ _ (clear_unary _ _) _ = _) => fail 1
    (* Above is REQUIRED in order to prevent inf loop *)
    | (InvState.Unary.sem_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_preserved_valueT; [exact x| |]; eauto; ii; des)
    | (InvState.Unary.sem_list_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_preserved_list_valueT; [exact x| |]; eauto; ii; des)
    end.

  Time destruct expr; ss;
    repeat (des_bool; des); des_ifs; clarify;
      (all_once exploit_clear_unary_subset_with); clarify;
        (all_once exploit_clear_unary_preserved_with); clarify.
Qed.

Lemma incl_implies_preserved
      conf st invst0 expr val inv
      (preserved: _ -> bool)
      (PRESERVED: forall id (ID: In id (Hints.Invariant.get_idTs_unary inv)), preserved id)
      (VAL: InvState.Unary.sem_expr conf st invst0 expr = Some val)
      (INCL: incl (Exprs.Expr.get_idTs expr) (Hints.Invariant.get_idTs_unary inv)):
  <<PRESERVED: InvState.Unary.sem_expr conf st
                                       (clear_unary preserved invst0)
                                       expr = Some val>>.
Proof.
  eapply clear_unary_preserved_expr; eauto. apply forallb_forall. i.
  apply PRESERVED. apply INCL. ss.
Qed.

Lemma clear_unary_spec
      conf st invst invmem inv
      (preserved: _ -> bool)
      (PRESERVED: forall id (ID: In id (Hints.Invariant.get_idTs_unary inv)), preserved id)
      (STATE: InvState.Unary.sem conf st invst invmem inv):
  InvState.Unary.sem conf st
                     (clear_unary preserved invst)
                     invmem inv.
Proof.
  inv STATE. econs.
  - ii.
    exploit clear_unary_subset_expr; eauto. i. des.
    exploit LESSDEF; eauto. i. des.
    exploit incl_implies_preserved; eauto.
    eapply incl_tran; [|eapply incl_tran].
    + apply incl_appr. apply incl_refl.
    + eapply In_list in H. des. refine H.
    + unfold Hints.Invariant.get_idTs_unary.
      apply incl_appl. apply incl_refl.
  - inv NOALIAS. econs; i.
    + eapply DIFFBLOCK; eauto.
      * eapply clear_unary_subset_valueT; eauto.
      * eapply clear_unary_subset_valueT; eauto.
    + eapply NOALIAS0; eauto.
      * eapply clear_unary_subset_valueT; eauto.
      * eapply clear_unary_subset_valueT; eauto.
  - ii. exploit UNIQUE; eauto. i. inv x0.
    econs; eauto.
  - ii. exploit PRIVATE; eauto.
    eapply clear_unary_subset_idT; eauto.
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
  exists (clear_rel (reduce_maydiff_preserved inv) invst0). red.
  inv STATE. econs; ss; cycle 2.
  - ii. ss.
    rewrite Exprs.IdTSetFacts.filter_b in NOTIN; [|solve_compat_bool].
    des_bool. des.
    + exploit MAYDIFF; eauto.
      { exploit clear_unary_subset_idT; eauto. }
      i. des. esplits; eauto.
      eapply reduce_maydiff_preserved_sem_idT; eauto.
    + destruct id0.
      rename t into __t__, i0 into __i__.
      unfold InvState.Unary.sem_idT in VAL_SRC. ss.
      unfold InvState.Unary.sem_tag in VAL_SRC. ss.
      destruct __t__; inv NOTIN.
      * rewrite clear_locals_spec in VAL_SRC.
        unfold Exprs.Tag.t in *. rewrite H0 in VAL_SRC. ss.
      * rewrite clear_locals_spec in VAL_SRC.
        unfold Exprs.Tag.t in *. rewrite H0 in VAL_SRC. ss.
  - apply clear_unary_spec; ss. i.
    unfold reduce_maydiff_preserved. apply orb_true_iff. right.
    rewrite find_app.
    match goal with
    | [|- context[match ?g with | Some _ => _ | None => _ end]] =>
      let COND := fresh "COND" in
      destruct g eqn:COND
    end; ss.
    eapply find_none in COND; [|eauto].
    destruct (Exprs.IdT.eq_dec id0 id0); ss.
  - apply clear_unary_spec; ss. i.
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
