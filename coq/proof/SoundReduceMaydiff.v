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
Require Import Exprs.
Require Import Hints.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.

Set Implicit Arguments.


Section Filter.
  Definition filter
             (preserved: Exprs.Tag.t * id -> bool)
             (inv: InvState.Unary.t): InvState.Unary.t :=
    InvState.Unary.update_ghost
      (filter_AL_atom (preserved <*> (pair Exprs.Tag.ghost)))
      (InvState.Unary.update_previous
         (filter_AL_atom (preserved <*> (pair Exprs.Tag.previous)))
         inv).

  Lemma filter_subset_idT st_unary f id invst_unary val
        (VAL_SUBSET: (InvState.Unary.sem_idT st_unary (filter f invst_unary) id = Some val)):
    <<VAL: (InvState.Unary.sem_idT st_unary invst_unary id = Some val)>>.
  Proof.
    destruct id. destruct t; ss.
    - eapply lookup_AL_filter_some. exact VAL_SUBSET.
    - eapply lookup_AL_filter_some. exact VAL_SUBSET.
  Qed.

  Lemma filter_subset_valueT conf_unary st_unary f vt invst_unary val
        (VAL_SUBSET: (InvState.Unary.sem_valueT
                        conf_unary st_unary
                        (filter f invst_unary) vt = Some val)):
    <<VAL: (InvState.Unary.sem_valueT conf_unary st_unary invst_unary vt = Some val)>>.
  Proof.
    red. destruct vt; ss.
    eapply filter_subset_idT; eauto.
  Qed.

  Lemma filter_subset_list_valueT conf_unary st_unary f vts invst_unary val
        (VAL_SUBSET: (InvState.Unary.sem_list_valueT
                        conf_unary st_unary
                        (filter f invst_unary) vts = Some val)):
    <<VAL: (InvState.Unary.sem_list_valueT conf_unary st_unary invst_unary vts = Some val)>>.
  Proof.
    red. revert val VAL_SUBSET. induction vts; i; ss. destruct a.
    Ltac exploit_with H x :=
      (exploit H; [exact x|]; eauto; ii; des).
    des_ifs; ss;
      (all_once exploit_with filter_subset_valueT);
      (exploit IHvts; eauto; i); clarify.
  Qed.

  Lemma filter_subset_expr conf_unary st_unary f expr invst_unary val
        (VAL_SUBSET: (InvState.Unary.sem_expr
                        conf_unary st_unary
                        (filter f invst_unary) expr = Some val)):
    <<VAL: (InvState.Unary.sem_expr conf_unary st_unary invst_unary expr = Some val)>>.
  Proof.
    red.
    Ltac exploit_filter_subset_with x :=
      match (type of x) with
      | (InvState.Unary.sem_valueT _ _ _ _ = Some _) =>
        (exploit filter_subset_valueT; [exact x|]; eauto; ii; des)
      | (InvState.Unary.sem_list_valueT _ _ _ _ = Some _) =>
        (exploit filter_subset_list_valueT; [exact x|]; eauto; ii; des)
      end.
    Time destruct expr; ss;
      des_ifs; ss; (all_once exploit_filter_subset_with); clarify.
  (* exploit_with: Finished transaction in 25.39 secs (25.194u,0.213s) (successful) *)
  (* exploit_with_fast: Finished transaction in 7.575 secs (7.536u,0.044s) (successful) *)
  Qed.

  Lemma filter_preserved_valueT
        conf_unary st_unary invst_unary vt val f
        (VAL: InvState.Unary.sem_valueT conf_unary st_unary invst_unary vt = Some val)
        (PRESERVED: (sflib.is_true (List.forallb f (Exprs.ValueT.get_idTs vt)))):
    <<VAL: InvState.Unary.sem_valueT conf_unary st_unary (filter f invst_unary) vt = Some val>>.
  Proof.
    red. destruct vt; ss. repeat (des_bool; des).
    unfold InvState.Unary.sem_idT. destruct x. s.
    destruct t; ss.
    - rewrite lookup_AL_filter_spec in *. des_ifs.
      unfold compose in *. unfold Tag.t in *. clarify.
    - rewrite lookup_AL_filter_spec in *. des_ifs.
      unfold compose in *. unfold Tag.t in *. clarify.
  Qed.

  Lemma filter_preserved_list_valueT
        conf_unary st_unary invst_unary vts val f
        (VAL: InvState.Unary.sem_list_valueT conf_unary st_unary invst_unary vts = Some val)
        (PRESERVED: sflib.is_true (List.forallb
                                     (fun x => (List.forallb f (Exprs.ValueT.get_idTs x)))
                                     (List.map snd vts))):
    <<VAL: InvState.Unary.sem_list_valueT conf_unary st_unary (filter f invst_unary) vts = Some val>>.
  Proof.
    revert val VAL PRESERVED. induction vts; i; ss.
    destruct a. ss. repeat (des_bool; des).
    des_ifs; ss.
    - (exploit filter_preserved_valueT; [exact Heq1| |]; eauto; ii; des).
      exploit IHvts; eauto; []; ii; des. clarify.
    - (exploit filter_preserved_valueT; [exact Heq1| |]; eauto; ii; des).
      exploit IHvts; eauto; []; ii; des. clarify.
    - (exploit filter_preserved_valueT; [exact Heq0| |]; eauto; ii; des).
      exploit IHvts; eauto; []; ii; des. clarify.
  Qed.

  Lemma filter_preserved_expr
        conf_unary st_unary invst_unary expr val f
        (VAL: InvState.Unary.sem_expr conf_unary st_unary invst_unary expr = Some val)
        (PRESERVED: List.forallb f (Exprs.Expr.get_idTs expr)):
    <<VAL: InvState.Unary.sem_expr conf_unary st_unary (filter f invst_unary) expr = Some val>>.
  Proof.
    red.
    unfold Exprs.Expr.get_idTs in *.
    eapply forallb_filter_map in PRESERVED. des.
    unfold is_true in PRESERVED. (* des_bool should kill it!!!!!!! KILL ALL is_true *)

    Ltac exploit_filter_preserved_with x :=
      match (type of x) with
      | (InvState.Unary.sem_valueT _ _ (filter _ _) _ = _) => fail 1
      | (InvState.Unary.sem_list_valueT _ _ (filter _ _) _ = _) => fail 1
      (* Above is REQUIRED in order to prevent inf loop *)
      | (InvState.Unary.sem_valueT _ _ _ _ = Some _) =>
        (exploit filter_preserved_valueT; [exact x| |]; eauto; ii; des)
      | (InvState.Unary.sem_list_valueT _ _ _ _ = Some _) =>
        (exploit filter_preserved_list_valueT; [exact x| |]; eauto; ii; des)
      end.

    Time destruct expr; ss;
      repeat (des_bool; des); des_ifs; clarify;
        (all_once exploit_filter_subset_with); clarify;
          (all_once exploit_filter_preserved_with); clarify.
  Qed.

  Lemma incl_implies_preserved
        conf st invst0 expr val inv
        (preserved: _ -> bool)
        (PRESERVED: forall id (ID: In id (Invariant.get_idTs_unary inv)), preserved id)
        (VAL: InvState.Unary.sem_expr conf st invst0 expr = Some val)
        (INCL: incl (Exprs.Expr.get_idTs expr) (Invariant.get_idTs_unary inv)):
    <<PRESERVED: InvState.Unary.sem_expr conf st (filter preserved invst0) expr = Some val>>.
  Proof.
    eapply filter_preserved_expr; eauto. apply forallb_forall. i.
    apply PRESERVED. apply INCL. ss.
  Qed.

  Lemma In_map_incl {A} (f: Exprs.ExprPair.t -> list A) x xs
        (IN: Exprs.ExprPairSet.In x xs):
    <<IN: List.incl (f x) (List.concat (List.map f (Exprs.ExprPairSet.elements xs)))>>.
  Proof.
    apply ExprPairSetFacts.elements_iff in IN. induction IN; ss.
    - subst. apply incl_appl. apply incl_refl.
    - apply incl_appr. ss.
  Qed.

  Lemma filter_AL_atom_preserves_wf_lc
        f mem lc
        (WF_LOCAL : memory_props.MemProps.wf_lc mem lc)
    : memory_props.MemProps.wf_lc mem (filter_AL_atom f lc).
  Proof.
    unfold memory_props.MemProps.wf_lc in *.
    i. exploit WF_LOCAL; eauto.
    eapply lookup_AL_filter_some; eauto.
  Qed.

  Lemma filter_spec
        conf st invst invmem inv gmax public
        (preserved: _ -> bool)
        (PRESERVED: forall id (ID: In id (Invariant.get_idTs_unary inv)), preserved id)
        (STATE: InvState.Unary.sem conf st invst invmem gmax public inv):
    InvState.Unary.sem conf st (filter preserved invst) invmem gmax public inv.
  Proof.
    inv STATE. econs; eauto.
    - ii.
      exploit filter_subset_expr; eauto. i. des.
      exploit LESSDEF; eauto. i. des.
      exploit incl_implies_preserved; eauto.
      eapply incl_tran; [|eapply incl_tran].
      + apply incl_appr. apply incl_refl.
      + eapply In_map_incl in H. des. refine H.
      + unfold Invariant.get_idTs_unary.
        apply incl_appl. apply incl_refl.
    - inv NOALIAS. econs; i.
      + eapply DIFFBLOCK; eauto.
        * eapply filter_subset_valueT; eauto.
        * eapply filter_subset_valueT; eauto.
      + eapply NOALIAS0; eauto.
        * eapply filter_subset_valueT; eauto.
        * eapply filter_subset_valueT; eauto.
    - ii. exploit PRIVATE; eauto.
      eapply filter_subset_idT; eauto.
    - apply filter_AL_atom_preserves_wf_lc. eauto.
    - apply filter_AL_atom_preserves_wf_lc. eauto.
    - ii. hexploit WF_VALUE; eauto.
      eapply filter_subset_valueT; eauto.
  Qed.
End Filter.

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
  ss. rewrite IdTSetFacts.filter_b in NOTIN; [|solve_compat_bool].
  repeat (des_bool; des); ss; cycle 2.
  { exploit MAYDIFF; eauto. } clear MAYDIFF.
  apply ExprPairSetFacts.exists_iff in NOTIN; [|solve_compat_bool].
  red in NOTIN; des.
  apply ExprPairSetFacts.exists_iff in NOTIN0; [|solve_compat_bool].
  red in NOTIN0; des.
  apply InvState.get_lhs_in_spec in NOTIN0.
  apply InvState.get_rhs_in_spec in NOTIN.
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

Lemma reduce_maydiff_preserved_sem_idT st_src st_tgt
      invst inv id val_src val_tgt
  (VAL_SRC: InvState.Unary.sem_idT st_src
              (filter (reduce_maydiff_preserved inv) (InvState.Rel.src invst)) id =
            Some val_src)
  (VAL_TGT: InvState.Unary.sem_idT st_tgt (InvState.Rel.tgt invst) id = Some val_tgt):
  <<VAL_TGT: InvState.Unary.sem_idT st_tgt
    (filter (reduce_maydiff_preserved inv) (InvState.Rel.tgt invst)) id = Some val_tgt>>.
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
  exists (InvState.Rel.update_both (filter (reduce_maydiff_preserved inv)) invst0). red.
  inv STATE.
  econs; ss; cycle 2.
  - ii. ss.
    rewrite IdTSetFacts.filter_b in NOTIN; [|solve_compat_bool].
    des_bool. des.
    + exploit MAYDIFF; eauto.
      { exploit filter_subset_idT; eauto. }
      i. des. esplits; eauto.
      eapply reduce_maydiff_preserved_sem_idT; eauto.
    + destruct id0.
      rename t into __t__, i0 into __i__.
      unfold InvState.Unary.sem_idT in VAL_SRC. ss.
      unfold InvState.Unary.sem_tag in VAL_SRC. ss.
      unfold compose in *.
      destruct __t__; inv NOTIN.
      * rewrite lookup_AL_filter_spec in VAL_SRC.
        unfold Tag.t in *. rewrite H0 in VAL_SRC. ss.
      * rewrite lookup_AL_filter_spec in VAL_SRC.
        unfold Tag.t in *. rewrite H0 in VAL_SRC. ss.
  - apply filter_spec; ss. i.
    unfold reduce_maydiff_preserved. apply orb_true_iff. right.
    rewrite find_app.
    match goal with
    | [|- context[match ?g with | Some _ => _ | None => _ end]] =>
      let COND := fresh "COND" in
      destruct g eqn:COND
    end; ss.
    eapply find_none in COND; [|eauto].
    destruct (IdT.eq_dec id0 id0); ss.
  - apply filter_spec; ss. i.
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
