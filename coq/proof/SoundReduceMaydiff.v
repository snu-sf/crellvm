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
      unfold compose, Tag.t, Ords.id.t in *. rewrite PRESERVED in *. clarify.
    - rewrite lookup_AL_filter_spec in *. des_ifs.
      unfold compose, Tag.t, Ords.id.t in *. rewrite PRESERVED in *. clarify.
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

  Lemma In_map_incl {A} (f: Exprs.ExprPair.t -> list A) x xs
        (IN: Exprs.ExprPairSet.In x xs):
    <<IN: List.incl (f x) (List.concat (List.map f (Exprs.ExprPairSet.elements xs)))>>.
  Proof.
    rewrite ExprPairSetFacts.elements_iff in IN. induction IN; ss.
    - subst. apply incl_appl. solve_leibniz. apply incl_refl.
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
End Filter.


Lemma project_into_IdT_spec e x:
  project_into_IdT e = Some x <-> e = Expr.value (ValueT.id x).
Proof.
  destruct e; ss. des_ifs.
  split; inversion 1; auto.
Qed.

Lemma project_into_IdTSet_In s x:
  IdTSet.In x (project_into_IdTSet s) ->
  exists e, ExprPairSet.In (Expr.value (ValueT.id x), e) s.
Proof.
  unfold project_into_IdTSet. i.
  rewrite ExprPairSet.fold_1 in *.
  rewrite <- fold_left_rev_right in *.
  remember (rev (ExprPairSet.elements s)) as s_elem.

  assert (incl s_elem (rev (ExprPairSet.elements s))).
  { subst. apply incl_refl. }
  clear Heqs_elem.

  induction s_elem; i.
  { ss. inversion H. }

  destruct a as [a1 a2]. ss.
  des_ifs.
  - rewrite IdTSetFacts.add_iff in *. des.
    + rewrite project_into_IdT_spec in *. subst.
      exploit IdT.compare_leibniz; eauto. i. subst.
      exists a2.
      rewrite ExprPairSetFacts.elements_iff.
      eapply InA_equiv with (eqB:=eq).
      { split.
        - apply ExprPair.compare_leibniz.
        - inversion 1. apply ExprPairFacts.compare_refl.
      }
      apply InA_iff_In.
      apply in_rev.
      unfold ExprPairSet.elt in *.
      exploit elim_incl_cons; eauto. i. des. eauto.
    + exploit IHs_elem; eauto.
      exploit elim_incl_cons; eauto. i. des. eauto.
  - exploit IHs_elem; eauto.
    exploit elim_incl_cons; eauto. i. des. eauto.
Qed.

Lemma reduce_maydiff_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst invmem inv
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem
                              (reduce_maydiff inv)>>.
Proof.
  exists invst.
  unfold reduce_maydiff. red.
  inv STATE.
  econs; ss. intro x. i.

  rewrite IdTSetFacts.diff_b in NOTIN. des_bool. des.
  { apply MAYDIFF. auto. }

  des_bool.
  rewrite <- IdTSetFacts.mem_iff in NOTIN.
  apply project_into_IdTSet_In in NOTIN. des.

  rewrite ExprPairSetFacts.filter_iff in NOTIN; [|solve_compat_bool].
  rewrite ExprPairSetFacts.filter_iff in NOTIN; [|solve_compat_bool].
  rewrite ExprPairSetFacts.filter_iff in NOTIN; [|solve_compat_bool].
  des. unfold swap_pair in *. ss.
  rewrite <- ExprPairSetFacts.mem_iff in *.

  ii.
  inv SRC. rename LESSDEF into LESSDEF_SRC.
  exploit LESSDEF_SRC; eauto. i. des. ss.

  exploit InvState.Rel.not_in_maydiff_expr_spec; eauto.
  i. des.

  inv TGT. rename LESSDEF into LESSDEF_TGT.
  exploit LESSDEF_TGT; eauto. i. des. ss.
  esplits; eauto.
  
  eapply GVs.inject_lessdef_compose; eauto.
  eapply GVs.lessdef_inject_compose; eauto.
Qed.
