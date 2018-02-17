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
Require AssnMem.
Require AssnState.

Set Implicit Arguments.


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
      invst assnmem inv
      (CONF: AssnState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst assnmem inv)
      (MEM: AssnMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) assnmem):
  exists invst1,
    <<STATE: AssnState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 assnmem
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

  exploit AssnState.Rel.not_in_maydiff_expr_spec; eauto.
  i. des.

  inv TGT. rename LESSDEF into LESSDEF_TGT.
  exploit LESSDEF_TGT; eauto. i. des. ss.
  esplits; eauto.
  
  eapply GVs.inject_lessdef_compose; eauto.
  eapply GVs.lessdef_inject_compose; eauto.
Qed.
