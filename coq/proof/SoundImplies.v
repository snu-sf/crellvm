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
Require Import Exprs.
Require Import Hints.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.


(* TODO: move to somewhere *)
Ltac solve_bool_true :=
  repeat
    (try match goal with
         | [H: andb ?a ?b = true |- _] =>
           apply andb_true_iff in H; des
         | [H: orb ?a ?b = true |- _] =>
           apply orb_true_iff in H; des
         | [H: proj_sumbool (?dec ?a ?b) = true |- _] =>
           destruct (dec a b)
         end;
     try subst; ss; unfold is_true in *; unfold sflib.is_true in *).

Ltac solve_match_bool :=
  repeat (match goal with
          | [H:match ?c with _ => _ end = true |- _] =>
            let MATCH := fresh "MATCH" in
            destruct c eqn:MATCH; try done
          | [H:match ?c with _ => _ end = false |- _] =>
            let MATCH := fresh "MATCH" in
            destruct c eqn:MATCH; try done
          end).

Lemma list_forall2_refl
      X P (l: list X)
      (REFL: reflexive X P):
  <<REFL: list_forall2 P l l>>.
Proof.
  induction l; econs; eauto.
Qed.

Lemma list_forall2_trans
      X P
      (l1 l2 l3: list X)
      (FORALL1: list_forall2 P l1 l2)
      (FORALL2: list_forall2 P l2 l3)
      (IMPLIES: transitive X P):
  <<FORALL: list_forall2 P l1 l3>>.
Proof.
  revert l3 FORALL2.
  induction FORALL1; destruct l3; eauto.
  - i. inv FORALL2.
  - econs; inv FORALL2; try apply IHFORALL1; eauto.
Qed.

(* TODO: position *)
Program Instance PreOrder_GVs_lessdef: PreOrder GVs.lessdef.
Next Obligation.
  ii. apply list_forall2_refl. ss.
Qed.
Next Obligation.
  ii. unfold GVs.lessdef in *.
  eapply list_forall2_trans; eauto.
  ii. des.
  split.
  - eapply Values.Val.lessdef_trans; eauto.
  - etransitivity; eauto.
Qed.

Lemma syntactic_lessdef_spec
      conf st invst e1 e2
      (SYNTACTIC_LESSDEF:Invariant.syntactic_lessdef e1 e2):
  <<LESSDEF: InvState.Unary.sem_lessdef conf st invst (e1, e2)>>.
Proof.
  unfold Invariant.syntactic_lessdef in *. solve_bool_true; ss.
  - subst. ii. esplits; eauto. reflexivity.
  - solve_match_bool. subst.
    red. unfold InvState.Unary.sem_lessdef. ss.
    ii. ss.
    destruct v0; ss.
    +
      unfold InvState.Unary.sem_idT.
      destruct x. ss.
      destruct t; ss.
      * esplits; eauto.
        ss.
        -- admit. (* not provable, allow None? *)
        -- admit. (* undef should lessdef with all *)
      * (* ditto *) admit.
      * (* ditto *) admit.
    +
      esplits; eauto.
      (* ditto *)
      admit.
      admit.
Admitted.

Lemma implies_lessdef_sound
      ld0 ld1 invst conf st
      (IMPLIES_LESSDEF: Invariant.implies_lessdef ld0 ld1)
      (LESSDEF: ExprPairSet.For_all (InvState.Unary.sem_lessdef conf st invst) ld0):
    <<LESSDEF: ExprPairSet.For_all (InvState.Unary.sem_lessdef conf st invst) ld1>>.
Proof.
  ii. apply ExprPairSet.for_all_2 in IMPLIES_LESSDEF; eauto; cycle 1.
  { ii. subst. ss. }
  specialize (IMPLIES_LESSDEF x H). ss.
  apply ExprPairSet.exists_2 in IMPLIES_LESSDEF; eauto; cycle 1.
  { ii. subst. ss. }
  inv IMPLIES_LESSDEF. des. solve_bool_true.
  destruct x0, x; ss. subst.
  specialize (LESSDEF _ H0 _ VAL1). ss. des.
  hexploit syntactic_lessdef_spec; eauto. i. des.
  specialize (H3 _ VAL2). ss. des.
  esplits; eauto. etransitivity; eauto.
Qed.

Lemma implies_diffblock_sound
      inv0 conf st invst gmax
      val1 val2 gval1 gval2
      (UNIQUE : AtomSetImpl.For_all (InvState.Unary.sem_unique conf st gmax) (Invariant.unique inv0))
      (IMPLIES_ALIAS : Invariant.diffblock_by_unique inv0 val1 val2 = true)
      (GLOBALS : genericvalues_inject.wf_globals gmax (Globals conf))
      (VAL1: InvState.Unary.sem_valueT conf st invst val1 = Some gval1)
      (VAL2: InvState.Unary.sem_valueT conf st invst val2 = Some gval2)
  :
    <<DIFFBLOCK: InvState.Unary.sem_diffblock conf gval1 gval2>>
.
Proof.
  red.
  unfold Invariant.diffblock_by_unique in *.
  move IMPLIES_ALIAS at bottom.
  repeat (des_bool; des);
    unfold Invariant.is_unique_value in *; des_ifs;
      unfold Invariant.values_diffblock_from_unique in *; repeat (des_bool; des);
        destruct x; destruct t; ss.
  +
    clear IMPLIES_ALIAS0.
    des_ifs.
    * (* tag is physical *)
      clear IMPLIES_ALIAS1.

      apply AtomSetFacts.mem_iff in IMPLIES_ALIAS2.
      exploit UNIQUE; try eapply IMPLIES_ALIAS2; []; intros HUniq; des.
      inv HUniq. clear MEM GLOBALS.

      unfold InvState.Unary.sem_idT in *. ss.
      clarify.

      exploit UNIQUE; eauto; []; ii; des.
      eapply LOCALS with (reg := i1); eauto.
      {
        des_sumbool.
        ii.
        unfold not in IMPLIES_ALIAS.
        apply IMPLIES_ALIAS.
        subst.
        ss.
      }
    * (* const *)
      unfold AtomSetImpl.For_all in *.
      eapply AtomSetFacts.mem_iff in IMPLIES_ALIAS2.
      specialize (UNIQUE i0 IMPLIES_ALIAS2). clear IMPLIES_ALIAS2.

      eapply unique_const_diffblock; eauto.
  + (* exactly copied from above *)
    clear IMPLIES_ALIAS0.
    des_ifs.
    * (* tag is physical *)
      clear IMPLIES_ALIAS1.

      apply AtomSetFacts.mem_iff in IMPLIES_ALIAS2.
      exploit UNIQUE; try eapply IMPLIES_ALIAS2; []; intros HUniq; des.
      inv HUniq. clear MEM GLOBALS.

      unfold InvState.Unary.sem_idT in *. ss.
      clarify.

      exploit UNIQUE; eauto; []; ii; des.
      eapply LOCALS with (reg := i1); eauto.
      {
        des_sumbool.
        ii.
        unfold not in IMPLIES_ALIAS.
        apply IMPLIES_ALIAS.
        subst.
        ss.
      }
    * (* const *)
      unfold AtomSetImpl.For_all in *.
      eapply AtomSetFacts.mem_iff in IMPLIES_ALIAS2.
      specialize (UNIQUE i0 IMPLIES_ALIAS2). clear IMPLIES_ALIAS2.

      eapply InvState.Unary.diffblock_comm.
      eapply unique_const_diffblock; eauto.
Qed.

(* TODO: premise for unique *)
Lemma implies_alias_sound
      inv0 inv1 conf st invst gmax
      (UNIQUE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf st gmax) (Invariant.unique inv0))
      (IMPLIES_ALIAS: Invariant.implies_alias inv0 inv0.(Invariant.alias) inv1.(Invariant.alias) = true)
      (ALIAS: InvState.Unary.sem_alias conf st invst (Invariant.alias inv0))
      public mem invmem
      (MEM: InvMem.Unary.sem conf gmax public mem invmem)
  :
  <<ALIAS: InvState.Unary.sem_alias conf st invst (Invariant.alias inv1)>>.
Proof.
  inv MEM.
  clear WF PRIVATE_PARENT MEM_PARENT UNIQUE_PARENT_MEM
        UNIQUE_PARENT_GLOBALS UNIQUE_PRIVATE_PARENT NEXTBLOCK.
  inv ALIAS.
  unfold Invariant.implies_alias in *.
  solve_bool_true.
  econs.
  - clear IMPLIES_ALIAS NOALIAS.
    unfold Invariant.implies_diffblock, flip in *.
    i. apply ValueTPairSet.for_all_2 in IMPLIES_ALIAS0; cycle 1.
    { solve_compat_bool. }
    apply ValueTPairSet.mem_2 in MEM.
    specialize (IMPLIES_ALIAS0 (val1, val2) MEM). ss.
    des_bool.
    des; cycle 1.
    { eapply DIFFBLOCK; eauto. }
    eapply ValueTPairSetFacts.mem_iff in MEM.
    eapply implies_diffblock_sound; eauto.
  - clear IMPLIES_ALIAS0 DIFFBLOCK.
    unfold Invariant.implies_noalias, flip in *.
    i. apply PtrPairSet.for_all_2 in IMPLIES_ALIAS; cycle 1.
    { solve_compat_bool. }
    apply PtrPairSet.mem_2 in MEM.
    specialize (IMPLIES_ALIAS (ptr1, ptr2) MEM). ss.
    des_bool.
    des; cycle 1.
    { eapply NOALIAS; eauto. }
    eapply PtrPairSetFacts.mem_iff in MEM.
    eapply implies_diffblock_sound; eauto.
Qed.

Lemma implies_unique_sound
      inv0 inv1 conf st gmax
      (IMPLIES_UNIQUE:AtomSetImpl.subset (Invariant.unique inv1) (Invariant.unique inv0) = true)
      (UNIQUE : AtomSetImpl.For_all (InvState.Unary.sem_unique conf st gmax)
                                    (Invariant.unique inv0)):
  <<UNIQUE:
    AtomSetImpl.For_all
      (InvState.Unary.sem_unique conf st gmax)
      (Invariant.unique inv1)>>.
Proof.
  ii. apply AtomSetImpl.subset_2 in IMPLIES_UNIQUE; eauto.
Qed.

Lemma implies_private_sound
      inv0 inv1 conf st invst
      private_parent public
      (IMPLIES_PRIVATE : IdTSet.subset (Invariant.private inv1)
                                       (Invariant.private inv0) = true)
      (PRIVATE : IdTSet.For_all
                   (InvState.Unary.sem_private conf st invst private_parent public)
                   (Invariant.private inv0)):
  <<PRIVATE: IdTSet.For_all
               (InvState.Unary.sem_private conf st invst private_parent public)
               (Invariant.private inv1)>>.
Proof.
  intros id. apply IdTSet.subset_2 in IMPLIES_PRIVATE; eauto.
Qed.

Lemma implies_unary_sound
    inv0 inv1 invmem invst conf st gmax public
    mem
    (IMPLIES_UNARY: Invariant.implies_unary inv0 inv1 = true)
    (MEM: InvMem.Unary.sem conf gmax public mem invmem)
    (UNARY: InvState.Unary.sem conf st invst invmem gmax public inv0):
      <<UNARY: InvState.Unary.sem conf st invst invmem gmax public inv1>>.
Proof.
  i. inv UNARY.
  unfold Invariant.implies_unary in IMPLIES_UNARY.
  solve_bool_true.
  econs; eauto.
  - eapply implies_lessdef_sound; eauto.
  - eapply implies_alias_sound; eauto.
  - eapply implies_unique_sound; eauto.
  - eapply implies_private_sound; eauto.
Qed.

Lemma implies_sound
      m_src conf_src st_src
      m_tgt conf_tgt st_tgt
      invst invmem inv0 inv1
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (IMPLIES: Invariant.implies inv0 inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv1>>.
Proof.
  unfold Invariant.implies in IMPLIES.
  solve_bool_true.
  { exfalso. eapply has_false_False; eauto. }
  inv STATE. econs.
  - eapply implies_unary_sound; eauto. apply MEM.
  - eapply implies_unary_sound; eauto. apply MEM.
  - i. apply MAYDIFF.
    apply IdTSetFacts.not_mem_iff. ii.
    apply IdTSetFacts.not_mem_iff in NOTIN. apply NOTIN.
    eapply IdTSetFacts.subset_iff; eauto.
Qed.
