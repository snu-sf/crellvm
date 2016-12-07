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
Require Import SimulationLocal.
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
    red.
    unfold InvState.Unary.sem_lessdef.
    ss.
    ii.
    ss.
    destruct v0; ss.
    +
      unfold InvState.Unary.sem_idT.
      destruct x. ss.
      destruct t; ss.
      * esplits; eauto.
        ss.
        admit.
        admit.
      * esplits; eauto.
        admit.
        admit.
      * admit.
    +
      esplits; eauto.
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

(* TODO: premise for unique *)
Lemma implies_alias_sound
      inv0 inv1 conf st invst gmax
      (UNIQUE: AtomSetImpl.For_all (InvState.Unary.sem_unique conf st gmax) (Invariant.unique inv0))
      (IMPLIES_ALIAS: Invariant.implies_alias inv0 inv0.(Invariant.alias) inv1.(Invariant.alias) = true)
      (ALIAS: InvState.Unary.sem_alias conf st invst (Invariant.alias inv0)):
  <<ALIAS: InvState.Unary.sem_alias conf st invst (Invariant.alias inv1)>>.
Proof.
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
    (* solve_bool_true. *)
    (* + unfold Invariant.is_unique_value in *. *)
    (*   solve_match_bool. *)
    (*   solve_bool_true. *)
    (*   apply AtomSetImpl.mem_2 in IMPLIES_ALIAS2. *)
    (*   specialize (UNIQUE (snd x) IMPLIES_ALIAS2). *)
    (*   inv UNIQUE. *)
    (*   assert (XVAL: val = gval1). *)
    (*   { unfold InvState.Unary.sem_idT in VAL1. *)
    (*     unfold InvState.Unary.sem_tag in VAL1. *)
    (*     rewrite e in VAL1. congruence. } *)
    (*   subst. *)
    (*   apply negb_true_iff in IMPLIES_ALIAS0. *)
    (*   destruct val2. *)
    (*   * ss. *)
    (*     admit. (* InvState.Unary.sem_unique - ghost? *) *)
    (*     apply (LOCALS (snd x0)). *)
    (*     { ii.  *)

      

    (*   InvState.Unary.sem_unique *)
    (*   unfold InvState.Unary.sem_diffblock. InvState.Unary.sem_noalias *)

    (*   admit. (* unique vp.(fst) *) *)
    (* + admit. (* unique vp.(snd) *) *)
    (* + eapply DIFFBLOCK; eauto. *)

    des_bool.
    des; cycle 1.
    { eapply DIFFBLOCK; eauto. }
    unfold Invariant.diffblock_by_unique in *.
    move IMPLIES_ALIAS0 at bottom.
    (* des_bool. des. des_bool. *)
    repeat (des_bool; des).
    +
      unfold Invariant.is_unique_value in *.
      des_ifs.
      unfold Invariant.values_diffblock_from_unique in *.
      des_ifs; repeat (des_bool; des).
      * (* tag is physical *)
        destruct x; destruct t; ss.
        clear IMPLIES_ALIAS1 IMPLIES_ALIAS2.
        rename i0 into i2.

        apply AtomSetFacts.mem_iff in IMPLIES_ALIAS3.
        exploit UNIQUE; try eapply IMPLIES_ALIAS3; []; intros HUniq; des.
        inv HUniq. clear MEM0 GLOBALS.

        unfold InvState.Unary.sem_idT in *. ss.

        exploit LOCALS; try apply VAL2; eauto.
        {
          des_sumbool.
          ii.
          unfold not in IMPLIES_ALIAS0.
          apply IMPLIES_ALIAS0.
          subst.
          ss.
        }
        ii; des.
        rename val into ttttttttt.

        unfold InvState.Unary.sem_diffblock in *.
        des_ifs.
      * (* const *)

        destruct x; destruct t; ss.
        clear IMPLIES_ALIAS0 IMPLIES_ALIAS1 IMPLIES_ALIAS2.
        rename i0 into i1.
        rename c into ___cnst___.

        (* should be able to build gval1 <> cnst, where cnst is diffblock with gval1 IN INV1. *)
        (* If it was in INV0? trivial *)
        assert(MEM0: ValueTPairSet.In
                       (ValueT.id (Tag.physical, i1), ValueT.const ___cnst___)
                       (Invariant.diffblock (Invariant.alias inv0))); cycle 1.
        {
          apply ValueTPairSetFacts.mem_iff in MEM0.
          eapply DIFFBLOCK; try apply MEM0; eauto.
        }

        (* sem_unique *)
        (* (forall (b : Values.block) (ofs : Integers.Int.int 31), *)
        (*     GV2ptr (CurTargetData conf) (getPointerSize (CurTargetData conf)) val = *)
        (*     Some (Values.Vptr b ofs) -> (gmax < b)%positive) *)

        (* memory_props.MemProps.const2GV_valid_ptrs: *)
        (*   forall (c0 : const) (maxb : positive) (gl : GVMap) (g : GenericValue) (S : system) (td : targetdata) (t : typ), *)
        (*     memory_props.MemProps.wf_globals maxb gl -> *)
        (*     wf_const S td c0 t -> Some g = const2GV td gl c0 -> memory_props.MemProps.valid_ptrs (maxb + 1)%positive g *)

        (* asked @yoonseung, answer was above lemma.
with wf condition, gval2 should be < maxb + 1, which means it is global.
(first maxb block = global, later = locals)
I think, then using global part of sem_unique may produce similar result with above.
         *)




        apply AtomSetFacts.mem_iff in IMPLIES_ALIAS3.
        exploit UNIQUE; try eapply IMPLIES_ALIAS3; []; intros HUniq; des.
        inv HUniq. clear LOCALS MEM0.

        unfold InvState.Unary.sem_idT in *. ss.

        (* (* exploit LOCALS; try apply VAL2; eauto. *) *)
        (* (* { *) *)
        (* (*   des_sumbool. *) *)
        (* (*   ii. *) *)
        (* (*   unfold not in IMPLIES_ALIAS0. *) *)
        (* (*   apply IMPLIES_ALIAS0. *) *)
        (* (*   subst. *) *)
        (* (*   ss. *) *)
        (* (* } *) *)
        (* (* ii; des. *) *)
        (* (* rename val into ttttttttt. *) *)

        (* unfold InvState.Unary.sem_diffblock. *)
        (* des_ifs. *)
        (* unfold GV2ptr in *. *)
        (* des_ifs. *)

        (* { *)
        (*   unfold InvState.Unary.sem_diffblock. *)
        (*   des_ifs. *)
        (* } *)
        admit.
    + admit.
  - (* noalias *)
    (* should be same with diffblock *)
Admitted.

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
    (IMPLIES_UNARY: Invariant.implies_unary inv0 inv1 = true)
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
  - eapply implies_unary_sound; eauto.
  - eapply implies_unary_sound; eauto.
  - i. apply MAYDIFF.
    apply IdTSetFacts.not_mem_iff. ii.
    apply IdTSetFacts.not_mem_iff in NOTIN. apply NOTIN.
    eapply IdTSetFacts.subset_iff; eauto.
Qed.
