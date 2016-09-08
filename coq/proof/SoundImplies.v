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
         end;
     try subst; ss; unfold is_true in *).

Lemma implies_lessdef_sound
      ld0 ld1 invst conf_src st_src
      (LESSDEF_IMPLIES:
         Exprs.ExprPairSet.for_all
           (fun p => Exprs.ExprPairSet.exists_
                       (fun q =>
                          (if (Exprs.Expr.eq_dec p.(fst) q.(fst))
                           then ((Exprs.Expr.eq_dec p.(snd) q.(snd)) ||
                                 (match p.(snd), q.(snd) with
                                  | Exprs.Expr.value v, 
                                    Exprs.Expr.value (Exprs.ValueT.const (const_undef ty)) => true
                                  | _, _ => false
                                  end))
                           else false)) ld0) ld1)
      (LESSDEF0:
         Exprs.ExprPairSet.For_all
           (InvState.Unary.sem_lessdef
              conf_src st_src
              invst) ld0):
    <<IMPLIES_LESSDEF_SOUND:
      Exprs.ExprPairSet.For_all
        (InvState.Unary.sem_lessdef
           conf_src st_src
           invst) ld1>>.
Proof.
  ii.
  apply Exprs.ExprPairSet.for_all_2 in LESSDEF_IMPLIES; eauto; cycle 1.
  { ii. subst. ss. }
  specialize (LESSDEF_IMPLIES x H). ss.
  apply Exprs.ExprPairSet.exists_2 in LESSDEF_IMPLIES; eauto; cycle 1.
  { ii. subst. ss. }
  inv LESSDEF_IMPLIES. des.
  destruct (Exprs.Expr.eq_dec (fst x) (fst x0)) eqn:EXPR_DEC; try done.
  specialize (LESSDEF0 x0 H0).
  solve_bool_true.
  - assert (DECX: x = x0).
    { eapply injective_projections; eauto.
      destruct (Exprs.Expr.eq_dec (snd x) (snd x0)); done. }
    subst.
    unfold InvState.Unary.sem_lessdef in LESSDEF0.
    eapply LESSDEF0; eauto.
  - repeat (match goal with
            | [H:match ?c with _ => _ end = _ |- _] =>
              let MATCH := fresh "MATCH" in
              destruct c eqn:MATCH; try done
            end).
    unfold InvState.Unary.sem_lessdef in LESSDEF0. ss.
    exploit LESSDEF0.
    { rewrite MATCH0. ss.
      admit. (* TODO: undef from const2GV *)
    }
    i. des.
    esplits; eauto.
    rewrite e. eauto.
Admitted.

Lemma implies_alias_sound
      inv0 inv1 conf_src st_src invst
      (ALIAS_IMPLIES:Hints.Invariant.implies_alias inv0 (Hints.Invariant.alias inv0) (Hints.Invariant.alias inv1) = true)
      (NOALIAS:InvState.Unary.sem_alias conf_src st_src invst
                                        (Hints.Invariant.alias inv0)):
  <<IMPLIES_ALIAS_SOUND:
    InvState.Unary.sem_alias
      conf_src st_src invst
      (Hints.Invariant.alias inv1)>>.
Proof.
Admitted.

Lemma implies_unique_sound
      inv0 inv1 conf_src st_src invst
      (IMPLIES:AtomSetImpl.subset (Hints.Invariant.unique inv1)
                                  (Hints.Invariant.unique inv0) = true)
      (UNIQUE : AtomSetImpl.For_all
                  (InvState.Unary.sem_unique conf_src st_src invst)
                  (Hints.Invariant.unique inv0)):
  <<IMPLIES_UNIQUE_SOUND:
    AtomSetImpl.For_all
      (InvState.Unary.sem_unique conf_src st_src invst)
      (Hints.Invariant.unique inv1)>>.
Proof.
  ii. apply AtomSetImpl.subset_2 in IMPLIES; eauto.
Qed.

Lemma implies_private_sound
      inv0 inv1 conf_src st_src invst invmem
      (IMPLIES : Exprs.IdTSet.subset (Hints.Invariant.private inv1)
                                     (Hints.Invariant.private inv0) = true)
      (PRIVATE : Exprs.IdTSet.For_all
                   (InvState.Unary.sem_private
                      conf_src st_src 
                      invst
                      (InvMem.Unary.private invmem))
                   (Hints.Invariant.private inv0)):
  <<IMPLIES_PRIVATE_SOUND:
    Exprs.IdTSet.For_all
      (InvState.Unary.sem_private
         conf_src st_src invst
         (InvMem.Unary.private invmem))
      (Hints.Invariant.private inv1)>>.
Proof.
  intros id. apply Exprs.IdTSet.subset_2 in IMPLIES; eauto.
Qed.

Lemma implies_unary_sound
    inv0 inv1 invmem invst
    conf_src st_src
    (IMPLIES: Hints.Invariant.implies_unary inv0 inv1 = true)
    (SRC : InvState.Unary.sem
             conf_src st_src
             invst invmem inv0):
      <<IMPLIES_UNARY_SOUND:
        InvState.Unary.sem
          conf_src st_src invst
          invmem inv1>>.
Proof.
  i. inv SRC.
  unfold Hints.Invariant.implies_unary in IMPLIES.
  solve_bool_true.
  econs.
  - eapply implies_lessdef_sound; eauto.
  - eapply implies_alias_sound; eauto.
  - eapply implies_unique_sound; eauto.
  - eapply implies_private_sound; eauto.
Qed.

Lemma implies_sound
      m_src conf_src st_src
      m_tgt conf_tgt st_tgt
      invst invmem inv0 inv1
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
      (IMPLIES: Hints.Invariant.implies inv0 inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv1>>.
Proof.
  unfold Hints.Invariant.implies in IMPLIES.
  solve_bool_true.
  - exfalso; eapply has_false_False; eauto.
  - inv STATE. econs.
    + eapply implies_unary_sound; eauto.
    + eapply implies_unary_sound; eauto.
    + i. apply MAYDIFF. ii. apply NOTIN.
      apply Exprs.IdTSetFacts.mem_iff.
      eapply Exprs.IdTSetFacts.subset_iff; eauto.
      apply Exprs.IdTSetFacts.mem_iff. ss.
Qed.
