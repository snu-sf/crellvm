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
    + 
      Lemma implies_unary_tmp:
        forall
        inv0 inv1 invmem invst
        conf_src st_src
          (IMPLIES: Hints.Invariant.implies_unary
                      inv0 inv1 = true)
          (SRC : InvState.Unary.sem conf_src st_src
                      (InvState.Rel.src invst) (InvMem.Rel.src invmem) inv0)
        ,
          InvState.Unary.sem conf_src st_src (InvState.Rel.src invst)
    (InvMem.Rel.src invmem) inv1.
      Proof.
        i. inv SRC.
        unfold Hints.Invariant.implies_unary in IMPLIES.
        solve_bool_true.
        econs.
        - (* lessdef *)
          Lemma ld_tmp:
            forall
              ld0 ld1 invst conf_src st_src
              (LESSDEF_IMPLIES:Exprs.ExprPairSet.for_all
              (fun p => Exprs.ExprPairSet.exists_
                          (fun q =>
                             (if (Exprs.Expr.eq_dec p.(fst) q.(fst))
                              then ((Exprs.Expr.eq_dec p.(snd) q.(snd)) ||
                                    (match p.(snd), q.(snd) with
                                     | Exprs.Expr.value v, 
                                       Exprs.Expr.value (Exprs.ValueT.const (const_undef ty)) => true
                                     | _, _ => false
                                     end))
                              else false))
                          ld0)
              ld1)
              (LESSDEF0:Exprs.ExprPairSet.For_all
                (InvState.Unary.sem_lessdef conf_src st_src
                (InvState.Rel.src invst))
                ld0),
              Exprs.ExprPairSet.For_all
                (InvState.Unary.sem_lessdef conf_src st_src
                (InvState.Rel.src invst))
                ld1.
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
              unfold InvState.Unary.sem_lessdef in LESSDEF0.
              subst.
    (*           eapply LESSDEF0. *)
    (*           esplits. *)
    (*           +  *)



                
    (*           destruct (snd x) eqn:SNDX; try done. *)
    (*           destruct (snd x0) eqn:SNDX0; try done. *)
    (*           destruct v0 eqn:VUNDEF; try done. *)
    (*           destruct  *)
    (*           rewrite -> SNDX in H1. *)
              
    (*         -  *)
    (*           esplits. *)
    (*           +  *)
            
    (*         - esplits. *)
    (*           +  *)
    (*         - ii. subst. ss. *)
          
    (*           unfold compat_bool. *)
    (*           Exprs.ExprPairSet.Exists *)

    (*         induction ld1. *)
            

            

    (*       induction  *)
    (*       eapply Exprs.ExprPairSet.for_all for_all_2. *)
        


    (*       InvState.Unary.sem *)
    (*     Hints.Invariant.implies_unary *)

        
    (*   admit. (* unary *) *)
    (* + admit. (* unary *) *)
    (* + i. apply STATE. ii. apply NOTIN. *)
    (*   apply Exprs.IdTSetFacts.mem_iff. *)
    (*   eapply Exprs.IdTSetFacts.subset_iff; eauto. *)
    (*   apply Exprs.IdTSetFacts.mem_iff. ss. *)
Admitted.
