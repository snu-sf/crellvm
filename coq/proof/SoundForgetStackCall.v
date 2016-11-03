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
Require Import Hints.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import Inject.
Require Import SoundBase.
Require Import SoundForgetStack.

Set Implicit Arguments.


Lemma forget_stack_call_Subset inv defs_src defs_tgt
  : Hints.Invariant.Subset (ForgetStackCall.t defs_src defs_tgt inv) inv.
Proof.
  unfold ForgetStackCall.t.
  apply forget_stack_Subset.
Qed.

Lemma invst_sem_eq_locals_mem
      st0_src st1_src conf_src
      st0_tgt st1_tgt conf_tgt
      invst invmem inv
      (MEM_SRC: st0_src.(Mem) = st1_src.(Mem))
      (MEM_TGT: st0_tgt.(Mem) = st1_tgt.(Mem))
      (LOCAL_SRC: st0_src.(EC).(Locals) = st1_src.(EC).(Locals))
      (LOCAL_TGT: st0_tgt.(EC).(Locals) = st1_tgt.(EC).(Locals))
      (STATE : InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst invmem inv)
  : InvState.Rel.sem conf_src conf_tgt st1_src st1_tgt invst invmem inv.
Proof.
  inv STATE.
  econs.
  - eapply unary_sem_eq_locals_mem; eauto.
  - eapply unary_sem_eq_locals_mem; eauto.
  - i. hexploit MAYDIFF; eauto. i.
    ii. exploit H.
    { erewrite sem_idT_eq_locals; eauto. }
    i. erewrite sem_idT_eq_locals; eauto.
Qed.

(* we need additional condition: all unique in inv1 is private, so not in inject: not in return value *)
Lemma forget_stack_call_sound
      invst2 invmem2 inv1 noret typ
      mem1_src conf_src retval1_src st0_src id_src cmds_src locals1_src
      mem1_tgt conf_tgt retval1_tgt st0_tgt id_tgt cmds_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (STATE:
         InvState.Rel.sem
           conf_src conf_tgt
           (mkState st0_src.(EC) st0_src.(ECS) mem1_src)
           (mkState st0_tgt.(EC) st0_tgt.(ECS) mem1_tgt)
           invst2 invmem2 inv1)
      (MEM:
         InvMem.Rel.sem conf_src conf_tgt mem1_src mem1_tgt invmem2)
      (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject invmem2.(InvMem.Rel.inject)) retval1_src retval1_tgt)
      (RETURN_SRC: return_locals
                     conf_src.(CurTargetData)
                                retval1_src id_src noret typ
                                st0_src.(EC).(Locals)
                   = Some locals1_src)
  : exists locals2_tgt,
        <<RETURN_TGT: return_locals
                        conf_tgt.(CurTargetData)
                        retval1_tgt id_tgt noret typ
                        st0_tgt.(EC).(Locals)
                      = Some locals2_tgt>> /\
        <<STATE:
          InvState.Rel.sem
            conf_src conf_tgt
            (mkState (mkEC st0_src.(EC).(CurFunction)
                           st0_src.(EC).(CurBB)
                           cmds_src
                           st0_src.(EC).(Terminator)
                           locals1_src
                           st0_src.(EC).(Allocas))
                     st0_src.(ECS) mem1_src)
            (mkState (mkEC st0_tgt.(EC).(CurFunction)
                           st0_tgt.(EC).(CurBB)
                           cmds_tgt
                           st0_tgt.(EC).(Terminator)
                           locals2_tgt
                           st0_tgt.(EC).(Allocas))
                     st0_tgt.(ECS) mem1_tgt)
            invst2 invmem2 (ForgetStackCall.t
                              (Exprs.AtomSetImpl_from_list (ite noret None (Some id_src)))
                              (Exprs.AtomSetImpl_from_list (ite noret None (Some id_tgt)))
                              inv1)>>.
Proof.
  unfold return_locals in *.
  destruct retval1_src; destruct retval1_tgt; ss.
  { (* some - some *)
    destruct noret.
    { esplits; eauto. clarify. ss.
      eapply Subset_sem.
      eapply invst_sem_eq_locals_mem; try exact STATE; eauto.
      apply forget_stack_call_Subset.
    }
    des_ifs.
    - hexploit genericvalues_inject.simulation__fit_gv; eauto.
      { inv MEM. eauto. }
      i. des.
      esplits; eauto.
      ss.
      inv CONF. rewrite TARGETDATA in *.
      clarify.

      unfold ForgetStackCall.t.
      eapply forget_stack_sound; eauto.
      { admit. (* state_equiv_except *) }
      { admit. (* state_equiv_except *) }
      { admit. (* unique_preserved_except id *) }
      { admit. (* unique_preserved_except id *) }
      { ss. inv STATE. inv SRC. ss.
        inv MEM.
        admit. (* g2 is in inject and wf_sb_mi should guarantee g2 is validptr *)
      }
      { admit. (* ditto *) }
    - hexploit genericvalues_inject.simulation__fit_gv; eauto.
      { inv MEM. eauto. }
      i. des.
      inv CONF. rewrite TARGETDATA in *.
      congruence.
  }
  { (* none - none *)
    esplits; des_ifs; ss.
    unfold Exprs.AtomSetImpl_from_list. ss.
    eapply Subset_sem; cycle 1.
    { unfold ForgetStackCall.t.
      apply forget_stack_Subset. }
    eapply invst_sem_eq_locals_mem; try exact STATE; eauto.
Admitted.
