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
    admit.
  }
  { (* none - none *)
    esplits; des_ifs; ss.
    unfold Exprs.AtomSetImpl_from_list. ss.
    eapply Subset_sem; cycle 1.
    { unfold ForgetStackCall.t.
      apply forget_stack_Subset. }
    admit. (* different cmds *)

    (* des_ifs; cycle 1. *)
    (* { ss. inv MEM. *)
    (*   exploit genericvalues_inject.simulation__fit_gv; eauto. i. des. *)
    (*   inv CONF. rewrite TARGETDATA in *. *)
    (*   congruence. *)
    (* } *)
    
    (* instantiate (1:= (updateAddAL GenericValue (Locals (EC st0_tgt)) id_tgt retval')). *)
  }
Admitted.
