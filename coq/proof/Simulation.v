Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Import Opsem.

Require Import sflib.
Require Import paco.
Require Import Classical.

Require Import GenericValues.

Set Implicit Arguments.


Inductive sInsn_indexed (conf:Config):
  forall (st1 st2:State) (idx1 idx2:nat) (event:trace), Prop :=
| sInsn_step
    st1 st2 idx1 idx2 event
    (STEP: sInsn conf st1 st2 event):
    sInsn_indexed conf st1 st2 idx1 idx2 event
| sInsn_stutter
    st idx1 idx2
    (IDX: (idx1 > idx2)%nat):
    sInsn_indexed conf st st idx1 idx2 E0
.

Inductive future_error_state (conf: Config) (st0: State): Prop :=
| future_error_state_intro
    (STUCK: forall st1 (TAU: sop_star conf st0 st1 E0), error_state conf st1)
.

Lemma error_future_error
      conf st
      (ERROR: error_state conf st)
  :
    <<FUTURE: future_error_state conf st>>
.
Proof.
  econs; eauto. i.
  inv TAU; ss.
  inv ERROR. unfold stuck_state in *. exfalso.
  apply STUCK. esplits; eauto.
Qed.

Lemma error_future_error_contrapos
      conf st
      (FUTURE: ~future_error_state conf st)
  :
    <<ERROR: ~error_state conf st>>
.
Proof. ii. apply error_future_error in H. ss. Qed.
(* TODO: Lemma on this? I can only find Decidable.contrapositive.. *)

Lemma nferror_stuck_final
      conf st
      (NFERROR: ~ future_error_state conf st)
      (STUCK: stuck_state conf st):
  exists retval, s_isFinialState conf st = Some retval.
Proof.
  apply error_future_error_contrapos in NFERROR.
  eapply nerror_stuck_final; eauto.
Qed.

Lemma nferror_nfinal_nstuck
      conf st1
      (NFERROR: ~ future_error_state conf st1)
      (NFINAL: s_isFinialState conf st1 = None):
  exists st2 e, sInsn conf st1 st2 e.
Proof.
  apply error_future_error_contrapos in NFERROR.
  eapply nerror_nfinal_nstuck; eauto.
Qed.


Section Sim.
  Variable (conf_src conf_tgt:Config).

  Inductive _sim
            (sim: forall (idx1:nat) (st1_src st1_tgt:State), Prop)
            (idx1:nat) (st1_src st1_tgt:State): Prop :=
  | _sim_error
      st2_src
      (STEP: sop_star conf_src st1_src st2_src E0)
      (ERROR: future_error_state conf_src st2_src)

  | _sim_exit
      st2_src
      ret_src ret_tgt
      (STEP_SRC: sop_star conf_src st1_src st2_src E0)
      (EXIT_SRC: s_isFinialState conf_src st2_src = Some ret_src)
      (EXIT_TGT: s_isFinialState conf_tgt st1_tgt = Some ret_tgt)
      (* TODO: the relation of ret_src and ret_tgt *)

  | _sim_step
      (PROGRESS: ~ stuck_state conf_tgt st1_tgt)
      (STEP:
         forall st3_tgt event
           (STEP: sInsn conf_tgt st1_tgt st3_tgt event),
         exists st2_src st3_src idx3,
           sop_star conf_src st1_src st2_src E0 /\
           sInsn_indexed conf_src st2_src st3_src idx1 idx3 event /\
           sim idx3 st3_src st3_tgt)
  .
  Hint Constructors _sim.

  Lemma _sim_mon: monotone3 _sim.
  Proof.
    repeat intro; inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
      i. exploit STEP; eauto. i. des.
      esplits; eauto.
  Qed.
  Hint Resolve _sim_mon: paco.

  Definition sim: _ -> _ -> _ -> Prop :=
    paco3 _sim bot3.
End Sim.
Hint Constructors _sim.
Hint Resolve _sim_mon: paco.

Lemma sop_star_sim
      conf_src conf_tgt sim idx
      st1_src st2_src
      st1_tgt
      (TAU: sop_star conf_src st1_src st2_src events.E0)
      (SIM: _sim conf_src conf_tgt sim idx st2_src st1_tgt):
  _sim conf_src conf_tgt sim idx st1_src st1_tgt.
Proof.
  inv SIM.
  - econs 1; cycle 1; eauto.
    rewrite <- events.E0_left.
    eapply opsem_props.OpsemProps.sop_star_trans; eauto.
  - econs 2; cycle 1; eauto.
    rewrite <- events.E0_left.
    eapply opsem_props.OpsemProps.sop_star_trans; eauto.
  - econs 3; eauto. i. exploit STEP; eauto. i. des.
    esplits; cycle 1; eauto.
    rewrite <- events.E0_left.
    eapply opsem_props.OpsemProps.sop_star_trans; eauto.
Qed.

Lemma _sim_src_error
      conf_src conf_tgt sim idx
      st_src st_tgt
      (SIM: forall (ERROR_SRC: ~ future_error_state conf_src st_src),
          _sim conf_src conf_tgt sim idx
               st_src st_tgt):
  _sim conf_src conf_tgt sim idx
       st_src st_tgt.
Proof.
  destruct (classic (future_error_state conf_src st_src)); eauto.
Qed.


Definition sim_module (module_src module_tgt:module): Prop :=
  forall main args
    conf_src st_src
    (SRC: s_genInitState [module_src] main args Mem.empty = Some (conf_src, st_src)),
  exists conf_tgt st_tgt idx,
    <<TGT: s_genInitState [module_tgt] main args Mem.empty = Some (conf_tgt, st_tgt)>> /\
    <<SIM: sim conf_src conf_tgt idx st_src st_tgt>>.
