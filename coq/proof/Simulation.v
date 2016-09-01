Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Import Opsem.

Require Import sflib.
Require Import paco.

Require Import GenericValues.
Require Import SimulationLocal.

Set Implicit Arguments.


Section Simulation.
  Variable (conf_src conf_tgt:Config).

  Inductive _sim
            (sim: forall (idx1:nat) (st1_src st1_tgt:State), Prop)
            (idx1:nat) (st1_src st1_tgt:State): Prop :=
  | _sim_error
      st2_src
      (STEP: sop_star conf_src st1_src st2_src E0)
      (ERROR: error_state conf_src st2_src)

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
         exists st2_src st3_src st3_tgt idx3,
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
End Simulation.
Hint Resolve _sim_mon: paco.


Section SimulationSystem.
  Variable (system_src system_tgt:system).

  Definition sim_system: Prop :=
    forall main args
      conf_src st_src
      (SRC: s_genInitState system_src main args Mem.empty = Some (conf_src, st_src)),
    exists conf_tgt st_tgt idx,
      s_genInitState system_tgt main args Mem.empty = Some (conf_tgt, st_tgt) /\
      sim conf_src conf_tgt idx st_src st_tgt.
End SimulationSystem.


(* TODO: Lemma sim_local_sim *)
