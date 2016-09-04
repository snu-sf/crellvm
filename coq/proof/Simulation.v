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


Section Sim.
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
End Sim.
Hint Resolve _sim_mon: paco.


Section SimModule.
  Variable (module_src module_tgt:module).

  Definition sim_module: Prop :=
    forall main args
      conf_src st_src
      (SRC: s_genInitState [module_src] main args Mem.empty = Some (conf_src, st_src)),
    exists conf_tgt st_tgt idx,
      s_genInitState [module_tgt] main args Mem.empty = Some (conf_tgt, st_tgt) /\
      sim conf_src conf_tgt idx st_src st_tgt.
End SimModule.


Inductive sim_local_stack
          (conf_src conf_tgt:Config):
  forall (ecs_src ecs_tgt: ECStack) (inv:InvMem.Rel.t), Prop :=
| sim_local_stack_nil
    inv:
    sim_local_stack conf_src conf_tgt nil nil inv
| sim_local_stack_cons
    ecs0_src ecs0_tgt inv0
    inv
    func_src b_src cmds_src term_src locals_src allocas_src ecs_src
    func_tgt b_tgt cmds_tgt term_tgt locals_tgt allocas_tgt ecs_tgt
    (STACK: sim_local_stack conf_src conf_tgt ecs0_src ecs0_tgt inv0)
    (LE0: InvMem.Rel.le inv0 inv)
    (LOCAL:
       forall inv' mem'_src mem'_tgt retval'_src retval'_tgt
         (LE: InvMem.Rel.le inv inv')
         (MEM: InvMem.Rel.sem conf_src conf_tgt mem'_src mem'_tgt inv')
         (NORET: noret = false)
         (RETVAL: GVs.inject inv'.(InvMem.Rel.inject) retval'_src retval'_tgt),
       exists idx',
         sim_local
           conf_src conf_tgt ecs0_src ecs0_tgt
           inv' idx'
           (mkState
              (mkEC func_src b_src cmds_src term_src locals_src allocas_src)
              ecs_src
              mem'_src)
           (mkState
              (mkEC func_tgt b_tgt cmds_tgt term_tgt locals_tgt allocas_tgt)
              ecs_tgt
              mem'_tgt)):
    sim_local_stack
      conf_src conf_tgt
      ((mkEC func_src b_src cmds_src term_src locals_src allocas_src) :: ecs_src)
      ((mkEC func_tgt b_tgt cmds_tgt term_tgt locals_tgt allocas_tgt) :: ecs_tgt)
      inv
.

Inductive sim_local_lift
          (conf_src conf_tgt:Config)
          (idx:nat) (st_src st_tgt: State): Prop :=
| sim_local_lift_intro
    ecs0_src ecs0_tgt inv0
    inv
    (STACK: sim_local_stack conf_src conf_tgt ecs0_src ecs0_tgt inv0)
    (LOCAL: sim_local conf_src conf_tgt ecs0_src ecs0_tgt
                      inv idx st_src st_tgt)
    (LE0: InvMem.Rel.le inv0 inv)
.

Lemma sim_local_lift_sim:
  sim_local_lift <5= sim.
Proof.
  s. intros conf_src conf_tgt. pcofix CIH. intros idx st_src st_tgt SIM. inv SIM.
  pfold. punfold LOCAL. inv LOCAL.
  - econs 1; eauto.
  - admit. (* return *)
  - admit. (* return_void *)
  - admit. (* call *)
  - econs 3; ss. i. exploit STEP; eauto. i. des.
    inv x2; [|done].
    esplits; eauto. right.
    apply CIH. econs; eauto.
    admit. (* InvMem.Rel.le trans *)
Admitted.
