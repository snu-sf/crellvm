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
      (SIM: forall (ERROR_SRC: ~ error_state conf_src st_src),
          _sim conf_src conf_tgt sim idx
               st_src st_tgt):
  _sim conf_src conf_tgt sim idx
       st_src st_tgt.
Proof.
  destruct (classic (error_state conf_src st_src)); eauto.
Qed.

Definition get_params (S: system) (fid: id): option args :=
  match lookupFdefViaIDFromSystem S fid with
  | Some (fdef_intro (fheader_intro _ _ _ args _) _) => Some args
  | _ => None
  end
.

Definition TD_of_module (md: module): TargetData :=
  match md with
  | module_intro los ndts _ => (los, ndts)
  end
.

Definition sim_module (module_src module_tgt:module): Prop :=
  forall main args
    conf_src st_src
    (SRC: s_genInitState [module_src] main args Mem.empty = Some (conf_src, st_src))
    (FIT_ARGS:
       forall params
       (PARAMS: (get_params [module_src] main) = Some params),
       Forall2 (fun x y => (fit_gv (TD_of_module module_src) x.(fst).(fst) y = Some y)) params args)
  ,
  exists conf_tgt st_tgt idx,
    <<TGT: s_genInitState [module_tgt] main args Mem.empty = Some (conf_tgt, st_tgt)>> /\
    <<SIM: sim conf_src conf_tgt idx st_src st_tgt>>.
