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


Definition sim_module (module_src module_tgt:module): Prop :=
  forall main args
    conf_src st_src
    (SRC: s_genInitState [module_src] main args Mem.empty = Some (conf_src, st_src)),
  exists conf_tgt st_tgt idx,
    <<TGT: s_genInitState [module_tgt] main args Mem.empty = Some (conf_tgt, st_tgt)>> /\
    <<SIM: sim conf_src conf_tgt idx st_src st_tgt>>.

Definition return_locals
           (TD:TargetData)
           (c:cmd) (retval:option GenericValue) (lc:GVMap): option GVsMap :=
  match c, retval with
  | insn_call id0 false _ ct _ _ _, Some retval =>
    match (fit_gv TD ct) retval with
    | Some retval' => Some (updateAddAL _ lc id0 retval')
    | _ => None
    end
  | insn_call _ _ _ _ _ _ _, _ => Some lc
  | _, _ => None
  end.

Lemma returnUpdateLocals_spec
      TD c' Result lc lc' gl:
  returnUpdateLocals TD c' Result lc lc' gl =
  match getOperandValue TD Result lc gl with
  | Some retval => return_locals TD c' (Some retval) lc'
  | None => None
  end.
Proof.
  unfold returnUpdateLocals.
  destruct (getOperandValue TD Result lc gl); ss.
Qed.

Inductive sim_local_stack
          (conf_src conf_tgt:Config):
  forall (ecs_src ecs_tgt: ECStack) (inv:InvMem.Rel.t), Prop :=
| sim_local_stack_nil
    inv:
    sim_local_stack conf_src conf_tgt nil nil inv
| sim_local_stack_cons
    ecs0_src ecs0_tgt inv0
    inv
    func_src b_src cmd_src cmds_src term_src locals_src allocas_src ecs_src
    func_tgt b_tgt cmd_tgt cmds_tgt term_tgt locals_tgt allocas_tgt ecs_tgt
    (STACK: sim_local_stack conf_src conf_tgt ecs0_src ecs0_tgt inv0)
    (LE0: InvMem.Rel.le inv0 inv)
    (CALL_SRC: Instruction.isCallInst cmd_src)
    (ID: getCmdID cmd_src = getCmdID cmd_tgt)
    (LOCAL:
       forall inv' mem'_src mem'_tgt retval'_src retval'_tgt locals'_tgt
         (LE: InvMem.Rel.le inv inv')
         (MEM: InvMem.Rel.sem conf_src conf_tgt mem'_src mem'_tgt inv')
         (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject inv'.(InvMem.Rel.inject)) retval'_src retval'_tgt)
         (RETURN_TGT: return_locals conf_tgt.(CurTargetData) cmd_tgt retval'_tgt locals_tgt = Some locals'_tgt),
       exists idx' locals'_src,
         <<RETURN_SRC: return_locals conf_src.(CurTargetData) cmd_src retval'_src locals_src = Some locals'_src>> /\
         <<SIM:
           sim_local
             conf_src conf_tgt ecs0_src ecs0_tgt
             inv' idx'
             (mkState
                (mkEC func_src b_src cmds_src term_src locals'_src allocas_src)
                ecs_src
                mem'_src)
             (mkState
                (mkEC func_tgt b_tgt cmds_tgt term_tgt locals'_tgt allocas_tgt)
                ecs_tgt
                mem'_tgt)>>):
    sim_local_stack
      conf_src conf_tgt
      ((mkEC func_src b_src (cmd_src::cmds_src) term_src locals_src allocas_src) :: ecs_src)
      ((mkEC func_tgt b_tgt (cmd_tgt::cmds_tgt) term_tgt locals_tgt allocas_tgt) :: ecs_tgt)
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
  - (* return *)
    destruct st2_src, st_tgt. ss.
    destruct EC0, EC1. ss. subst.
    inv STACK.
    + (* final *)
      admit.
    + (* return *)
      econs 3; ss.
      { admit. (* tgt not stuck *) }
      i. inv STEP0. rewrite returnUpdateLocals_spec in *. ss.
      rewrite RET_TGT in *.
      exploit LOCAL; eauto.
      { instantiate (1 := Some _). ss. eauto. }
      i. des.
      esplits; eauto.
      * econs 1. destruct conf_src. ss. econs; eauto.
        { admit. (* free_allocas *) }
        { rewrite returnUpdateLocals_spec, RET_SRC. eauto. }
      * right. apply CIH. econs; eauto.
        etransitivity; eauto.
  - (* return_void *)
    destruct st2_src, st_tgt. ss.
    destruct EC0, EC1. ss. subst.
    inv STACK.
    + (* final *)
      admit.
    + (* return *)
      econs 3; ss.
      { admit. (* tgt not stuck *) }
      i. inv STEP0.
      destruct cmd_tgt; ss. destruct noret5; ss.
      destruct cmd_src; ss. destruct noret5; ss.
      exploit LOCAL; eauto.
      { instantiate (1 := None). instantiate (1 := None). ss. }
      i. des. inv RETURN_SRC.
      esplits; eauto.
      * econs 1. destruct conf_src. econs; eauto.
        admit. (* free_allocas *)
      * right. apply CIH. econs; eauto.
        etransitivity; eauto.
  - (* call *)
    admit.
  - econs 3; ss. i. exploit STEP; eauto. i. des.
    inv SIM; [|done].
    esplits; eauto. right.
    apply CIH. econs; eauto.
    etransitivity; eauto.
Admitted.
