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
Require Import Nop.
Require Import SoundBase.
Require InvMem.
Require InvState.
Require Import Simulation.

Set Implicit Arguments.


Section SimLocal.
  Variable (conf_src conf_tgt:Config).
  Variable (inv0:InvMem.Rel.t).

  Inductive _sim_local
            (sim_local: forall (stack0_src stack0_tgt:ECStack) (inv1:InvMem.Rel.t) (idx1:nat) (st1_src st1_tgt:State), Prop)
            (stack0_src stack0_tgt:ECStack) (inv1:InvMem.Rel.t) (idx1:nat) (st1_src st1_tgt:State): Prop :=
  | _sim_local_error
      st2_src
      (STEP: sop_star conf_src st1_src st2_src E0)
      (ERROR: error_state conf_src st2_src)

  | _sim_local_return
      st2_src
      id2_src typ2_src ret2_src
      id1_tgt typ1_tgt ret1_tgt
      (STEP: sop_star conf_src st1_src st2_src E0)
      (CMDS_SRC: st2_src.(EC).(CurCmds) = nil)
      (CMDS_TGT: st1_tgt.(EC).(CurCmds) = nil)
      (TERM_SRC: st2_src.(EC).(Terminator) = insn_return id2_src typ2_src ret2_src)
      (TERM_TGT: st1_tgt.(EC).(Terminator) = insn_return id1_tgt typ1_tgt ret1_tgt)
      (TYP: typ2_src = typ1_tgt)
      (STACK_SRC: st2_src.(ECS) = stack0_src)
      (STACK_TGT: st1_tgt.(ECS) = stack0_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st2_src.(Mem) st1_tgt.(Mem) inv1)
      (RET:
         forall retval2_src
           (RET_SRC: getOperandValue conf_src.(CurTargetData) ret2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some retval2_src),
         exists retval1_tgt,
           <<RET_TGT: getOperandValue conf_tgt.(CurTargetData) ret1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some retval1_tgt>> /\
           <<INJECT: genericvalues_inject.gv_inject inv1.(InvMem.Rel.inject) retval2_src retval1_tgt>>)

  (* TODO: seems duplicate of _sim_local_return. Change semantics? *)
  | _sim_local_return_void
      st2_src
      id2_src
      id1_tgt
      (STEP: sop_star conf_src st1_src st2_src E0)
      (CMDS_SRC: st2_src.(EC).(CurCmds) = nil)
      (CMDS_TGT: st1_tgt.(EC).(CurCmds) = nil)
      (TERM_SRC: st2_src.(EC).(Terminator) = insn_return_void id2_src)
      (TERM_TGT: st1_tgt.(EC).(Terminator) = insn_return_void id1_tgt)
      (STACK_SRC: st2_src.(ECS) = stack0_src)
      (STACK_TGT: st1_tgt.(ECS) = stack0_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st2_src.(Mem) st1_tgt.(Mem) inv1)

  | _sim_local_call
      st2_src
      id2_src noret2_src clattrs2_src typ2_src varg2_src fun2_src params2_src cmds2_src
      id1_tgt noret1_tgt clattrs1_tgt typ1_tgt varg1_tgt fun1_tgt params1_tgt cmds1_tgt
      (STEP: sop_star conf_src st1_src st2_src E0)
      (CMDS_SRC: st2_src.(EC).(CurCmds) = (insn_call id2_src noret2_src clattrs2_src typ2_src varg2_src fun2_src params2_src)::cmds2_src)
      (CMDS_TGT: st1_tgt.(EC).(CurCmds) = (insn_call id1_tgt noret1_tgt clattrs1_tgt typ1_tgt varg1_tgt fun1_tgt params1_tgt)::cmds1_tgt)
      (NORET: noret2_src = noret1_tgt)
      (CLATTRS: clattrs2_src = clattrs1_tgt)
      (TYP: typ2_src = typ1_tgt)
      (VARG: varg2_src = varg1_tgt)
      (FUN:
         forall funval2_src
           (FUN_SRC: getOperandValue conf_src.(CurTargetData) fun2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some funval2_src),
         exists funval1_tgt,
           <<FUN_TGT: getOperandValue conf_tgt.(CurTargetData) fun1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some funval1_tgt>> /\
           <<INJECT: genericvalues_inject.gv_inject inv1.(InvMem.Rel.inject) funval2_src funval1_tgt>>)
      (ARGS:
         forall args2_src
           (ARGS_SRC: params2GVs conf_src.(CurTargetData) params2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
         exists args1_tgt,
           <<ARGS_TGT: params2GVs conf_tgt.(CurTargetData) params1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>> /\
           <<INJECT: list_forall2 (genericvalues_inject.gv_inject inv1.(InvMem.Rel.inject)) args2_src args1_tgt>>)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st2_src.(Mem) st1_tgt.(Mem) inv1)
      (RETURN:
         forall inv3 mem3_src mem3_tgt retval3_src retval3_tgt locals4_src
           (INCR: InvMem.Rel.le (InvMem.Rel.lift st2_src.(Mem) st1_tgt.(Mem) inv1) inv3)
           (MEM: InvMem.Rel.sem conf_src conf_tgt mem3_src mem3_tgt inv3)
           (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject inv3.(InvMem.Rel.inject)) retval3_src retval3_tgt)
           (RETURN_SRC: return_locals
                          conf_src.(CurTargetData)
                          retval3_src id2_src noret2_src typ2_src
                          st2_src.(EC).(Locals)
                        = Some locals4_src),
         exists locals4_tgt idx4 inv4,
           <<RETURN_TGT: return_locals
                           conf_tgt.(CurTargetData)
                           retval3_tgt id1_tgt noret1_tgt typ1_tgt
                           st1_tgt.(EC).(Locals)
                         = Some locals4_tgt>> /\
           <<MEMLE: InvMem.Rel.le inv1 inv4>> /\
           <<SIM:
             sim_local
               stack0_src stack0_tgt inv4 idx4
               (mkState
                  (mkEC st2_src.(EC).(CurFunction) st2_src.(EC).(CurBB) cmds2_src st2_src.(EC).(Terminator) locals4_src st2_src.(EC).(Allocas))
                  st2_src.(ECS)
                  mem3_src)
               (mkState
                  (mkEC st1_tgt.(EC).(CurFunction) st1_tgt.(EC).(CurBB) cmds1_tgt st1_tgt.(EC).(Terminator) locals4_tgt st1_tgt.(EC).(Allocas))
                  st1_tgt.(ECS)
                  mem3_tgt)>>)

  | _sim_local_step
      (PROGRESS: ~ stuck_state conf_tgt st1_tgt)
      (STEP:
         forall st3_tgt event
           (STEP: sInsn conf_tgt st1_tgt st3_tgt event),
         exists st2_src st3_src inv3 idx3,
           <<TAU: sop_star conf_src st1_src st2_src E0>> /\
           <<EVT: sInsn_indexed conf_src st2_src st3_src idx1 idx3 event>> /\
           <<MEMLE: InvMem.Rel.le inv1 inv3>> /\
           <<SIM: sim_local stack0_src stack0_tgt inv3 idx3 st3_src st3_tgt>>)
  .
  Hint Constructors _sim_local.

  Lemma _sim_local_mon: monotone6 _sim_local.
  Proof.
    repeat intro; inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
      i. exploit RETURN; eauto. i. des.
      esplits; eauto.
    - econs 5; eauto.
      i. exploit STEP; eauto. i. des.
      esplits; eauto.
  Qed.
  Hint Resolve _sim_local_mon: paco.

  Definition sim_local: _ -> _ -> _ -> _ -> _ -> _ -> Prop :=
    paco6 _sim_local bot6.
End SimLocal.
Hint Constructors _sim_local.
Hint Resolve _sim_local_mon: paco.

Lemma sop_star_sim_local
      conf_src conf_tgt sim_local ecs0_src ecs0_tgt
      inv idx
      st1_src st2_src
      st1_tgt
      (TAU: sop_star conf_src st1_src st2_src events.E0)
      (SIM: _sim_local conf_src conf_tgt sim_local ecs0_src ecs0_tgt inv idx st2_src st1_tgt):
  _sim_local conf_src conf_tgt sim_local ecs0_src ecs0_tgt inv idx st1_src st1_tgt.
Proof.
  inv SIM.
  - econs 1; try exact ERROR; eauto.
    rewrite <- events.E0_left.
    eapply opsem_props.OpsemProps.sop_star_trans; eauto.
  - econs 2; try exact MEM; eauto. 
    rewrite <- events.E0_left.
    eapply opsem_props.OpsemProps.sop_star_trans; eauto.
  - econs 3; try exact MEM; eauto.
    rewrite <- events.E0_left.
    eapply opsem_props.OpsemProps.sop_star_trans; eauto.
  - econs 4; try exact MEM; eauto.
    rewrite <- events.E0_left.
    eapply opsem_props.OpsemProps.sop_star_trans; eauto.
  - econs 5; eauto.
    i. exploit STEP; eauto. i. des.
    esplits; cycle 1; eauto.
    rewrite <- events.E0_left.
    eapply opsem_props.OpsemProps.sop_star_trans; eauto.
Qed.

Lemma _sim_local_src_error
      conf_src conf_tgt sim_local ecs_src ecs_tgt
      inv index
      st_src st_tgt
      (SIM: forall (ERROR_SRC: ~ error_state conf_src st_src),
          _sim_local conf_src conf_tgt sim_local ecs_src ecs_tgt
                     inv index
                     st_src st_tgt):
  _sim_local conf_src conf_tgt sim_local ecs_src ecs_tgt
             inv index
             st_src st_tgt.
Proof.
  destruct (classic (error_state conf_src st_src)); eauto.
Qed.


Inductive init_fdef (conf:Config) (f:fdef) (args:list GenericValue): forall (ec:ExecutionContext), Prop :=
| init_fdef_intro
    fa rt fid la va lb
    l' ps' cs' tmn'
    lc'
    (FDEF: f = fdef_intro (fheader_intro fa rt fid la va) lb)
    (ENTRY: getEntryBlock f = Some (l', stmts_intro ps' cs' tmn'))
    (LOCALS: initLocals conf.(CurTargetData) la args = Some lc'):
    init_fdef conf f args (mkEC f (l', stmts_intro ps' cs' tmn') cs' tmn' lc' nil)
.


Section SimLocalFdef.
  Variable (conf_src conf_tgt:Config).

  Definition sim_fdef (fdef_src fdef_tgt:fdef): Prop :=
    forall inv0 stack0_src stack0_tgt mem0_src mem0_tgt
      args_src args_tgt
      ec0_src
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem0_src mem0_tgt inv0)
      (ARGS: list_forall2 (genericvalues_inject.gv_inject inv0.(InvMem.Rel.inject)) args_src args_tgt)
      (SRC: init_fdef conf_src fdef_src args_src ec0_src),
    exists ec0_tgt idx0,
      init_fdef conf_tgt fdef_tgt args_tgt ec0_tgt /\
      sim_local conf_src conf_tgt stack0_src stack0_tgt inv0 idx0
                (mkState ec0_src stack0_src mem0_src)
                (mkState ec0_tgt stack0_tgt mem0_tgt).
End SimLocalFdef.