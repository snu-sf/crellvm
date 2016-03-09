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

Set Implicit Arguments.

Module MemInv.
  (* TODO *)
  Structure t := mk {
    meminj: meminj
  }.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (INCR: inject_incr lhs.(meminj) rhs.(meminj))
      (TODO: False)
  .

  (* TODO: le_public? *)
End MemInv.

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

Section SimulationLocal.
  Variable (conf_src conf_tgt:Config).
  Variable (stack0_src stack0_tgt:ECStack).
  Variable (inv0:MemInv.t).

  Inductive _sim_local
            (sim_local: MemInv.t -> nat -> State -> State -> Prop)
            (inv1:MemInv.t) (idx1:nat) (st1_src:State) (st1_tgt:State): Prop :=
  | _sim_local_error
      st2_src
      (STEP: sop_star conf_src st1_src st2_src E0)
      (ERROR: stuck_state conf_src st2_src)

  | _sim_local_return
      st2_src
      id2_src typ2_src ret2_src
      id1_tgt typ1_tgt ret1_tgt
      retval2_src
      retval1_tgt
      (STEP: sop_star conf_src st1_src st2_src E0)
      (CMDS_SRC: st2_src.(EC).(CurCmds) = nil)
      (CMDS_TGT: st1_tgt.(EC).(CurCmds) = nil)
      (TERM_SRC: st2_src.(EC).(Terminator) = insn_return id2_src typ2_src ret2_src)
      (TERM_TGT: st1_tgt.(EC).(Terminator) = insn_return id1_tgt typ1_tgt ret1_tgt)
      (TYP: typ2_src = typ1_tgt)
      (RET_SRC: getOperandValue conf_src.(CurTargetData) ret2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some retval2_src)
      (RET_TGT: getOperandValue conf_tgt.(CurTargetData) ret1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some retval1_tgt)
      (RETVAL: GVs.inject inv1.(MemInv.meminj) retval2_src retval1_tgt)

  | _sim_local_return_void
      st2_src
      id2_src
      id1_tgt
      (STEP: sop_star conf_src st1_src st2_src E0)
      (CMDS_SRC: st2_src.(EC).(CurCmds) = nil)
      (CMDS_TGT: st1_tgt.(EC).(CurCmds) = nil)
      (TERM_SRC: st2_src.(EC).(Terminator) = insn_return_void id2_src)
      (TERM_TGT: st1_tgt.(EC).(Terminator) = insn_return_void id1_tgt)

  | _sim_local_call
      st2_src
      id2_src noret2_src clattrs2_src typ2_src varg2_src fun2_src params2_src cmds2_src
      id1_tgt noret1_tgt clattrs1_tgt typ1_tgt varg1_tgt fun1_tgt params1_tgt cmds1_tgt
      funval2_src args2_src
      funval1_tgt args1_tgt
      (STEP: sop_star conf_src st1_src st2_src E0)
      (CMDS_SRC: st2_src.(EC).(CurCmds) = (insn_call id2_src noret2_src clattrs2_src typ2_src varg2_src fun2_src params2_src)::cmds2_src)
      (CMDS_TGT: st1_tgt.(EC).(CurCmds) = (insn_call id1_tgt noret1_tgt clattrs1_tgt typ1_tgt varg1_tgt fun1_tgt params1_tgt)::cmds1_tgt)
      (NORET: noret2_src = noret1_tgt)
      (CLATTRS: clattrs2_src = clattrs1_tgt)
      (TYP: typ2_src = typ1_tgt)
      (VARG: varg2_src = varg1_tgt)
      (FUN_SRC: getOperandValue conf_src.(CurTargetData) fun2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some funval2_src)
      (FUN_TGT: getOperandValue conf_tgt.(CurTargetData) fun1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some funval1_tgt)
      (FUNVAL: GVs.inject inv1.(MemInv.meminj) funval2_src funval1_tgt)
      (PARAMS_SRC: params2GVs conf_src.(CurTargetData) params2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some args2_src)
      (PARAMS_TGT: params2GVs conf_tgt.(CurTargetData) params1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt)
      (ARGS: list_forall2 (GVs.inject inv1.(MemInv.meminj)) args2_src args1_tgt)
      (RETURN:
         forall inv3 mem3_src mem3_tgt retval3_src retval3_tgt
           (INCR: MemInv.le inv1 inv3)
           (INV_TODO: False)
           (RET: noret2_src = false)
           (RETVAL: GVs.inject inv3.(MemInv.meminj) retval3_src retval3_tgt),
         exists idx3,
           sim_local
             inv3 idx3
             (mkState
                (mkEC st2_src.(EC).(CurFunction) st2_src.(EC).(CurBB) cmds2_src st2_src.(EC).(Terminator) st2_src.(EC).(Locals) st2_src.(EC).(Allocas))
                st2_src.(ECS)
                mem3_src)
             (mkState
                (mkEC st1_tgt.(EC).(CurFunction) st1_tgt.(EC).(CurBB) cmds1_tgt st1_tgt.(EC).(Terminator) st1_tgt.(EC).(Locals) st1_tgt.(EC).(Allocas))
                st1_tgt.(ECS)
                mem3_tgt))

  | _sim_local_step
      (PROGRESS: ~ stuck_state conf_tgt st1_tgt)
      (STEP:
         forall st3_tgt event
           (STEP: sInsn conf_tgt st1_tgt st3_tgt event),
         exists st2_src st3_src st3_tgt inv3 idx3,
           sop_star conf_src st1_src st2_src E0 /\
           sInsn_indexed conf_src st2_src st3_src idx1 idx3 event /\
           MemInv.le inv1 inv3 /\
           sim_local inv3 idx3 st3_src st3_tgt)
  .
  Hint Constructors _sim_local.

  Lemma _sim_local_mon: monotone4 _sim_local.
  Proof.
    repeat intro. inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
      i. exploit RETURN; eauto. i. des.
      eexists _. splits; eauto.
    - econs 5; eauto.
      i. exploit STEP; eauto. i. des.
      eexists _, _, _, _, _. splits; eauto.
  Qed.
  Hint Resolve _sim_local_mon: paco.

  Definition sim_local: _ -> _ -> _ -> _ -> Prop :=
    paco4 _sim_local bot4.
End SimulationLocal.
Hint Constructors _sim_local.
Hint Resolve _sim_local_mon: paco.
