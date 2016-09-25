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
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.


Lemma add_terminator_cond_br_uncond
      inv bid_src bid_tgt l:
  Postcond.add_terminator_cond
    inv
    (insn_br_uncond bid_src l)
    (insn_br_uncond bid_tgt l)
    l =
  inv.
Proof. destruct inv, src, tgt. ss. Qed.

Lemma add_terminator_cond_switch
      inv bid_src bid_tgt ty val_src val_tgt l0 cls l:
  Postcond.add_terminator_cond
    inv
    (insn_switch bid_src ty val_src l0 cls)
    (insn_switch bid_tgt ty val_tgt l0 cls)
    l =
  inv.
Proof. destruct inv, src, tgt. ss. Qed.

Lemma add_terminator_cond_br
      conf_src conf_tgt
      st_src st_tgt
      invst invmem inv
      decision l1 l2
      id_src val_src gval_src
      id_tgt val_tgt gval_tgt
      (STATE: InvState.Rel.sem
                conf_src conf_tgt st_src st_tgt
                invst invmem inv)
      (VAL_SRC: getOperandValue
                  conf_src.(CurTargetData)
                  val_src
                  st_src.(EC).(Locals)
                  conf_src.(Globals) = Some gval_src)
      (VAL_TGT: getOperandValue
                  conf_tgt.(CurTargetData)
                  val_tgt
                  st_tgt.(EC).(Locals)
                  conf_tgt.(Globals) = Some gval_tgt)
      (DECIDE_SRC: decide_nonzero conf_src.(CurTargetData) gval_src decision)
      (DECIDE_TGT: decide_nonzero conf_tgt.(CurTargetData) gval_tgt decision):
  InvState.Rel.sem
    conf_src conf_tgt
    st_src st_tgt
    invst invmem
    (Postcond.add_terminator_cond
       inv
       (insn_br id_src val_src l1 l2)
       (insn_br id_tgt val_tgt l1 l2) (ite decision l1 l2)).
Proof.
Admitted.

Lemma postcond_phinodes_sound
      conf_src st0_src phinodes_src cmds_src terminator_src locals_src
      conf_tgt st0_tgt phinodes_tgt cmds_tgt terminator_tgt locals_tgt
      invst0 invmem inv0 inv1
      l_from l_to
      (CMD_SRC: st0_src.(EC).(CurCmds) = [])
      (CMD_TGT: st0_tgt.(EC).(CurCmds) = [])
      (L_SRC: st0_src.(EC).(CurBB).(fst) = l_from)
      (L_TGT: st0_tgt.(EC).(CurBB).(fst) = l_from)
      (STMT_SRC: lookupAL stmts st0_src.(EC).(CurFunction).(get_blocks) l_to =
                 Some (stmts_intro phinodes_src cmds_src terminator_src))
      (STMT_TGT: lookupAL stmts st0_tgt.(EC).(CurFunction).(get_blocks) l_to =
                 Some (stmts_intro phinodes_tgt cmds_tgt terminator_tgt))
      (POSTCOND: Postcond.postcond_phinodes l_from phinodes_src phinodes_tgt inv0 = Some inv1)
      (STATE: InvState.Rel.sem conf_src conf_tgt st0_src st0_tgt invst0 invmem inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st0_src.(Mem) st0_tgt.(Mem) invmem)
      (STEP_SRC: switchToNewBasicBlock
                   conf_src.(CurTargetData)
                   (l_to, stmts_intro phinodes_src cmds_src terminator_src)
                   st0_src.(EC).(CurBB)
                   conf_src.(Globals)
                   st0_src.(EC).(Locals)
                 = Some locals_src)
      (STEP_TGT: switchToNewBasicBlock
                   conf_tgt.(CurTargetData)
                   (l_to, stmts_intro phinodes_tgt cmds_tgt terminator_tgt)
                   st0_tgt.(EC).(CurBB)
                   conf_tgt.(Globals)
                   st0_tgt.(EC).(Locals)
                 = Some locals_tgt):
  exists invst1,
    <<STATE: InvState.Rel.sem
               conf_src conf_tgt
               (mkState
                  (mkEC
                     st0_src.(EC).(CurFunction)
                     (l_to, stmts_intro phinodes_src cmds_src terminator_src)
                     cmds_src
                     terminator_src
                     locals_src
                     st0_src.(EC).(Allocas))
                  st0_src.(ECS)
                  st0_src.(Mem))
               (mkState
                  (mkEC
                     st0_tgt.(EC).(CurFunction)
                     (l_to, stmts_intro phinodes_tgt cmds_tgt terminator_tgt)
                     cmds_tgt
                     terminator_tgt
                     locals_tgt
                     st0_tgt.(EC).(Allocas))
                  st0_tgt.(ECS)
                  st0_tgt.(Mem))
               invst1 invmem inv1>>.
Proof.
Admitted.
