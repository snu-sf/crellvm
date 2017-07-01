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
Require Import Simulation.
Require Import Inject.
Require Import program_sim.
Require Import TODOProof.
Import Vellvm.program_sim.
Require Import OpsemAux.
Require Import memory_props.

Set Implicit Arguments.

(* TODO: Can we define general wrapper? currying/uncurrying problem ... *)
Inductive wf_ConfigI conf :=
| wf_ConfigI_intro (WF_CONF: OpsemPP.wf_Config conf)
.

Lemma wf_ConfigI_spec
      conf
  :
    <<EQ: wf_ConfigI conf <-> OpsemPP.wf_Config conf>>
.
Proof. split; ii; ss. inv H. ss. Qed.

Inductive wf_StateI conf st :=
| wf_stateP_intro (WF_ST: OpsemPP.wf_State conf st)
.

Lemma wf_StateI_spec
      st conf
  :
    <<EQ: wf_StateI conf st <-> OpsemPP.wf_State conf st>>
.
Proof. split; ii; ss. inv H. ss. Qed.

Lemma preservation
      conf st0 st1 tr
      (WF_CONF: wf_ConfigI conf)
      (WF_ST: wf_StateI conf st0)
      (STEP: sInsn conf st0 st1 tr)
  :
    <<WF_ST: wf_StateI conf st1>>
.
Proof.
  apply wf_StateI_spec in WF_ST.
  apply wf_ConfigI_spec in WF_CONF.
  apply wf_StateI_spec.
  eapply OpsemPP.preservation; eauto.
Qed.

Lemma progress
      conf st0
      (WF_CONF: wf_ConfigI conf)
      (WF_ST: wf_StateI conf st0)
  :
    (<<IS_FINAL: s_isFinialState conf st0 <> merror>>) \/
    (<<IS_UNDEFINED: OpsemPP.undefined_state conf st0>>) \/
    (<<PROGRESS: ~stuck_state conf st0>>)
.
Proof.
  apply wf_StateI_spec in WF_ST.
  apply wf_ConfigI_spec in WF_CONF.
  expl OpsemPP.progress.
  - left. ss.
  - right. right. ii. apply H. esplits; eauto.
  - right. left. ss.
Qed.

Lemma wf_lc_preservation
      conf
      st0 st1 tr
      (* (WF_CONF: wf_ConfigI conf) *)
      (WF_LC: MemProps.wf_lc st0.(Mem) st0.(EC).(Locals))
      (STEP: sInsn conf st0 st1 tr)
  :
    <<WF_LC: MemProps.wf_lc st1.(Mem) st1.(EC).(Locals)>>
.
Proof.
  destruct st0; ss. destruct EC0; ss. destruct CurCmds0; ss.
  { inv STEP; ss.
    - unfold returnUpdateLocals in *. des_ifs.
  inv STEP; destruct cmd; ss;
    try (split; [apply MemProps.updateAddAL__wf_lc; eauto; [] | by auto]); clarify.
  -
    eapply opsem_props.OpsemProps.BOP_inversion in H.
    des.
    eapply MemProps.mbop_preserves_valid_ptrs; eauto.
  -
    eapply opsem_props.OpsemProps.FBOP_inversion in H.
    des.
    eapply MemProps.mfbop_preserves_valid_ptrs; eauto.
  -
    eapply MemProps.extractGenericValue_preserves_valid_ptrs; eauto.
    (* unfold MemProps.wf_Mem in *. *)
    (* des. clear WF. *)
    eapply get_operand_valid_ptr; eauto.
  -
    eapply MemProps.insertGenericValue_preserves_valid_ptrs; eauto.
    + eapply get_operand_valid_ptr; eauto.
    + eapply get_operand_valid_ptr; eauto.
  - split. (* free *)
    + eapply MemProps.free_preserves_wf_lc; eauto.
    + eapply MemProps.free_preserves_wf_Mem; eauto.
  - split. (* alloca *)
    + exploit alloca_result; eauto. i. des.
      ii. destruct (id_dec id0 id5).
      * subst.
        rewrite lookupAL_updateAddAL_eq in *. clarify. ss.
        split; auto.
        rewrite NEXT_BLOCK. apply Plt_succ.
      * rewrite <- lookupAL_updateAddAL_neq in *; eauto.
        eapply MemProps.alloca_preserves_wf_lc_in_tail; eauto.
    + eapply MemProps.alloca_preserves_wf_Mem; eauto.
  - unfold MemProps.wf_Mem in *. des.
    eapply WF; eauto.
  - (* store *)
    assert(WF_LC2: MemProps.wf_lc Mem' lc).
    { eapply MemProps.mstore_preserves_wf_lc; eauto. }
    splits; eauto.
    red.
    (* exploit mstore_aux_valid_ptrs_preserves_wf_Mem; eauto. *)
    unfold MemProps.wf_Mem in *.
    des.
    eapply mstore_inversion in H1. des. clarify.
    exploit MemProps.nextblock_mstore_aux; eauto; []; intros NEXTBLOCK_SAME; des.
    splits; cycle 1.
    *
      rewrite <- NEXTBLOCK_SAME.
      ss.
    *
      ii.
      apply mload_inv in H1. des. clarify.
      (* destruct (Pos.eqb b0 b) eqn:T. *)
      (* { apply Peqb_true_eq in T. subst. *)
      (*   des_sumbool. } *)
      exploit MemProps.mstore_aux_preserves_mload_aux_inv; eauto; []; ii; des.
      eapply MemProps.valid_ptrs_overlap; eauto.
      { eapply get_operand_valid_ptr; eauto.
        exploit mstore_aux_valid_ptrs_preserves_wf_Mem; eauto.
        { instantiate (1:= {| CurSystem := S;
                              CurTargetData := TD;
                              CurProducts := Ps;
                              Globals := gl;
                              FunTable := fs|}). ss.
          instantiate (1:= gmax). ss. }
        { eapply get_operand_valid_ptr; eauto. splits; ss. }
        ii; ss. }
      {
        rewrite <- NEXTBLOCK_SAME.
        eapply WF; eauto.
        Check ([(Values.Vptr b0 ofs0, cm)]): mptr.
        instantiate (3:= ([(Values.Vptr b0 ofs0, cm)])).
        cbn.
        erewrite H4. ss. }
  -
    eapply dopsem.GEP_inv in H1. des.
    + eapply MemProps.undef_valid_ptrs; eauto.
    + clarify.
      exploit get_operand_valid_ptr; eauto.
  -
    eapply opsem_props.OpsemProps.TRUNC_inversion in H.
    des.
    eapply MemProps.mtrunc_preserves_valid_ptrs; eauto.
  -
    eapply opsem_props.OpsemProps.EXT_inversion in H.
    des.
    eapply MemProps.mext_preserves_valid_ptrs; eauto.
  -
    eapply opsem_props.OpsemProps.CAST_inversion in H.
    des.
    eapply MemProps.mcast_preserves_valid_ptrs; eauto.
    eapply get_operand_valid_ptr; eauto.
  -
    eapply opsem_props.OpsemProps.ICMP_inversion in H.
    des.
    eapply MemProps.micmp_preserves_valid_ptrs; eauto.
  -
    eapply opsem_props.OpsemProps.FCMP_inversion in H.
    des.
    eapply MemProps.mfcmp_preserves_valid_ptrs; eauto.
  - destruct decision.
    + eapply get_operand_valid_ptr; eauto.
    + eapply get_operand_valid_ptr; eauto.

  apply wf_StateI_spec in WF_ST.
  apply wf_ConfigI_spec in WF_CONF.
  apply wf_StateI_spec.
  eapply OpsemPP.preservation; eauto.
Qed.


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
      (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src st1_src /\
               MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt st1_tgt /\
               MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))

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
      inv2
      (INJECT_ALLOCAS: InvState.Rel.inject_allocas inv2.(InvMem.Rel.inject)
                                            st2_src.(EC).(Allocas) st1_tgt.(EC).(Allocas))
      (VALID_ALLOCAS_SRC:
         Forall (fun x => (x < inv2.(InvMem.Rel.src).(InvMem.Unary.nextblock))%positive)
                st2_src.(EC).(Allocas))
      (VALID_ALLOCAS_TGT:
         Forall (fun x => (x < inv2.(InvMem.Rel.tgt).(InvMem.Unary.nextblock))%positive)
                st1_tgt.(EC).(Allocas))
      (ALLOCAS_DISJOINT_SRC: list_disjoint st2_src.(EC).(Allocas)
                                           (InvMem.Unary.private_parent inv2.(InvMem.Rel.src)))
      (ALLOCAS_DISJOINT_TGT: list_disjoint st1_tgt.(EC).(Allocas)
                                           (InvMem.Unary.private_parent inv2.(InvMem.Rel.tgt)))
      (MEMLE: InvMem.Rel.le inv1 inv2)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st2_src.(Mem) st1_tgt.(Mem) inv2)
      (RET:
         forall retval2_src
           (RET_SRC: getOperandValue conf_src.(CurTargetData) ret2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some retval2_src),
         exists retval1_tgt,
           <<RET_TGT: getOperandValue conf_tgt.(CurTargetData) ret1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some retval1_tgt>> /\
           <<INJECT: genericvalues_inject.gv_inject inv2.(InvMem.Rel.inject) retval2_src retval1_tgt>>)
      (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src st1_src /\
               MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt st1_tgt /\
               MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))

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
      (INJECT_ALLOCAS: InvState.Rel.inject_allocas inv1.(InvMem.Rel.inject)
                                            st2_src.(EC).(Allocas) st1_tgt.(EC).(Allocas))
      (VALID_ALLOCAS_SRC:
         Forall (fun x => (x < inv1.(InvMem.Rel.src).(InvMem.Unary.nextblock))%positive)
                st2_src.(EC).(Allocas))
      (VALID_ALLOCAS_TGT:
         Forall (fun x => (x < inv1.(InvMem.Rel.tgt).(InvMem.Unary.nextblock))%positive)
                st1_tgt.(EC).(Allocas))
      (STACK_SRC: st2_src.(ECS) = stack0_src)
      (STACK_TGT: st1_tgt.(ECS) = stack0_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st2_src.(Mem) st1_tgt.(Mem) inv1)
      (ALLOCAS_DISJOINT_SRC: list_disjoint st2_src.(EC).(Allocas)
                                           (InvMem.Unary.private_parent inv1.(InvMem.Rel.src)))
      (ALLOCAS_DISJOINT_TGT: list_disjoint st1_tgt.(EC).(Allocas)
                                           (InvMem.Unary.private_parent inv1.(InvMem.Rel.tgt)))
      (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src st1_src /\
               MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt st1_tgt /\
               MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))

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
      inv2
      (MEMLE: InvMem.Rel.le inv1 inv2)
      (FUN:
         forall funval2_src
           (FUN_SRC: getOperandValue conf_src.(CurTargetData) fun2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some funval2_src),
         exists funval1_tgt,
           <<FUN_TGT: getOperandValue conf_tgt.(CurTargetData) fun1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some funval1_tgt>> /\
           <<INJECT: genericvalues_inject.gv_inject inv2.(InvMem.Rel.inject) funval2_src funval1_tgt>>)
      (ARGS:
         forall args2_src
           (ARGS_SRC: params2GVs conf_src.(CurTargetData) params2_src st2_src.(EC).(Locals) conf_src.(Globals) = Some args2_src),
         exists args1_tgt,
           <<ARGS_TGT: params2GVs conf_tgt.(CurTargetData) params1_tgt st1_tgt.(EC).(Locals) conf_tgt.(Globals) = Some args1_tgt>> /\
           <<INJECT: list_forall2 (genericvalues_inject.gv_inject inv2.(InvMem.Rel.inject)) args2_src args1_tgt>>)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st2_src.(Mem) st1_tgt.(Mem) inv2)
      uniqs_src uniqs_tgt privs_src privs_tgt
      (UNIQS_SRC: forall mptr typ align val
                         (LOAD: mload conf_src.(CurTargetData) st2_src.(Mem) mptr typ align = Some val),
          InvMem.gv_diffblock_with_blocks conf_src val uniqs_src)
      (UNIQS_GLOBALS_SRC: forall b, In b uniqs_src -> (inv2.(InvMem.Rel.gmax) < b)%positive)
      (UNIQS_TGT: forall mptr typ align val
                         (LOAD: mload conf_tgt.(CurTargetData) st1_tgt.(Mem) mptr typ align = Some val),
          InvMem.gv_diffblock_with_blocks conf_tgt val uniqs_tgt)
      (TGT_NOUNIQ: uniqs_tgt = [])
      (UNIQS_GLOBALS_TGT: forall b, In b uniqs_tgt -> (inv2.(InvMem.Rel.gmax) < b)%positive)
      (PRIVS_SRC: forall b (IN: In b privs_src),
          InvMem.private_block st2_src.(Mem) (InvMem.Rel.public_src inv2.(InvMem.Rel.inject)) b)
      (PRIVS_TGT: forall b (IN: In b privs_tgt),
          InvMem.private_block st1_tgt.(Mem) (InvMem.Rel.public_tgt inv2.(InvMem.Rel.inject)) b)
      (RETURN: forall inv3 mem3_src mem3_tgt retval3_src retval3_tgt locals4_src
                 (INCR: InvMem.Rel.le (InvMem.Rel.lift st2_src.(Mem) st1_tgt.(Mem) uniqs_src uniqs_tgt privs_src privs_tgt inv2) inv3)
                 (MEM: InvMem.Rel.sem conf_src conf_tgt mem3_src mem3_tgt inv3)
                 (RETVAL: TODO.lift2_option (genericvalues_inject.gv_inject inv3.(InvMem.Rel.inject)) retval3_src retval3_tgt)
                 (RETURN_SRC: return_locals
                                conf_src.(CurTargetData)
                                retval3_src id2_src noret2_src typ2_src
                                st2_src.(EC).(Locals)
                              = Some locals4_src)
        ,
               exists locals4_tgt idx4 inv4,
                 (* TODO: Define update_locals function *)
                 <<RETURN_TGT: return_locals
                                 conf_tgt.(CurTargetData)
                                 retval3_tgt id1_tgt noret1_tgt typ1_tgt
                                 st1_tgt.(EC).(Locals)
                               = Some locals4_tgt>> /\
                 <<MEMLE: InvMem.Rel.le inv2 inv4>> /\
                 forall
                   (WF_SRC: wf_StateI conf_src (mkState (mkEC st2_src.(EC).(CurFunction) st2_src.(EC).(CurBB) cmds2_src st2_src.(EC).(Terminator) locals4_src st2_src.(EC).(Allocas)) st2_src.(ECS) mem3_src)
                            /\ MemProps.wf_lc st2_src.(Mem) st2_src.(EC).(Locals))
                   (WF_TGT: wf_StateI conf_tgt (mkState (mkEC st1_tgt.(EC).(CurFunction) st1_tgt.(EC).(CurBB) cmds1_tgt st1_tgt.(EC).(Terminator) locals4_tgt st1_tgt.(EC).(Allocas)) st1_tgt.(ECS) mem3_tgt)
                            /\ MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))
                 ,
                   <<SIM:
                     sim_local
                       stack0_src stack0_tgt inv4 idx4
                       (mkState (mkEC st2_src.(EC).(CurFunction) st2_src.(EC).(CurBB)
                                      cmds2_src st2_src.(EC).(Terminator) locals4_src st2_src.(EC).(Allocas))
                                st2_src.(ECS) mem3_src)
                       (mkState (mkEC st1_tgt.(EC).(CurFunction) st1_tgt.(EC).(CurBB)
                                      cmds1_tgt st1_tgt.(EC).(Terminator) locals4_tgt st1_tgt.(EC).(Allocas))
                                st1_tgt.(ECS) mem3_tgt)>>)
      (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src st1_src /\
               MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt st1_tgt /\
               MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))

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
      (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src st1_src /\
               MemProps.wf_lc st1_src.(Mem) st1_src.(EC).(Locals))
      (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt st1_tgt /\
               MemProps.wf_lc st1_tgt.(Mem) st1_tgt.(EC).(Locals))
  .
  Hint Constructors _sim_local.

  Lemma _sim_local_wf
        sim_local stack0_src stack0_tgt inv1 idx1 st1_src st1_tgt
        (SIM: _sim_local sim_local stack0_src stack0_tgt inv1 idx1 st1_src st1_tgt)
    :
      <<WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt st1_tgt>>
  .
  Proof. inv SIM; des; split; assumption. Qed.

  Lemma _sim_local_mon: monotone6 _sim_local.
  Proof.
    repeat intro; inv IN.
    - econs 1; eauto.
    - econs 2; eauto.
    - econs 3; eauto.
    - econs 4; eauto.
      i. expl RETURN.
      esplits; eauto.
      i. specialize (RETURN0 WF_SRC2). specialize (RETURN0 WF_TGT2). des.
      splits; eauto.
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

(* Lemma sim_local_inject_incr *)
(*       conf_src conf_tgt sim_local stack0_src stack0_tgt inv0 idx0 mem0_src mem0_tgt ec0_src ec0_tgt *)
(*       (SIM: _sim_local conf_src conf_tgt sim_local stack0_src stack0_tgt inv0 idx0 *)
(*                        (mkState ec0_src stack0_src mem0_src) *)
(*                        (mkState ec0_tgt stack0_tgt mem0_tgt)) *)
(*       inv1 *)
(*       (LE: InvMem.Rel.le inv0 inv1) *)
(*   : *)
(*     <<SIM: _sim_local conf_src conf_tgt sim_local stack0_src stack0_tgt inv1 idx0 *)
(*                       (mkState ec0_src stack0_src mem0_src) *)
(*                       (mkState ec0_tgt stack0_tgt mem0_tgt)>> *)
(* . *)
(* Proof. *)
(*   inv SIM. *)
(*   - econs 1; eauto. *)
(*   - ss. *)
(*     econstructor 2 with (st2_src := st2_src) *)
(*                         (id2_src := id2_src) *)
(*                         (typ2_src := typ1_tgt) *)
(*                         (ret2_src := ret2_src) *)
(*                         (id1_tgt := id1_tgt) *)
(*                         (ret1_tgt := ret1_tgt) *)
(*     ; ss; ss. *)
(*     + eapply InvState.Rel.inject_allocas_preserved_aux; eauto. *)
(* Qed. *)

Lemma _sim_local_src_error
      conf_src conf_tgt sim_local ecs_src ecs_tgt
      inv index
      st_src st_tgt
      (SIM: forall (ERROR_SRC: ~ error_state conf_src st_src),
          _sim_local conf_src conf_tgt sim_local ecs_src ecs_tgt
                     inv index
                     st_src st_tgt)
      (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src st_src /\
               MemProps.wf_lc st_src.(Mem) st_src.(EC).(Locals))
      (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt st_tgt /\
               MemProps.wf_lc st_tgt.(Mem) st_tgt.(EC).(Locals))
  :
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
    (LOCALS: initLocals conf.(CurTargetData) la args = Some lc')
  :
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
      (SRC: init_fdef conf_src fdef_src args_src ec0_src)
    ,
    exists ec0_tgt idx0,
      (init_fdef conf_tgt fdef_tgt args_tgt ec0_tgt) /\
      (forall
          (WF_SRC: wf_ConfigI conf_src /\ wf_StateI conf_src (mkState ec0_src stack0_src mem0_src)
                   /\ MemProps.wf_lc mem0_src ec0_src.(Locals))
          (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt (mkState ec0_tgt stack0_tgt mem0_tgt)
                   /\ MemProps.wf_lc mem0_tgt ec0_tgt.(Locals))
        ,
          sim_local conf_src conf_tgt stack0_src stack0_tgt inv0 idx0
                    (mkState ec0_src stack0_src mem0_src)
                    (mkState ec0_tgt stack0_tgt mem0_tgt)).
End SimLocalFdef.
