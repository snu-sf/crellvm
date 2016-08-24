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
Require Import GenericValues.
Require Import MemInv.
Require Import Nop.
Require Import SimulationLocal.

Definition LOCALS_TODO: Prop. Admitted.
Definition ALLOCAS_TODO: Prop. Admitted.
Definition MEM_TODO: Prop. Admitted.
Definition CONF_TODO: Prop. Admitted.

Inductive nop_state_sim
          (conf_src conf_tgt:Config)
          (stack0_src stack0_tgt:ECStack)
          (inv:Relational.t):
  forall (idx:nat) (st_src st_tgt:State), Prop :=
| nop_state_sim_intro
    fdef_src fdef_tgt
    l s_src s_tgt
    cmds_src cmds_tgt term locals_src locals_tgt allocas_src allocas_tgt
    mem_src mem_tgt
    (FDEF: nop_fdef fdef_src fdef_tgt)
    (CMDS: nop_cmds cmds_src cmds_tgt)
    (LOCALS: LOCALS_TODO)
    (ALLOCAS: ALLOCAS_TODO)
    (MEM: Relational.sem conf_src conf_tgt mem_src mem_tgt inv):
    nop_state_sim
      conf_src conf_tgt
      stack0_src stack0_tgt inv
      (length cmds_tgt)
      (mkState
         (mkEC fdef_src (l, s_src) cmds_src term locals_src allocas_src)
         stack0_src
         mem_src)
      (mkState
         (mkEC fdef_tgt (l, s_tgt) cmds_tgt term locals_tgt allocas_tgt)
         stack0_tgt
         mem_tgt)
.

Lemma locals_init
      inv la gvs_tgt
    args_src args_tgt
    conf_src conf_tgt
    (CONF: CONF_TODO)
    (ARGS: list_forall2 (GVs.inject inv.(Relational.inject)) args_src args_tgt)
    (LOCALS : initLocals (CurTargetData conf_tgt) la args_tgt = Some gvs_tgt) :
  initLocals (CurTargetData conf_src) la args_src =
  initLocals (CurTargetData conf_tgt) la args_tgt.
Proof.
Admitted.

Lemma nop_init
      conf_src conf_tgt
      stack0_src stack0_tgt
      header
      blocks_src blocks_tgt
      args_src args_tgt
      mem_src mem_tgt
      inv
      ec_tgt
      (NOP_FDEF: nop_fdef (fdef_intro header blocks_src)
                          (fdef_intro header blocks_tgt))
      (NOP_FIRST_MATCHES: option_map fst (hd_error blocks_src) = option_map fst (hd_error blocks_tgt))
      (ARGS: list_forall2 (GVs.inject inv.(Relational.inject)) args_src args_tgt)
      (MEM: MEM_TODO)
      (CONF: CONF_TODO)
      (INIT: init_fdef conf_tgt (fdef_intro header blocks_tgt) args_tgt ec_tgt):
  exists ec_src idx,
    init_fdef conf_src (fdef_intro header blocks_src) args_src ec_src /\
    nop_state_sim
      conf_src conf_tgt
      stack0_src stack0_tgt
      inv idx
      (mkState ec_src stack0_src mem_src)
      (mkState ec_tgt stack0_tgt mem_tgt).
Proof.
  inv INIT. inv NOP_FDEF. inv FDEF.
  destruct blocks_src, lb; inv NOP_FIRST_MATCHES; try inv ENTRY.
  destruct b. ss. subst. destruct s.
  esplits.
  - econs; ss. rewrite <- LOCALS. eapply locals_init; eauto.
  - generalize (BLOCKS l'). intro B. ss.
    destruct (_ == _) in B; [|done].
    ss. des. subst.
    econs; eauto.
    + econs; eauto.
    + admit.
    + admit.
Admitted.

Inductive status :=
| status_call
| status_return
| status_return_void
| status_step
.

(* TODO *)
Definition get_status (ec:ExecutionContext): status :=
  match ec.(CurCmds) with
  | c::_ =>
    match c with
    | insn_call _ _ _ _ _ _ _ => status_call
    | _ => status_step
    end
  | nil =>
    match ec.(Terminator) with
    | insn_return _ _ _ => status_return
    | insn_return_void _ => status_return_void
    | _ => status_step
    end
  end.

Lemma get_status_call_inv ec
      (CALL: get_status ec = status_call):
  exists id noret attrs ty varg f args cmds,
    ec.(CurCmds) = (insn_call id noret attrs ty varg f args)::cmds.
Proof.
  unfold get_status in *. destruct ec. ss.
  destruct CurCmds0; ss.
  - destruct Terminator0; ss.
  - destruct c; ss.
    esplits; eauto.
Qed.

Lemma get_status_return_inv ec
      (CALL: get_status ec = status_return):
    ec.(CurCmds) = [] /\
    exists id typ value, ec.(Terminator) = insn_return id typ value.
Proof.
  unfold get_status in *. destruct ec. ss. destruct CurCmds0.
  - destruct Terminator0; ss. esplits; ss.
  - destruct c; ss.
Qed.

Lemma get_status_return_void_inv ec
      (CALL: get_status ec = status_return_void):
    ec.(CurCmds) = [] /\
    exists id, ec.(Terminator) = insn_return_void id.
Proof.
  unfold get_status in *. destruct ec. ss. destruct CurCmds0.
  - destruct Terminator0; ss. esplits; ss.
  - destruct c; ss.
Qed.

Lemma nop_cmds_pop_both x src tgt
      (NOPCMDS: nop_cmds (x :: src) (x :: tgt)):
  nop_cmds src tgt.
Proof.
  inv NOPCMDS.
  unfold compose in *.
  destruct (negb (is_nop x)) eqn:T; ss.
  inv H0. auto.
Qed.

Lemma nop_cmds_pop_src_nop nop src tgt
      (ISNOP: is_nop nop = true)
      (NOPCMDS: nop_cmds (nop :: src) tgt):
  nop_cmds src tgt.
Proof.
  inv NOPCMDS.
  unfold compose in *.
  rewrite ISNOP in *. ss.
Qed.

Lemma nop_cmds_pop_tgt_nop nop src tgt
      (ISNOP: is_nop nop = true)
      (NOPCMDS: nop_cmds src (nop :: tgt)):
  nop_cmds src tgt.
Proof.
  apply nop_cmds_commutes in NOPCMDS.
  apply nop_cmds_commutes.
  eapply nop_cmds_pop_src_nop; eauto.
Qed.

Lemma nop_cmds_tgt_non_nop src non_nop tgt_tail
      (NONNOP: (is_nop non_nop) = false)
      (NOPCMDS: nop_cmds src (non_nop :: tgt_tail)):
  exists nops src_tail, src = nops ++ non_nop :: src_tail /\
                        List.forallb is_nop nops = true /\
                        nop_cmds src_tail tgt_tail.
Proof.
  generalize dependent src.
  generalize dependent tgt_tail.
  induction src; ii.
  - red in NOPCMDS. unfold compose in NOPCMDS. ss.
    rewrite NONNOP in NOPCMDS. ss.
  - destruct (is_nop a) eqn:T.
    + exploit IHsrc; eauto.
      eapply nop_cmds_pop_src_nop; eauto.
      ii. des.
      exists (a :: nops), src_tail.
      splits; auto.
      rewrite x.
      rewrite app_comm_cons. auto.
      ss. rewrite T. auto.
    + subst.
      exists [], src.
      inv NOPCMDS.
      unfold compose in *. rewrite T in *. rewrite NONNOP in *. ss.
      inv H0.
      splits; eauto.
Qed.

(* TODO
 - tgt cmds =           [non-nop] ++ .. =>
   src cmds = [nops] ++ [non-nop] ++ .. & src, tgt related
 - tgt cmds = [nop] ++ ..(A) =>
    + tgt proceeds, src waits
    + index decr by 1
    + src cmds & A related
 *)

Lemma nop_step:
  nop_state_sim <8= sim_local.
Proof.
  intros conf_src conf_tgt stack0_src stack0_tgt.
  pcofix CIH.
  intros inv0 idx0 st_src st_tgt SIM. pfold.
  generalize (classic (stuck_state conf_tgt st_tgt)). intro STUCK. des.
  { inv SIM. eapply _sim_local_error.
    - econs 1.
    - admit. (* tgt stuck -> src stuck *)
  }
  destruct st_src as [ec_src ecs_src mem_src].
  destruct st_tgt as [ec_tgt ecs_tgt mem_tgt].
  destruct (get_status ec_tgt) eqn:TGT.
  - (* call *)
    exploit get_status_call_inv; eauto. i. des.
    inv SIM. ss. subst.
    eapply _sim_local_call.
    + econs 1.
    + ss.

admit.
  - (* return *)
    admit.
  - (* return_void *)
    admit.
  - (* step *)
    admit.

(* inv EC_INJECT. simpl in *. subst. *)
(*     apply get_status_call_inv in TGT. des. simpl in *. subst. *)
(*     exploit identity_step_call_function; ii; eauto. *)
(*     des. *)
(*     exploit identity_step_call_parameter; ii; eauto. *)
(*     des. *)
(*     eapply _sim_local_call; *)
(*       repeat (simpl in *; eauto). *)
(*     + i. eexists. right. apply CIH. *)
(*       econs; simpl; eauto. *)
(*       econs; eauto. *)
(*   - *)
(*     inv EC_INJECT; simpl in *; auto. *)
(*     symmetry in H, H0. simpl in *; subst. *)
(*     eapply get_status_return_inv in TGT. des. simpl in *. *)
(*     exploit identity_step_return; eauto; ii; des; subst. *)
(*     eapply _sim_local_return; repeat (simpl in *; eauto). *)
(*     + admit. *)
(*   - inv EC_INJECT. *)
(*     symmetry in H. symmetry in H0. *)
(*     simpl in *; subst. *)
(*     eapply get_status_return_void_inv in TGT; des. *)
(*     eapply _sim_local_return_void; repeat (simpl in *; eauto). *)
(*   - *)
(*     destruct conf_src. *)
(*     eapply _sim_local_step; simpl in *; eauto. *)
(*     ii. *)
(*     do 5 eexists. *)
(*     splits. *)
(*     + econs. *)
(*     + admit. *)
(*       (* destruct event. *) *)
(*       (* * eapply sInsn_stutter. admit. *) *)
(*       (* * *) *)
(*       (*   econs; eauto. *) *)
(*       (*   inv EC_INJECT. *) *)
(*       (*   econs. *) *)
(*       (*   instantiate (1:=inv0). admit. *) *)

(*       (*   unfold stuck_state, not in NO_ERROR. *) *)
(*       (*   apply double_neg in NO_ERROR. *) *)
(*     + instantiate (1:=inv0). *)
(*       admit. *)
(*     + right. apply CIH. *)
(*       econs; simpl; eauto. *)
(*       instantiate (2:=mkState ec_src ecs_src mem_src). *)
(*       instantiate (1:=mkState ec_tgt ecs_tgt mem_tgt). *)
(*       admit. *)
(*       simpl; auto. *)
(*       simpl; auto. *)
(*       inv STEP; simpl; auto; inv TGT. *)
(*   Unshelve. *)
(*   apply {| *)
(*       CurFunction := fdef0; *)
(*       CurBB := block0; *)
(*       CurCmds := cmds0; *)
(*       Terminator := terminator0; *)
(*       Locals := locals2; *)
(*       Allocas := allocas2 |}. *)

    (* { *)
    (* destruct conf_src. *)
    (* eapply _sim_local_step; simpl in *; eauto. *)
    (* unfold stuck_state, not. *)
    (* apply double_neg2. *)
    (* + (* ERROR should imply it *) admit. *)
    (* + i. eexists _, _, st3_tgt, _, _. splits; simpl in *; eauto. *)
    (*   * econs; eauto. *)
    (*     inv EC_INJECT. *)
    (*     (* destruct cmds0, terminator0; simpl in *; inv TGT. *) *)
    (*     admit. *)
    (*   * instantiate (1:=inv0). admit. *)
    (*   * right. apply CIH. *)
    (*     econs; simpl; eauto. *)
    (*     instantiate (1:=mkState ec_src ecs_src mem_src). *)
    (*     admit. *)
    (*     simpl; auto. *)
    (*     inv STEP; simpl; auto; inv TGT. *)
    (* } *)
Admitted.

Lemma nop_sim
      conf_src conf_tgt
      header
      blocks_src blocks_tgt
      (NOP: nop_fdef (fdef_intro header blocks_src) (fdef_intro header blocks_tgt))
      (NOP_FIRST_MATCHES: option_map fst (hd_error blocks_src) = option_map fst (hd_error blocks_tgt)):
  sim_func conf_src conf_tgt (fdef_intro header blocks_src) (fdef_intro header blocks_tgt).
Proof.
  ii.
  exploit nop_init; eauto.
  { admit. }
  { admit. }
  i. des.
  esplits; eauto.
  apply nop_step. eauto.
Admitted.

Lemma identity_step_call_function
      conf_src conf_tgt mem_src mem_tgt inv
      CurTargetData
      locals_tgt locals_src
      allocas_tgt
      fdef_tgt block_tgt
      ecs_tgt
      id noret attrs ty varg f args
      cmds terminator
      (LOCALS : LOCALS_TODO)
      (ALLOCAS : ALLOCAS_TODO)
      (MEM_INJECT : Relational.sem conf_src conf_tgt mem_src mem_tgt inv)
      (NO_ERROR :
         ~(stuck_state
             conf_tgt
             {|
               EC := {|
                  CurFunction := fdef_tgt;
                  CurBB := block_tgt;
                  CurCmds := insn_call id noret attrs ty varg f args
                             :: cmds;
                  Terminator := terminator;
                  Locals := locals_tgt;
                  Allocas := allocas_tgt |};
            ECS := ecs_tgt;
            Mem := mem_tgt |})):
  exists funval_src funval_tgt,
    getOperandValue (CurTargetData conf_tgt) f locals_tgt
                    (Globals conf_tgt) = Some funval_tgt /\
     getOperandValue (CurTargetData conf_src) f locals_src
                    (Globals conf_src) = Some funval_src /\
     GVs.inject (Relational.inject inv) funval_src funval_tgt.
Proof.
Admitted.

Lemma identity_step_call_parameter
      conf_src conf_tgt mem_src mem_tgt inv
      CurTargetData
      locals_tgt locals_src
      allocas_tgt
      fdef_tgt block_tgt
      ecs_tgt
      id noret attrs ty varg f args
      cmds terminator
      (LOCALS : True)
      (ALLOCAS : True)
      (MEM_INJECT : Relational.sem conf_src conf_tgt mem_src mem_tgt inv)
      (NO_ERROR :
         ~(stuck_state
             conf_tgt
             {|
               EC := {|
                      CurFunction := fdef_tgt;
                      CurBB := block_tgt;
                      CurCmds := insn_call id noret attrs ty varg f args
                                           :: cmds;
                      Terminator := terminator;
                      Locals := locals_tgt;
                      Allocas := allocas_tgt |};
               ECS := ecs_tgt;
               Mem := mem_tgt |})):
  exists args_src args_tgt,
    params2GVs (CurTargetData conf_src) args locals_src (Globals conf_src) =
    Some args_src /\
    params2GVs (CurTargetData conf_tgt) args locals_tgt (Globals conf_tgt) =
    Some args_tgt /\
    list_forall2 (GVs.inject (Relational.inject inv)) args_src args_tgt.
  Admitted.

Lemma identity_step_return
      inv
      mem_src conf_src
      ecs_tgt mem_tgt conf_tgt
      (* (fdef_src : fdef) *)
      (* (block_src : blocks) *)
      (* cmds_src terminator_src locals_src allocas_src *)
      fdef_tgt block_tgt cmds_tgt terminator_tgt locals_tgt allocas_tgt
      ec_src
      id typ value
      (MEM_INJECT : Relational.sem conf_src conf_tgt mem_src mem_tgt inv)
      (LOCALS : True)
      (ALLOCALS : True)
      (NO_ERROR :
         ~(stuck_state
             conf_tgt
             {|
               EC := {|
                      CurFunction := fdef_tgt;
                      CurBB := block_tgt;
                      CurCmds := cmds_tgt;
                      Terminator := terminator_tgt;
                      Locals := locals_tgt;
                      Allocas := allocas_tgt |};
               ECS := ecs_tgt;
               Mem := mem_tgt |}))
      (TGT : terminator_tgt = insn_return id typ value):
  exists retval_src retval_tgt,
    getOperandValue (CurTargetData conf_src) value (Locals ec_src)
                    (Globals conf_src) = Some retval_src /\
    getOperandValue (CurTargetData conf_tgt) value locals_tgt
                    (Globals conf_tgt) = Some retval_tgt /\
    GVs.inject (Relational.inject inv) retval_src retval_tgt.
  Admitted.
