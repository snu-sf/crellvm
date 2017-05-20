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
Require Import TODOProof.
Require Import GenericValues.
Require Import Nop.
Require Import Simulation.
Require Import SimulationLocal.
Require Import Inject.
Require Import SoundBase.
Require InvMem.
Require InvState.

Set Implicit Arguments.

Inductive nop_state_sim_EC: ExecutionContext -> ExecutionContext -> Prop :=
| nop_state_sim_EC_intro
    f_src f_tgt
    (FDEF: nop_fdef f_src f_tgt)
    bb_src bb_tgt
    (BB: nop_blocks [bb_src] [bb_tgt])
    cmds_src cmds_tgt
    (CMDS: nop_cmds cmds_src cmds_tgt)
    term lc als
  : nop_state_sim_EC (mkEC f_src bb_src cmds_src term lc als)
                     (mkEC f_tgt bb_tgt cmds_tgt term lc als)
.

(*           (ec_src ec_tgt:ExecutionContext): Prop := *)
(* | nop_state_sim_EC_intro *)
(*     (FDEF: nop_fdef ec_src.(CurFunction) ec_tgt.(CurFunction)) *)
(*     (BB: nop_blocks [ec_src.(CurBB)] [ec_tgt.(CurBB)]) *)
(*     (TERM: ec_src.(Terminator) = ec_tgt.(Terminator)) *)
(*     (LOCALS: ec_src.(Locals) = ec_tgt.(Locals)) *)
(*     (ALLOCAS: ec_src.(Allocas) = ec_tgt.(Allocas)) *)
(* . *)

Inductive nop_state_sim: nat -> State -> State -> Prop :=
| nop_state_sim_intro
  ec_src ec_tgt
  (EC: nop_state_sim_EC ec_src ec_tgt)
  ecs_src ecs_tgt
  (ECS: list_forall2 nop_state_sim_EC ecs_src ecs_tgt)
  idx
  (IDX: (idx > List.length ec_tgt.(CurCmds))%nat)
  mem
  : nop_state_sim idx
                  (mkState ec_src ecs_src mem)
                  (mkState ec_tgt ecs_tgt mem)
.

Inductive transl_product: product -> product -> Prop :=
| transl_product_gvar g
  : transl_product
      (product_gvar g) (product_gvar g)
| transl_product_fdec f
  : transl_product
      (product_fdec f) (product_fdec f)
| transl_product_fdef
    f_src f_tgt
    (NOP_FDEF: nop_fdef f_src f_tgt)
  : transl_product
      (product_fdef f_src) (product_fdef f_tgt)
.

Definition transl_products prods_src prods_tgt : Prop :=
  List.Forall2 transl_product prods_src prods_tgt
.

Lemma transl_products_lookupFdefViaIDFromProducts
      products_src products_tgt
      f fdef_src
      (PRODUCTS: transl_products products_src products_tgt)
      (SRC: lookupFdefViaIDFromProducts products_src f = Some fdef_src):
  exists fdef_tgt,
    <<TGT: lookupFdefViaIDFromProducts products_tgt f = Some fdef_tgt>> /\
    <<FDEF: transl_product (product_fdef fdef_src) (product_fdef fdef_tgt)>>
.
Proof.
  ginduction products_src; ii; ss.
  inv PRODUCTS.
  inv H1; ss.
  - hexploit IHproducts_src; eauto.
  - hexploit IHproducts_src; eauto.
  - inv NOP_FDEF. ss. des_ifs.
    + esplits; eauto.
      econs; eauto. econs; eauto.
    + hexploit IHproducts_src; eauto.
Qed.

Lemma transl_products_genGlobalAndInitMem
      layouts namedts prods_src prods_tgt
      globals locals mem
      (PRODUCTS: transl_products prods_src prods_tgt):
  genGlobalAndInitMem (layouts, namedts) prods_src globals locals mem =
  genGlobalAndInitMem (layouts, namedts) prods_tgt globals locals mem
.
Proof.
  ginduction prods_src; ii; ss.
  - inv PRODUCTS. ss.
  - inv PRODUCTS. ss.
    inv H1.
    + des_ifs; eauto.
    + des_ifs; eauto.
    + inv NOP_FDEF. des_ifs; ss.
      eapply IHprods_src; eauto.
Qed.

Inductive transl_module : forall m_src m_tgt, Prop :=
| transl_module_intro
    los ndts prods_src prods_tgt
    (TRANSL_PRODUCTS: transl_products prods_src prods_tgt)
  : transl_module (module_intro los ndts prods_src)
                  (module_intro los ndts prods_tgt)
.

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

Lemma nop_cmds_tgt_non_nop src head tail_tgt
      (NONNOP: is_nop head = false)
      (NOPCMDS: nop_cmds src (head :: tail_tgt)):
  exists nops src_tail,
    <<SRC: src = nops ++ head :: src_tail>> /\
    <<NOPSRC: List.forallb is_nop nops>> /\
    <<NOPCMDS': nop_cmds src_tail tail_tgt>>.
Proof.
  revert NOPCMDS. induction src; i.
  - red in NOPCMDS. unfold compose in NOPCMDS. ss.
    rewrite NONNOP in NOPCMDS. ss.
  - destruct (is_nop a) eqn:NOP.
    + exploit IHsrc; eauto.
      { eapply nop_cmds_pop_src_nop; eauto. }
      i. des. subst.
      exists (a :: nops), src_tail.
      splits; ss. rewrite NOP, NOPSRC. ss.
    + exists [], src. ss.
      red in NOPCMDS. unfold compose in NOPCMDS. ss.
      rewrite NONNOP in NOPCMDS. ss.
      rewrite NOP in *. ss. inv NOPCMDS; ss.
Qed.

Lemma nop_cmds_tgt_nil src
      (NOPCMDS: nop_cmds src []):
  List.forallb is_nop src.
Proof.
  revert NOPCMDS. induction src; ss. i.
  red in NOPCMDS. unfold compose in NOPCMDS. ss.
  destruct (is_nop a) eqn:NOP; ss. apply IHsrc. eauto.
Qed.

Lemma nops_sop_star
      conf fdef bb cmds_nop cmds term locals allocas ecs mem
      (NOPS: List.forallb is_nop cmds_nop):
  sop_star
    conf
    (mkState (mkEC fdef bb (cmds_nop ++ cmds) term locals allocas) ecs mem)
    (mkState (mkEC fdef bb cmds term locals allocas) ecs mem)
    events.E0.
Proof.
  move cmds_nop at top. revert_until conf.
  induction cmds_nop; ss. i.
  apply andb_true_iff in NOPS. des.
  rewrite <- events.E0_left. econs; cycle 1.
  - eapply IHcmds_nop. ss.
  - destruct a; inv NOPS. destruct conf. econs.
Qed.

Ltac is_applied_function TARGET :=
  match TARGET with
  | ?f ?x =>
    (* idtac f; idtac "is applied"; *)
    (* idtac g; idtac a; *)
    idtac
  | _ => fail
  end
.
Ltac has_inside_strict A B :=
  match A with
  | context[B] => tryif (check_equal A B) then fail else idtac
  | _ => fail
  end
.
Ltac is_inside_others_body TARGET :=
  tryif (repeat multimatch goal with
                | [ |- context[?f ?x] ] =>
                  (* idtac f; idtac x; *)
                  tryif (has_inside_strict x TARGET)
                  then fail 2
                  else fail
                end)
  then fail
  else idtac
.
Ltac on_leftest_function TAC :=
  (* repeat *)
  multimatch goal with
  | [ |- context[?f ?x] ] =>
    (* idtac f; idtac x; idtac "--------------------"; *)
    tryif (is_applied_function f)
    then fail
    else
      tryif (is_inside_others_body f)
      then fail
      else TAC f
  (* else TAC constr:(f) *)
  (* TODO: What is the difference? *)
  end
.
(* TODO: more cannonical way to get leftest function? *)
(* I tried match reverse but it was not good *)
(* TODO: I want to define "get_leftest_function" *)
(* TODO: try tactic notation ? *)

Ltac rpapply H :=
  on_leftest_function ltac:(fun f =>
     (idtac f; first
                 [ erewrite (f_equal8 f)
                 | erewrite (f_equal7 f)
                 | erewrite (f_equal6 f)
                 | erewrite (f_equal5 f)
                 | erewrite (f_equal4 f)
                 | erewrite (f_equal3 f)
                 | erewrite (f_equal2 f)
                 | erewrite (f_equal  f) | fail]); [ eapply H | .. ]; try reflexivity).

(* Lemma similar_state_same_stuck *)
(*       conf_src conf_tgt st_src st_tgt *)
(*       (CONF: inject_conf conf_src conf_tgt) *)
(*       (STUCK : stuck_state conf_tgt st_tgt) *)
(*       (CMDS: st_src.(EC).(CurCmds) = st_tgt.(EC).(CurCmds)) *)
(*       (TERM: st_src.(EC).(Terminator) = st_tgt.(EC).(Terminator)) *)
(*       (LOCALS: st_src.(EC).(Locals) = st_tgt.(EC).(Locals)) *)
(*       (ALLOCAS: st_src.(EC).(Allocas) = st_tgt.(EC).(Allocas)) *)
(*       (MEM: st_src.(Mem) = st_tgt.(Mem)) *)
(*   : *)
(*   <<STUCK: stuck_state conf_src st_src>> *)
(* . *)
(* Proof. *)
(*  inv CONF. *)
(*  destruct conf_src, conf_tgt; ss. clarify. *)
(*  destruct st_src, st_tgt; ss. clarify. *)
(*  destruct EC0, EC1; ss. clarify. *)
(*  ii. des. apply STUCK. *)
(*  destruct ECS0, ECS1; ss. *)
(*  inv H; ss.  *)
(*  esplits; eauto. eapply sReturn. econs; eauto. *)
(* Qed. *)

Lemma nop_sim
      conf_src conf_tgt
      (CONF: inject_conf conf_src conf_tgt):
  (nop_state_sim) <3= (sim conf_src conf_tgt)
.
Proof.
  s.
  pcofix CIH. intros idx0 st_src st_tgt SIM. pfold.
  (* destruct (s_isFinialState conf_tgt st_tgt) eqn:FINAL_TGT. *)
  (* { hide_goal. *)
  (*   inv SIM. inv EC0. ss. inv BB. des_ifs_safe ss. des. clarify. *)
  (*   des_ifs_safe ss. clarify. *)
  (*   assert(ecs_tgt = []). *)
  (*   { des_ifs; ss. } clarify. *)
  (*   inv ECS0. inv H4. clear_tac. *)
  (*   destruct conf_src, conf_tgt; ss. clarify. *)

  (*   eapply nop_cmds_tgt_nil in CMDS. *)
  (*   des_ifs. *)
  (*   - eapply _sim_exit; try exact FINAL_TGT. *)
  (*     + rpapply nops_sop_star; eauto. *)
  (*       rewrite app_nil_r. eauto. *)
  (*     + ss. eauto. *)
  (*   - eapply _sim_exit; try exact FINAL_TGT. *)
  (*     + rpapply nops_sop_star; eauto. *)
  (*       rewrite app_nil_r. eauto. *)
  (*     + ss. *)
  (* } *)
  destruct (classic (stuck_state conf_tgt st_tgt)).
  { rename H into STUCK.
    (* src should also be stuck *)
    inv SIM. inv EC0. ss.
    destruct cmds_tgt; ss.
    - eapply nop_cmds_tgt_nil in CMDS.
      eapply _sim_error.
      + rpapply nops_sop_star; eauto.
        rewrite app_nil_r. eauto.
      + apply error_future_error.
        econs.
        * unfold stuck_state. ii. apply STUCK.
          des.
          admit.
        * i.
              
              des_ifs.
          inv H.
          esplits; eauto. econs; eauto.
          reductio_ad_absurdum.
        reductio_ad_absurdum. unfold error_state in *.
        econs; eauto.
      
    nop_cmds_tgt_non_nop
  }
  inv SIM. inv EC0. ss.
  destruct cmds_tgt.
  { eapply nop_cmds_tgt_nil in CMDS.
    eapply _sim_step.
    - ii. apply H. econs; eauto.
  }
  inv CMDS.
Qed.

Lemma transl_sim_module:
  transl_module <2= sim_module.
Proof.
  s. intros module_src module_tgt MODULE.
  inv MODULE. ii.
  unfold s_genInitState in SRC. ss. des_ifs.
  expl transl_products_lookupFdefViaIDFromProducts.
  unfold s_genInitState. ss.
  rewrite TGT.
  match goal with
  | [|- context [productInModuleB_dec ?a ?b]] => destruct (productInModuleB_dec a b)
  end; cycle 1.
  { expl infrastructure_props.lookupFdefViaIDFromProducts_inv. ss. clarify. }

  unfold proj_sumbool.
  unfold initTargetData in *.
  expl transl_products_genGlobalAndInitMem.
  rewrite <- transl_products_genGlobalAndInitMem0. rewrite Heq1.
  inv FDEF; ss. inv NOP_FDEF; ss. inv BLOCKS; ss.
  des_ifs_safe ss. des. clarify.
  esplits; eauto.
  eapply nop_sim; ss; eauto.
  { econs; ss; eauto.
    - econs; ss; eauto.
      + econs; ss; eauto.
        econs; ss; eauto.
      + econs; ss; eauto.
    - econs; ss; eauto.
  }
Qed.



Lemma nop_init
      conf_src conf_tgt
      stack0_src stack0_tgt
      header
      blocks_src blocks_tgt
      args_src args_tgt
      mem_src mem_tgt
      inv
      ec_src
      (NOP_FDEF: nop_fdef (fdef_intro header blocks_src)
                          (fdef_intro header blocks_tgt))
      (NOP_FIRST_MATCHES: option_map fst (hd_error blocks_src) = option_map fst (hd_error blocks_tgt))
      (ARGS: list_forall2 (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) args_src args_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (CONF: inject_conf conf_src conf_tgt)
      (INIT: init_fdef conf_src (fdef_intro header blocks_src) args_src ec_src)
  :
  exists ec_tgt idx,
    (<<INIT_TGT: init_fdef conf_tgt (fdef_intro header blocks_tgt) args_tgt ec_tgt>>) /\
    (forall (WF_TGT: wf_ConfigI conf_tgt /\ wf_StateI conf_tgt (mkState ec_tgt stack0_tgt mem_tgt)),
        <<SIM: nop_state_sim
          conf_src conf_tgt
          stack0_src stack0_tgt
          inv idx
          (mkState ec_src stack0_src mem_src)
          (mkState ec_tgt stack0_tgt mem_tgt)>>).
Proof.
  inv INIT. inv NOP_FDEF. inv FDEF.
  destruct blocks_tgt, lb; inv NOP_FIRST_MATCHES; try inv ENTRY.
  destruct b. ss. subst. destruct s.
  exploit locals_init; eauto.
  { apply MEM. }
  i. des.
  esplits.
  - econs; eauto. ss.
  - unfold nop_blocks in BLOCKS. inv BLOCKS.
    des. subst.
    econs; eauto.
    + econs. econs; eauto.
    + econs.
    + ss.
    + ss.
Qed.

Inductive status :=
| status_call
| status_return
| status_return_void
| status_terminator
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
    | _ => status_terminator
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

Lemma nop_sim
      conf_src conf_tgt
      (CONF: inject_conf conf_src conf_tgt):
  (nop_state_sim conf_src conf_tgt) <6= (sim_local conf_src conf_tgt).
Proof.
  s. intros stack0_src stack0_tgt.
  pcofix CIH. intros inv0 idx0 st_src st_tgt SIM. pfold.
  generalize (classic (stuck_state conf_tgt st_tgt)). intro STUCK_TGT. des.
  { destruct (s_isFinialState conf_tgt st_tgt) eqn:FINAL_TGT; cycle 1.
    - exploit error_state_intro; eauto. i.
      (* tgt stuck -> src stuck; see old simplberry *)
      admit.
    - destruct st_tgt; ss. destruct EC0; ss. destruct CurCmds0; ss.
      destruct ECS0; [|by destruct Terminator0].
      inv SIM.
      exploit nop_cmds_tgt_nil; eauto. intro NOPS.
      rewrite (app_nil_end cmds_src).
      eapply sop_star_sim_local; [by apply nops_sop_star|].
      destruct Terminator0; inv FINAL_TGT.
      + econs 2; try reflexivity; ss.
        { ss. eapply SoundBase.fully_inject_allocas_inject_allocas; eauto. }
        s. i.
        eapply inject_locals_getOperandValue; eauto.
        eapply fully_inject_locals_inject_locals; eauto.
      + econs 3; ss.
        { ss. eapply SoundBase.fully_inject_allocas_inject_allocas; eauto. }
  }
  apply NNPP in STUCK_TGT. destruct STUCK_TGT as (st'_tgt & tr_tgt & PROGRESS_TGT).
  destruct st_src as [ec_src ecs_src mem_src].
  destruct st_tgt as [ec_tgt ecs_tgt mem_tgt].
  destruct (get_status ec_tgt) eqn:TGT.
  - (* call *)
    exploit get_status_call_inv; eauto. i. des.
    inv SIM. ss. subst.
    exploit nop_cmds_tgt_non_nop; eauto; ss. i. des. subst.
    eapply sop_star_sim_local; [by apply nops_sop_star|].
    apply _sim_local_src_error; [|split; ss]. i.
    exploit nerror_nfinal_nstuck; eauto. i.
    destruct x0 as (st'_src & tr_src & PROGRESS_SRC).
    assert (FUNC_TGT: exists func_tgt, getOperandValue (CurTargetData conf_tgt) f locals_tgt (Globals conf_tgt) = Some func_tgt).
    { inv PROGRESS_TGT; eauto. }
    assert (PARAM_TGT: exists gvs_param_tgt, params2GVs (CurTargetData conf_tgt) args0 locals_tgt (Globals conf_tgt) = Some gvs_param_tgt).
    { inv PROGRESS_TGT; eauto. }
    des.
    eapply _sim_local_call with (uniqs_src:= nil) (uniqs_tgt:= nil) (privs_src:= nil) (privs_tgt:= nil);
      try apply STEPS; try eexact x0; ss; try reflexivity; eauto; try (ii; des; contradiction).
    { s. i. eapply inject_locals_getOperandValue; eauto.
      eapply fully_inject_locals_inject_locals; eauto. }
    { s. i. eapply inject_locals_params2GVs; eauto.
      eapply fully_inject_locals_inject_locals; eauto. }
    s. i.
    exploit return_locals_fully_inject_locals; eauto.
    { eapply fully_inject_locals_inj_incr; eauto. apply INCR. }
    i. des.
    esplits. i. splits; eauto.
    + inv CONF. rewrite <- TARGETDATA. eauto.
    + eapply lift_unlift_le; eauto.
      { apply MEM. }
      { apply MEM. }
    + right. eapply CIH.
      econs; ss; eauto.
      { eapply inject_incr_fully_inject_allocas; eauto.
        ss. inv INCR. ss. }
      { eapply invmem_unlift; eauto. }
      { eapply Forall_harder; [apply VALID_ALLOCAS_SRC|].
        i. ss.
        eapply Pos.lt_le_trans; eauto.
        apply INCR.
      }
      { eapply Forall_harder; [apply VALID_ALLOCAS_TGT|].
        i. ss.
        eapply Pos.lt_le_trans; eauto.
        apply INCR.
      }
  - (* return *)
    exploit get_status_return_inv; eauto. i. des.
    inv SIM. ss. subst.
    exploit nop_cmds_tgt_nil; eauto. intro NOPS.
    rewrite (app_nil_end cmds_src).
    eapply sop_star_sim_local; [by apply nops_sop_star|].
    eapply _sim_local_return; eauto; ss.
    { ss. eapply SoundBase.fully_inject_allocas_inject_allocas; eauto. }
    { reflexivity. }
    i. eapply inject_locals_getOperandValue; eauto.
    eapply fully_inject_locals_inject_locals; eauto.
  - (* return void *)
    exploit get_status_return_void_inv; eauto. i. des.
    inv SIM. ss. subst.
    exploit nop_cmds_tgt_nil; eauto. intro NOPS.
    rewrite (app_nil_end cmds_src).
    eapply sop_star_sim_local; [by apply nops_sop_star|].
    eapply _sim_local_return_void; ss.
    { ss. eapply SoundBase.fully_inject_allocas_inject_allocas; eauto. }
  - clear PROGRESS_TGT.
    inv SIM; ss. move CMDS at bottom.
    unfold get_status in *; ss.
    destruct conf_src; ss.
    inv CONF. ss. clarify.
    des_ifs; ss.
    + eapply nop_cmds_tgt_nil in CMDS.
      hide_goal. econs 5; eauto.
      { ii. admit. (* remove "clear PROGRESS_TGT" above *) }
      i.
      des. expl preservation.
      inv STEP. ss.
      destruct value5; ss; cycle 1.
      {
        esplits.
        - rpapply nops_sop_star; eauto. rewrite app_nil_r. eauto.
        - econs; eauto.
          eapply sBranch; eauto.
          + instantiate (1:= tmn').
            instantiate (2:= ps').
            admit. (* nop_fdef spec *)
          + admit. (* *)
        - reflexivity.
        - right. apply CIH.
          econs; eauto.
          + admit.
          + admit.
      }
      {
        hide_goal. 
        hexploit fully_inject_locals_spec; eauto. rewrite H12. intro INJ.
        unfold lift2_option in *. des_ifsH INJ.
        inv INJ.
        { subst HIDDEN_GOAL0.
          esplits.
          - rpapply nops_sop_star; eauto. rewrite app_nil_r. eauto.
          - econs; eauto.
            eapply sBranch; eauto.
            + instantiate (1:= tmn').
              instantiate (2:= ps').
              admit. (* nop_fdef spec *)
            + admit. (* *)
          - reflexivity.
          - right. apply CIH.
            econs; eauto.
            + admit.
            + admit.
        }
        { subst HIDDEN_GOAL0.
          esplits.
          - rpapply nops_sop_star; eauto. rewrite app_nil_r. eauto.
          - econs; eauto.
            eapply sBranch; eauto.
            ttttttttttttttttttttt
            + instantiate (1:= tmn').
              instantiate (2:= ps').
              admit. (* nop_fdef spec *)
            + admit. (* *)
          - reflexivity.
          - right. apply CIH.
            econs; eauto.
            + admit.
            + admit.
        }
      }
      {
      }
      esplits.
      * rpapply nops_sop_star; eauto. rewrite app_nil_r. eauto.
      * econs; eauto.
        { destruct value5; ss.
          unfold lift2_option in *. des_ifsH INJ.
          inv INJ; ss.
          destruct conds; ss.
          des_ifs.
          destruct value5; ss.
          tttttttttt
          exploit LOCALS; eauto.
          tttttttttttttttttttt
      *
        econs; eauto.

  - (* step *)
    eapply _sim_local_step; swap 2 3.
    { ii. apply H. esplits; eauto. }
    { inv SIM. des. split; ss. }
    i.
    inv SIM. des. ss.
    move CMDS at bottom.
    destruct cmds_tgt; ss.
    { apply nop_cmds_tgt_nil in CMDS.
      destruct conf_src; ss.
      esplits.
      - instantiate (1:= {| EC := {|
                                   CurFunction := fdef_src;
                                   CurBB := (l0, s_src);
                                   CurCmds := [];
                                   Terminator := term;
                                   Locals := locals_src;
                                   Allocas := allocas_src |};
                            ECS := ecs_src;
                            Mem := mem_src |}).
        clear - CMDS.
        ginduction cmds_src; ii; ss.
        unfold is_true in *. des_bool. (* TODO: enhance des_bool *)
        des. destruct a; ss. clear_tac.

        on_leftest_function ltac:(fun x => idtac x).
        on_leftest_function ltac:(fun f => idtac f; generalize f). Undo 1.
        on_leftest_function ltac:(fun f => erewrite (f_equal f)). Undo 1.
        Fail on_leftest_function ltac:(fun f => erewrite f_equal with (f:= constr:(f))).
        Fail on_leftest_function ltac:(fun f => erewrite f_equal with (f:= f)).
        (* TODO: IDK why this fails *)
        rpapply sop_star_cons.
        + rpapply sNop.
        + eapply IHcmds_src; eauto.
        + ss.
      - econs; eauto.
        econs; eauto.
      -
    }
    admit.
    (* exploit get_status_step_inv; eauto. i. des. *)
Admitted.
(* step case *)
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

Lemma nop_sim_fdef
      conf_src conf_tgt
      header
      blocks_src blocks_tgt
      (CONF: inject_conf conf_src conf_tgt)
      (NOP: nop_fdef (fdef_intro header blocks_src) (fdef_intro header blocks_tgt))
      (NOP_FIRST_MATCHES: option_map fst (hd_error blocks_src) = option_map fst (hd_error blocks_tgt)):
  sim_fdef conf_src conf_tgt (fdef_intro header blocks_src) (fdef_intro header blocks_tgt).
Proof.
  ii.
  exploit nop_init; eauto. intro NOP_INIT. des.
  esplits; eauto. i. specialize (NOP_INIT0 WF_TGT).
  apply nop_sim; eauto.
Qed.
