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


Section TRANSL.

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

  Inductive transl_module : forall m_src m_tgt, Prop :=
  | transl_module_intro
      los ndts prods_src prods_tgt
      (TRANSL_PRODUCTS: transl_products prods_src prods_tgt)
    : transl_module (module_intro los ndts prods_src)
                    (module_intro los ndts prods_tgt)
  .

End TRANSL.



Section SIMDEF.

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

  Inductive nop_caller_sim (ec_src ec_tgt: ExecutionContext): Prop :=
  | nop_caller_sim_intro
      c_src cmds_src
      (CMDS_SRC: ec_src.(CurCmds) = c_src :: cmds_src)
      (ISCALL_SRC: Instruction.isCallInst c_src = true)
      c_tgt cmds_tgt
      (CMDS_TGT: ec_tgt.(CurCmds) = c_tgt :: cmds_tgt)
      (ISCALL_TGT: Instruction.isCallInst c_tgt = true)
      (* We may pull out unary reasoning, but there will not be much gain *)
      (* Migrating WF, neither *)
      (RETID: getCallerReturnID c_src = getCallerReturnID c_tgt)
  .

  Inductive nop_state_sim: nat -> State -> State -> Prop :=
  | nop_state_sim_intro
      ec_src ec_tgt
      (EC: nop_state_sim_EC ec_src ec_tgt)
      ecs_src ecs_tgt
      (ECS: list_forall2 nop_state_sim_EC ecs_src ecs_tgt)
      idx
      (IDX: (idx > List.length ec_src.(CurCmds) + List.length ec_tgt.(CurCmds))%nat)
      (CALLER: list_forall2 nop_caller_sim ecs_src ecs_tgt)
      mem
    : nop_state_sim idx
                    (mkState ec_src ecs_src mem)
                    (mkState ec_tgt ecs_tgt mem)
  .

  Inductive nop_conf_sim (conf_src conf_tgt: Config) :=
  | nop_conf_sim_intro
      (CONF: inject_conf conf_src conf_tgt)
      (FUNTABLE: conf_src.(FunTable) = conf_tgt.(FunTable))
      (PRODUCTS: transl_products conf_src.(CurProducts) conf_tgt.(CurProducts))
  .

  Coercion inject_conf_of_nop_conf_sim (conf_src conf_tgt: Config):
    nop_conf_sim conf_src conf_tgt -> inject_conf conf_src conf_tgt
  .
  i. destruct H. assumption.
  (* using inversion yields complex program *)
  Defined.

End SIMDEF.




Section COMMUTES.

  Lemma list_forall2_commutes
        A
        (xs ys: list A)
        P
        (FORALL: list_forall2 P xs ys)
        (COMMUTE: forall x y, P x y -> P y x)
  :
    <<FORALL: list_forall2 P ys xs>>
  .
  Proof.
    ginduction FORALL; ii; ss.
    - econs; eauto.
    - econs; eauto. apply IHFORALL; eauto.
  Qed.

  (* TODO: totally remove list_forall2 *)
  Lemma forall2_eq
        A
        (xs ys: list A)
        P
    :
      <<EQ: list_forall2 P xs ys <-> Forall2 P xs ys>>
  .
  Proof. split; i; ginduction H; ii; ss; econs; eauto. Qed.
  
  Lemma nop_blocks_commutes
        b_src b_tgt
        (BLOCKS: nop_blocks b_src b_tgt)
    :
      <<BLOCKS: nop_blocks b_tgt b_src>>
  .
  Proof.
    apply forall2_eq.
    apply forall2_eq in BLOCKS.
    apply list_forall2_commutes; eauto.
    i. des_ifs. des; clarify.
  Qed.

  Lemma nop_fdef_commutes
        f_src f_tgt
        (FDEF: nop_fdef f_src f_tgt)
    :
      <<FDEF: nop_fdef f_tgt f_src>>
  .
  Proof.
    inv FDEF.
    econs; eauto.
    eapply nop_blocks_commutes; eauto.
  Qed.

  Lemma inject_conf_commutes
        conf_src conf_tgt
        (CONF: inject_conf conf_src conf_tgt)
    :
      <<CONF: inject_conf conf_tgt conf_src>>
  .
  Proof. inv CONF. ss. Qed.

  Lemma transl_product_commutes
        p_src p_tgt
        (PROD: transl_product p_src p_tgt)
    :
      <<PROD: transl_product p_tgt p_src>>
  .
  Proof.
    ginduction PROD; ii; ss.
    - econs; eauto.
    - econs; eauto.
    - econs; eauto.
      apply nop_fdef_commutes; ss.
  Qed.

  Lemma transl_products_commutes
        ps_src ps_tgt
        (PRODS: transl_products ps_src ps_tgt)
    :
      <<PRODS: transl_products ps_tgt ps_src>>
  .
  Proof.
    apply forall2_eq. apply forall2_eq in PRODS.
    apply list_forall2_commutes; eauto.
    i. apply transl_product_commutes; ss.
  Qed.

  Lemma nop_conf_sim_commutes
        conf_src conf_tgt
        (CONF: nop_conf_sim conf_src conf_tgt)
    :
      <<CONF: nop_conf_sim conf_tgt conf_src>>
  .
  Proof.
    inv CONF.
    econs; eauto.
    - apply inject_conf_commutes; ss.
    - apply transl_products_commutes; ss.
  Qed.

  Lemma nop_state_sim_EC_commutes
        st_src st_tgt
        (SIM: nop_state_sim_EC st_src st_tgt)
    :
      <<SIM: nop_state_sim_EC st_tgt st_src>>
  .
  Proof.
    inv SIM.
    econs; ss; eauto.
    - apply nop_fdef_commutes; ss.
    - apply nop_blocks_commutes; ss.
  Qed.

  Lemma nop_caller_sim_commutes
        ec_src ec_tgt
        (SIM: nop_caller_sim ec_src ec_tgt)
    :
      <<SIM: nop_caller_sim ec_tgt ec_src>>
  .
  Proof. inv SIM. econs; try eassumption. ss. Qed.

  Lemma nop_state_sim_commutes
        idx st_src st_tgt
        (SIM: nop_state_sim idx st_src st_tgt)
    :
      <<SIM: nop_state_sim idx st_tgt st_src>>
  .
  Proof.
    inv SIM.
    econs; ss; eauto.
    - apply nop_state_sim_EC_commutes; ss.
    - clear - ECS0.
      ginduction ecs_src; ii; ss.
      + inv ECS0. econs; ss.
      + inv ECS0. econs; eauto.
        apply nop_state_sim_EC_commutes; ss.
    - omega.
    - apply list_forall2_commutes; eauto.
      apply nop_caller_sim_commutes.
  Qed.

End COMMUTES.



Section NOPS.

  (* TODO: Move to Nops.v? *)
  (* I want to somehow isolate proofs on nop. *)
  (* Meta-issue: I also have desire to separate def/proof. Just as we did in this repo's dir *)
  (* How about - "Module Nop" && "Module NopFacts" like set library? *)
  Lemma nop_cmds_pop_both x src tgt
        (NOPCMDS: nop_cmds (x :: src) (x :: tgt)):
    nop_cmds src tgt.
  Proof.
    inv NOPCMDS.
    unfold compose in *.
    destruct (negb (is_nop x)) eqn:T; ss.
    inv H0. auto.
  Qed.

  Lemma nop_cmds_push_both x src tgt
        (NOPCMDS: nop_cmds src tgt):
    nop_cmds (x :: src) (x :: tgt).
  Proof.
    unfold nop_cmds. ss.
    des_ifs.
    f_equal.
    inv NOPCMDS. ss.
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
      (<<SRC: src = nops ++ head :: src_tail>>) /\
      (<<NOPSRC: List.forallb is_nop nops>>) /\
      (<<NOPCMDS': nop_cmds src_tail tail_tgt>>).
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

End NOPS.




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

Lemma nop_state_sim_final
      conf_src conf_tgt
      (CONF: inject_conf conf_src conf_tgt)
      idx0 st_src0 st_tgt0
      (SIM: nop_state_sim idx0 st_src0 st_tgt0)
      g
      (FINAL_TGT: s_isFinialState conf_tgt st_tgt0 = Some g)
  :
    (* TODO: we may state exists -> forall? *)
  exists st_src1,
    <<FINAL_SRC: sop_star conf_src st_src0 st_src1 [] /\
                 s_isFinialState conf_src st_src1 = Some g>>
.
Proof.
  inv SIM. inv EC0. ss. des_ifs_safe ss. des. clarify.
  assert(ecs_tgt = []).
  { des_ifs; ss. } clarify.
  inv ECS0. clear_tac.
  inv CONF. destruct conf_src, conf_tgt; ss. clarify.

  eapply nop_cmds_tgt_nil in CMDS.
  des_ifsH FINAL_TGT.
  - esplits.
    + rpapply nops_sop_star; eauto.
      rewrite app_nil_r. eauto.
    + ss.
  - esplits.
    + rpapply nops_sop_star; eauto.
      rewrite app_nil_r. eauto.
    + ss.
Qed.

Lemma nop_conf_sim_lookup
      conf_src conf_tgt
      (CONF: nop_conf_sim conf_src conf_tgt)
      src_fdef fptr
      (SRC: lookupFdefViaPtr conf_src.(CurProducts) conf_src.(FunTable) fptr =
            Some src_fdef)
  :
    exists tgt_fdef,
      <<TGT: lookupFdefViaPtr conf_tgt.(CurProducts) conf_tgt.(FunTable) fptr =
             Some tgt_fdef>> /\
             <<FDEF: nop_fdef src_fdef tgt_fdef>>
.
Proof.
  inv CONF.
  destruct conf_src, conf_tgt; ss.
  inv CONF0; ss.
  clarify.
  unfold lookupFdefViaPtr in *.
  unfold monad.mbind in *. des_ifs_safe ss.
  clear Heq.
  clear_tac.
  ginduction CurProducts0; ii; ss.
  inv PRODUCTS.
  des_ifs.
  - ss. unfold lookupFdefViaIDFromProduct in *.
    des_ifsH Heq. inv H1.
    inv NOP_FDEF. ss.
    des_ifs_safe.
    esplits; eauto.
    econs; eauto.
  - expl IHCurProducts0.
    ss.
    inv H1; ss.
    + esplits; eauto.
    + esplits; eauto.
    + inv NOP_FDEF. ss. des_ifs.
      esplits; eauto.
Qed.

Lemma nop_conf_sim_lookup_ex_id
      ps_src ps_tgt
      (PRODUCTS: transl_products ps_src ps_tgt)
      i0
  :
    <<EQ: lookupFdecViaIDFromProducts ps_src i0 =
          lookupFdecViaIDFromProducts ps_tgt i0>>
.
Proof.
  ginduction PRODUCTS; ii; ss.
  expl IHPRODUCTS. rewrite IHPRODUCTS0.
  inv H; ss.
Qed.

Lemma nop_conf_sim_lookup_ex
      conf_src conf_tgt
      (CONF: nop_conf_sim conf_src conf_tgt)
      fptr
  :
    <<EQ: lookupExFdecViaPtr conf_tgt.(CurProducts) conf_tgt.(FunTable) fptr =
          lookupExFdecViaPtr conf_src.(CurProducts) conf_src.(FunTable) fptr>>
.
Proof.
  inv CONF.
  destruct conf_src, conf_tgt; ss.
  inv CONF0; ss.
  clarify.
  unfold lookupExFdecViaPtr in *.
  unfold monad.mbind in *. des_ifs_safe ss.
  des_outest_ifsG.
  { hexploit nop_conf_sim_lookup; eauto; revgoals.
    { instantiate (3:= mkCfg _ _ _ _ _). ss.
      i; des.
      unfold lookupFdefViaPtr in *.
      unfold monad.mbind in *.
      rewrite Heq in *.
      rewrite TGT.
      ss. }
    { instantiate (2:= mkCfg _ _ _ _ _). ss.
      unfold lookupFdefViaPtr in *.
      unfold monad.mbind in *.
      rewrite Heq. eauto. }
    { econs; ss; eauto.
      apply transl_products_commutes; ss.
    }
  }
  des_outest_ifsG.
  { exfalso.
    generalize Heq0.
    hexploit nop_conf_sim_lookup; eauto; revgoals.
    { instantiate (3:= mkCfg _ _ _ _ _). ss.
      i; des.
      unfold lookupFdefViaPtr in *.
      unfold monad.mbind in *.
      rewrite Heq in *.
      rewrite TGT in *.
      ss.
    }
    { instantiate (2:= mkCfg _ _ _ _ _). ss.
      unfold lookupFdefViaPtr in *.
      unfold monad.mbind in *.
      rewrite Heq. eauto. }
    { econs; ss; eauto. }
  }
  erewrite nop_conf_sim_lookup_ex_id; eauto.
  apply transl_products_commutes; ss.
Unshelve.
all: try (by ss).
Qed.

Lemma nop_state_sim_step_nops
      conf_src conf_tgt
      (CONF: nop_conf_sim conf_src conf_tgt)
      idx0 st_src0 st_tgt0
      (SIM: nop_state_sim idx0 st_src0 st_tgt0)
      st_tgt1 tr
      (STEP_TGT: sInsn conf_tgt st_tgt0 st_tgt1 tr)
      c cmds_src cmds_tgt
      (HEAD_SRC: st_src0.(EC).(CurCmds) = c :: cmds_src)
      (HEAD_TGT: st_tgt0.(EC).(CurCmds) = c :: cmds_tgt)
      (NOTNOP: is_nop c = false)
  :
    exists st_src1 idx1,
      (<<STEP_SRC: sInsn conf_src st_src0 st_src1 tr>>) /\
      <<SIM: nop_state_sim idx1 st_src1 st_tgt1>>
.
Proof.
  inv SIM. inv EC0. ss. clarify.
  destruct conf_src, conf_tgt; ss. inv CONF. ss. inv CONF0. ss. clarify.
  apply nop_cmds_pop_both in CMDS.
  inv STEP_TGT; ss;
    try (by (esplits; eauto; econs; ss; eauto)).
  - hexploit nop_conf_sim_lookup; eauto; swap 1 2.
    { instantiate (3:= mkCfg _ _ _ _ _). ss. eauto. }
    { instantiate (1:= mkCfg _ _ _ _ _).
      instantiate (3:= CurProducts0).
      econs; ss; eauto.
      apply transl_products_commutes; ss.
    }
    i; des. ss.
    inv FDEF0.
    des_ifs. inv BLOCKS.
    match goal with | [ H: Forall2 _ _ _ |- _ ] => move H at top end.
    des_ifs. des. clarify.
    esplits; eauto.
    + eapply sCall; eauto.
      { ss. }
    + econs; ss; eauto.
      { econs; ss; eauto.
        - econs; ss; eauto.
          econs; ss; eauto.
          apply nop_blocks_commutes; ss.
        - econs; ss; eauto.
      }
      {
        econs; ss; eauto.
        econs; ss; eauto.
        apply nop_cmds_push_both; ss.
      }
      { econs; eauto. econs; ss; eauto. }
  -
    (* hexploit nop_conf_sim_lookup_ex; try apply H16; eauto. *)
    (* { *)
    esplits; eauto.
    eapply sExCall; eauto.
    + Fail erewrite nop_conf_sim_lookup_ex; eauto.
      (* hard to use in erewrite... Can we do more smart? *)
      rewrite <- H16.
      hexploit nop_conf_sim_lookup_ex; revgoals.
      { instantiate (5:= mkCfg _ _ _ _ _). ss.
        instantiate (3:= mkCfg _ _ _ _ _). ss.
        i. eauto. }
      { econs; ss; eauto.
        apply transl_products_commutes; ss. }
    + econs; ss; eauto.
Unshelve.
all: try (by ss).
Qed.

Lemma nop_state_sim_stuck
      conf_src conf_tgt
      (CONF: nop_conf_sim conf_src conf_tgt)
      idx0 st_src0 st_tgt0
      (SIM: nop_state_sim idx0 st_src0 st_tgt0)
      c cmds_src cmds_tgt
      (HEAD_SRC: st_src0.(EC).(CurCmds) = c :: cmds_src)
      (HEAD_TGT: st_tgt0.(EC).(CurCmds) = c :: cmds_tgt)
      (NOTNOP: is_nop c = false)
      (STUCK_TGT: stuck_state conf_tgt st_tgt0)
  :
    <<STUCK_SRC: stuck_state conf_src st_src0>>
.
Proof.
  ii. des. exploit nop_state_sim_step_nops; try apply H; eauto.
  { apply nop_conf_sim_commutes. eauto. }
  { eapply nop_state_sim_commutes. eauto. }
  i; des.
  apply STUCK_TGT. esplits; eauto.
Qed.

Lemma nop_fdef_lookup
      f_src lbl ps cs_src tmn f_tgt
      (FDEF: nop_fdef f_src f_tgt)
      (SRC_LOOKUP: lookupBlockViaLabelFromFdef f_src lbl = Some (stmts_intro ps cs_src tmn))
  :
    exists cs_tgt,
      (<<TGT_LOOKUP: lookupBlockViaLabelFromFdef f_tgt lbl = Some (stmts_intro ps cs_tgt tmn)>>)
      /\
      <<CMDS: nop_cmds cs_src cs_tgt>>
.
Proof.
  inv FDEF. ss. clear_tac.
  ginduction blocks_src; ii; ss.
  des_ifs.
  - clear IHblocks_src. inv BLOCKS.
    des_ifs. des. clarify.
    ss. des_ifs.
    esplits; eauto.
  - inv BLOCKS.
    des_ifs. des. clarify.
    ss. des_ifs.
    hexploit IHblocks_src; eauto.
Qed.

Lemma nop_blocks_get_value
      l1 bb_src bb_tgt
      (BLOCKS: nop_blocks [bb_src] [bb_tgt])
  :
    <<EQ: getValueViaBlockFromValuels l1 bb_src = getValueViaBlockFromValuels l1 bb_tgt>>
.
Proof. inv BLOCKS. des_ifs. des. clarify. Qed.

Lemma nop_blocks_get_incoming_values
      bb_src bb_tgt
      (BLOCKS: nop_blocks [bb_src] [bb_tgt])
  :
    (* TODO: putting forall in premise makes existentials on exploit *)
    (* Can we do exploit more smart to prevent this? *)
    <<EQ: forall TD gs ps lc,
      getIncomingValuesForBlockFromPHINodes TD ps bb_src gs lc =
      getIncomingValuesForBlockFromPHINodes TD ps bb_tgt gs lc>>
.
Proof.
  ii.
  inv BLOCKS. des_ifs. des. clarify.
  match goal with | [ H: Forall2 _ [] [] |- _ ] => clear H end.
  ginduction ps; ii; ss.
  des_ifs_safe. clear_tac.
  assert(EQ: getValueViaBlockFromValuels l0 (l1, stmts_intro phinodes0 cmds5 terminator0)
         = getValueViaBlockFromValuels l0 (l1, stmts_intro phinodes0 cmds0 terminator0)).
  { erewrite <- nop_blocks_get_value; eauto.
    econs; eauto. splits; ss. }
  rewrite EQ.
  expl IHps. rewrite IHps0. des_ifs.
Qed.

Lemma nop_blocks_switch
      cs_src cs_tgt
      (CMDS: nop_cmds cs_src cs_tgt)
      bb_src bb_tgt
      (BLOCKS: nop_blocks [bb_src] [bb_tgt])
      TD lbl ps tmn
      gs lc lc'
      (SWITCH_SRC: switchToNewBasicBlock TD (lbl, stmts_intro ps cs_src tmn) bb_src gs lc =
                   Some lc')
  :
    <<SWITCH_TGT: switchToNewBasicBlock TD (lbl, stmts_intro ps cs_tgt tmn) bb_tgt gs lc =
                   Some lc'>>
.
Proof.
  unfold switchToNewBasicBlock in *.
  ss.
  des_ifs_safe ss. clarify. clear_tac.
  ginduction ps; ii; ss.
  - clarify.
  - des_ifs_safe ss. clarify.
    hexploit nop_blocks_get_incoming_values; eauto; []; intro INCOMING; des.
    inv BLOCKS. des_ifs_safe ss. des. clarify.
    match goal with | [ H: Forall2 _ [] [] |- _ ] => clear H end.
    unfold getValueViaBlockFromValuels in *. ss.
    des_ifs_safe. clear_tac.
    erewrite <- INCOMING.
    rewrite Heq3. (* TODO: rewriter tactic *)
    ss.
Qed.

Lemma nop_state_sim_term_step_nops
      conf_src conf_tgt
      (CONF: inject_conf conf_src conf_tgt)
      idx0 st_src0 st_tgt0
      (SIM: nop_state_sim idx0 st_src0 st_tgt0)
      st_tgt1 tr
      (STEP_TGT: sInsn conf_tgt st_tgt0 st_tgt1 tr)
      (HEAD_SRC: st_src0.(EC).(CurCmds) = [])
      (HEAD_TGT: st_tgt0.(EC).(CurCmds) = [])
  :
    exists st_src1 idx1,
      (<<STEP_SRC: sInsn conf_src st_src0 st_src1 tr>>) /\
      <<SIM: nop_state_sim idx1 st_src1 st_tgt1>>
.
Proof.
  apply nop_state_sim_commutes in SIM. des.
  (* TODO: I want to change src/tgt of nop_state_sim in goal too. *)
  (* Smarter way to do this? *)
  assert(exists (st_src1 : State) (idx1 : nat),
            sInsn conf_src st_src0 st_src1 tr  /\ nop_state_sim idx1 st_tgt1 st_src1); cycle 1.
  { des. esplits; eauto. eapply nop_state_sim_commutes; eauto. }
  inv SIM. inv EC0. ss. clarify.
  destruct conf_src, conf_tgt; ss. inv CONF. ss. clarify.
  clear CMDS. clear_tac.
  inv STEP_TGT; ss.
  - inv CALLER. inv H1. ss. clarify. destruct b1; ss. clarify.
    inv ECS0. inv H2.
    assert(c_src = c_tgt).
    { unfold nop_cmds in *. ss.
      destruct c_src; ss.
      destruct c_tgt; ss.
      clarify. } clarify.
    esplits.
    rpapply sReturn; eauto.
    econs; ss; eauto.
    econs; ss; eauto.
    eapply nop_cmds_pop_both; eauto.
  - inv CALLER. inv H1. ss. clarify. destruct b1; ss. clarify.
    inv ECS0. inv H2.
    assert(c_src = c_tgt).
    { unfold nop_cmds in *. ss.
      destruct c_src; ss.
      destruct c_tgt; ss.
      clarify. } clarify.
    esplits.
    rpapply sReturnVoid; eauto.
    econs; ss; eauto.
    econs; ss; eauto.
    eapply nop_cmds_pop_both; eauto.
  - expl nop_fdef_lookup.
    expl nop_blocks_switch.
    esplits; eauto.
    rpapply sBranch; eauto.
    do 3 (econs; ss; eauto).
  - expl nop_fdef_lookup.
    expl nop_blocks_switch.
    esplits; eauto.
    rpapply sSwitch; eauto.
    do 3 (econs; ss; eauto).
  - expl nop_fdef_lookup.
    expl nop_blocks_switch.
    esplits; eauto.
    rpapply sBranch_uncond; eauto.
    do 3 (econs; ss; eauto).
Qed.

Lemma nop_state_sim_term_stuck
      conf_src conf_tgt
      (CONF: inject_conf conf_src conf_tgt)
      idx0 st_src0 st_tgt0
      (SIM: nop_state_sim idx0 st_src0 st_tgt0)
      (HEAD_SRC: st_src0.(EC).(CurCmds) = [])
      (HEAD_TGT: st_tgt0.(EC).(CurCmds) = [])
      (STUCK_TGT: stuck_state conf_tgt st_tgt0)
  :
    <<STUCK_SRC: stuck_state conf_src st_src0>>
.
Proof.
  ii. des. exploit nop_state_sim_term_step_nops; try apply H; eauto.
  { apply inject_conf_commutes; eauto. }
  { eapply nop_state_sim_commutes. eauto. }
  i; des.
  apply STUCK_TGT. esplits; eauto.
Qed.

Lemma nop_sim
      conf_src conf_tgt
      (CONF: nop_conf_sim conf_src conf_tgt)
  :
  (nop_state_sim) <3= (sim conf_src conf_tgt)
.
Proof.
  s.
  pcofix CIH. intros idx0 st_src0 st_tgt0 SIM. pfold.

  destruct (s_isFinialState conf_tgt st_tgt0) eqn:FINAL_TGT.
  { expl nop_state_sim_final (try apply CONF; eauto).
    eapply _sim_exit; eauto.
  }

  {
    inv SIM. inv EC0. ss.
    (* inv SIM. inv EC0. ss. inv BB. des_ifs_safe ss. des. clarify. clear H4. *)
    destruct (classic (option_map (is_nop) (head cmds_tgt) = Some true)).
    { destruct cmds_tgt; ss. clarify. destruct c; ss. clear_tac.
      eapply _sim_step; eauto.
      { ii. apply H. esplits; eauto. destruct conf_tgt. econs; eauto. }
      i. inv STEP. esplits; eauto.
      - eapply sInsn_stutter. eauto.
      - right. apply CIH.
        econs; ss; eauto.
        omega.
        (* econs; ss; eauto. *)
        (* econs; ss; eauto. *)
    }
    destruct cmds_tgt; ss.
    { clear H. (* enhance clear_tac *)
      apply nop_cmds_tgt_nil in CMDS.
      destruct (classic (stuck_state
                           conf_tgt (mkState
                                       (mkEC f_tgt bb_tgt [] term lc als)
                                       ecs_tgt mem0))).
      {
        match goal with | [ H: context[stuck_state] |- _] => rename H into STUCK end.
        eapply _sim_error.
        - rpapply nops_sop_star; eauto.
          rewrite app_nil_r. ss.
        - econs; eauto.
          + eapply nop_state_sim_term_stuck; try apply STUCK; eauto.
            { apply CONF. }
            { econs; ss; eauto. }
          + ss.
            destruct conf_src, conf_tgt; ss. inv CONF. ss. inv CONF0. ss. clarify.
            des_ifs.
            { inv ECS0. }
            { inv ECS0. }
      }
      {
        eapply _sim_step; eauto.
        i.
        hexploit nop_state_sim_term_step_nops; try apply STEP.
        { apply CONF. }
        { instantiate (1:= (mkState
                              (mkEC f_src bb_src [] term lc als)
                              ecs_src mem0)).
          econs; ss; eauto.
        }
        { ss. }
        { ss. }
        i; des.
        esplits.
        - rpapply nops_sop_star; eauto.
          rewrite app_nil_r. ss.
        - econs; eauto.
        - right. apply CIH.
          eauto.
      }
    }
    {
      hexploit nop_cmds_tgt_non_nop; eauto.
      { destruct c; ss. }
      i; des. clarify.
      destruct (classic (stuck_state
                           conf_tgt (mkState
                                       (mkEC f_tgt bb_tgt (c :: cmds_tgt) term lc als)
                                       ecs_tgt mem0))).
      {
        match goal with | [ H: context[stuck_state] |- _] => rename H into STUCK end.
        eapply _sim_error.
        - rpapply nops_sop_star; eauto.
        - econs; eauto.
          eapply nop_state_sim_stuck; try apply STUCK; ss; eauto.
          { econs; ss; eauto.
            econs; ss; eauto.
            eapply nop_cmds_push_both; eauto.
          }
          { destruct c; ss. }
      }
      {
        eapply _sim_step; eauto.
        i.
        hexploit nop_state_sim_step_nops; try apply STEP.
        { instantiate (1:= conf_src). ss. }
        { instantiate (1:= (mkState
                              (mkEC f_src bb_src (c :: src_tail) term lc als)
                              ecs_src mem0)).
          econs; ss; eauto. econs; ss; eauto.
          eapply nop_cmds_push_both; eauto.
        }
        { ss. }
        { ss. }
        { destruct c; ss. }
        i; des.
        esplits.
        - rpapply nops_sop_star; eauto.
        - econs; eauto.
        - right. apply CIH.
          eauto.
      }
    }
  }
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
    - econs; eauto.
  }
Qed.
