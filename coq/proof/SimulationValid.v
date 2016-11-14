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
Require Import Decs.
Require Import Hints.
Require Import Validator.
Require Import GenericValues.
Require Import TODOProof.
Require Import PropOpsem.
Require Import SimulationLocal.
Require Import Simulation.
Require Import AdequacyLocal.
Require Import Inject.
Require InvMem.
Require InvState.
Require Import PropValid.
Require Import SoundBase.
Require Import SoundImplies.
Require Import SoundPostcondCmd.
Require Import SoundPostcondCall.
Require Import SoundPostcondPhinodes.
Require Import SoundInfrules.
Require Import SoundReduceMaydiff.

Set Implicit Arguments.


Inductive valid_state_sim
          (conf_src conf_tgt:Config)
          (stack0_src stack0_tgt:ECStack)
          (invmem:InvMem.Rel.t)
          (idx:nat)
          (st_src st_tgt:State): Prop :=
| valid_state_sim_intro
    m_src m_tgt
    fdef_hint cmds_hint
    inv inv_term
    invst
    (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
    (ECS_SRC: st_src.(ECS) = stack0_src)
    (ECS_TGT: st_tgt.(ECS) = stack0_tgt)
    (FDEF: valid_fdef m_src m_tgt st_src.(EC).(CurFunction) st_tgt.(EC).(CurFunction) fdef_hint)
    (LABEL: st_src.(EC).(CurBB).(fst) = st_tgt.(EC).(CurBB).(fst))
    (CMDS: valid_cmds m_src m_tgt st_src.(EC).(CurCmds) st_tgt.(EC).(CurCmds) cmds_hint inv = Some inv_term)
    (TERM: valid_terminator fdef_hint inv_term m_src m_tgt
                            st_src.(EC).(CurFunction).(get_blocks)
                            st_tgt.(EC).(CurFunction).(get_blocks)
                            st_src.(EC).(CurBB).(fst)
                            st_src.(EC).(Terminator)
                            st_tgt.(EC).(Terminator))
    (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
    (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
.

Lemma valid_init
      m_src m_tgt
      conf_src conf_tgt
      stack0_src stack0_tgt
      fdef_src fdef_tgt
      fdef_hint
      args_src args_tgt
      mem_src mem_tgt
      inv idx
      ec_src
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint)
      (ARGS: list_forall2 (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) args_src args_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (INIT_SRC: init_fdef conf_src fdef_src args_src ec_src):
  exists ec_tgt,
    <<INIT_TGT: init_fdef conf_tgt fdef_tgt args_tgt ec_tgt>> /\
    <<SIM:
      valid_state_sim
        conf_src conf_tgt
        stack0_src stack0_tgt
        inv idx
        (mkState ec_src stack0_src mem_src)
        (mkState ec_tgt stack0_tgt mem_tgt)>>.
Proof.
  inv INIT_SRC. unfold valid_fdef in FDEF. simtac.
  exploit locals_init; eauto; [by apply CONF|]. i. des.
  generalize FDEF. i.
  unfold forallb2AL in FDEF0. ss. apply andb_true_iff in FDEF0. des. simtac.
  hexploit InvState.Rel.sem_empty; eauto.
  { instantiate (2 := mkEC _ _ _ _ _ _).
    instantiate (1 := mkEC _ _ _ _ _ _).
    s. eauto.
  }
  i. des.
  esplits.
  - econs; eauto. ss.
  - econs; eauto. ss.
    repeat
      (try match goal with
           | [|- is_true (if ?c then _ else _)] =>
             let COND := fresh "COND" in
             destruct c eqn:COND
           end;
       simtac).
    { match goal with
      | [H: proj_sumbool (fheader_dec ?a ?a) = false |- _] => destruct (fheader_dec a a); ss
      end.
    }
    apply andb_true_iff. splits; [|by eauto].
    repeat
      (try match goal with
           | [|- (if ?c then _ else _) = true] =>
             let COND := fresh "COND" in
             destruct c eqn:COND
           end;
       simtac).
    { match goal with
      | [H: proj_sumbool (id_dec ?a ?a) = false |- _] => destruct (id_dec a a); ss
      end.
    }
    rewrite COND0, COND1, COND2, COND3, COND4. ss.
Qed.

Lemma valid_sim
      conf_src conf_tgt:
  (valid_state_sim conf_src conf_tgt) <6= (sim_local conf_src conf_tgt).
Proof.
  intros stack0_src stack0_tgt.
  pcofix CIH.
  intros inv0 idx0 st_src st_tgt SIM. pfold.
  apply _sim_local_src_error. i.
  destruct st_src, st_tgt. destruct EC0, EC1.
  inv SIM. ss.
  destruct CurCmds0; simtac;
    (try by exfalso; eapply has_false_False; eauto).
  - (* term *)
    unfold valid_terminator in TERM.
    simtac;
      (try by exfalso; eapply has_false_False; eauto).
    destruct Terminator0, Terminator1; simtac.
    + (* return *)
      eapply _sim_local_return; eauto; ss.
      i. exploit InvState.Rel.inject_value_spec; eauto.
      { rewrite InvState.Unary.sem_valueT_physical. eauto. }
      i. des. rewrite InvState.Unary.sem_valueT_physical in VAL_TGT. ss.
      esplits; eauto.
    + (* return_void *)
      eapply _sim_local_return_void; eauto; ss.
    + (* br *)
      exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
      rewrite <- (ite_spec decision l0 l3) in *. simtac.
      exploit InvState.Rel.inject_value_spec; eauto.
      { rewrite InvState.Unary.sem_valueT_physical. eauto. }
      rewrite InvState.Unary.sem_valueT_physical. s. i. des.
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP. unfold valid_phinodes in *.
      do 12 simtac0. rewrite <- (ite_spec decision0 l0 l3) in *. simtac.
      rewrite VAL_TGT in H16. inv H16.
      exploit decide_nonzero_inject_aux; eauto.
      { inv CONF. inv INJECT0. ss. subst. eauto. }
      i. subst.
      exploit add_terminator_cond_br; eauto. i. des.
      rewrite lookupBlockViaLabelFromFdef_spec in *.
      exploit (lookupAL_ite fdef_hint decision0 l0 l3); eauto. clear COND7 COND3. i.
      exploit (lookupAL_ite CurFunction0.(get_blocks) decision0 l0 l3); eauto. clear COND8 COND4. i.
      exploit (lookupAL_ite CurFunction1.(get_blocks) decision0 l0 l3); eauto. clear COND9 COND5. i.
      idtac.
      unfold l in H14. rewrite x2 in H14. inv H14.
      unfold l in H18. rewrite x3 in H18. inv H18.
      destruct decision0; inv H0; inv H1; ss.
      * exploit postcond_phinodes_sound;
          (try instantiate (1 := (mkState (mkEC _ _ _ _ _ _) _ _))); s;
            (try eexact x0; try eexact MEM);
            (try eexact H19; try eexact H15); ss; eauto.
        i. des.
        exploit apply_infrules_sound; try exact STATE0; eauto; ss. i. des.
        exploit reduce_maydiff_sound; eauto; ss. i. des.
        exploit implies_sound; try exact COND2; eauto; ss. i. des.
        exploit valid_fdef_valid_stmts; eauto. i. des.
        esplits; eauto.
        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        { right. apply CIH. econs; ss; eauto; ss; eauto. }
      * exploit postcond_phinodes_sound;
          (try instantiate (1 := (mkState (mkEC _ _ _ _ _ _) _ _))); s;
            (try eexact x0; try eexact MEM);
            (try eexact H19; try eexact H15); ss; eauto.
        i. des.
        exploit apply_infrules_sound; try exact STATE0; eauto; ss. i. des.
        exploit reduce_maydiff_sound; eauto; ss. i. des.
        exploit implies_sound; try exact COND11; eauto; ss. i. des.
        exploit valid_fdef_valid_stmts; eauto. i. des.
        esplits; eauto.
        { econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss. }
        { right. apply CIH. econs; ss; eauto; ss; eauto. }
    + (* br_uncond *)
      exploit nerror_nfinal_nstuck; eauto. i. des. inv x0. simtac.
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP. unfold valid_phinodes in *. simtac.
      rewrite add_terminator_cond_br_uncond in *.
      rewrite lookupBlockViaLabelFromFdef_spec in *.
      rewrite COND2 in H10. inv H10.
      rewrite COND3 in H12. inv H12.
      exploit postcond_phinodes_sound;
        (try instantiate (1 := (mkState (mkEC _ _ _ _ _ _) _ _))); s;
        (try eexact COND4; try eexact MEM);
        (try eexact H11; try eexact H13); ss; eauto.
      i. des.
      exploit apply_infrules_sound; eauto; ss. i. des.
      exploit reduce_maydiff_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      exploit valid_fdef_valid_stmts; eauto. i. des.
      esplits; eauto.
      * econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss.
      * right. apply CIH. econs; ss; eauto; ss; eauto.
    + (* switch *)
      destruct (list_const_l_dec l0 l1); ss. subst.
      exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
      exploit InvState.Rel.inject_value_spec; eauto.
      { rewrite InvState.Unary.sem_valueT_physical. eauto. }
      rewrite InvState.Unary.sem_valueT_physical. s. i. des.
      exploit get_switch_branch_inject; eauto. i.
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP.
      assert (CONF_EQ: TD0 = TD /\ gl0 = gl).
      { inv CONF.
        match goal with
        | [INJ: inject_conf _ _ |- _] => inv INJ
        end. ss. }
      des. subst. ss. clarify.
      unfold valid_phinodes in *. simtac.
      exploit add_terminator_cond_switch; eauto. i. des.
      rewrite lookupBlockViaLabelFromFdef_spec in *.

      rewrite forallb_forall in COND2.
      exploit get_switch_branch_in_successors; eauto.
      i. unfold successors_terminator in *.
      apply nodup_In in x2. ss. des.
      { (* default *)
        subst.
        rewrite COND4 in H15. inv H15.
        rewrite COND5 in H19. inv H19.
        exploit postcond_phinodes_sound; try exact x1; eauto.
        { rewrite <- LABEL. eauto. }
        i. des.
        exploit apply_infrules_sound; eauto; ss. i. des.
        exploit reduce_maydiff_sound; eauto; ss. i. des.
        exploit implies_sound; eauto; ss. i. des.
        exploit implies_sound; eauto; ss. i. des.
        exploit valid_fdef_valid_stmts; eauto. i. des.
        esplits; eauto.
        * econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss.
        * right. apply CIH. econs; ss; eauto; ss; eauto.
      }
      { (* case *)
        apply list_prj2_inv in x2. des.
        exploit COND2; eauto. i.
        des_ifs. simtac. clear COND2.
        rewrite <- H15 in Heq1. inv Heq1.
        rewrite <- H19 in Heq2. inv Heq2.
        clear dependent phinodes5.
        clear dependent phinodes0.
        exploit postcond_phinodes_sound; try exact x1; eauto.
        { rewrite <- LABEL. eauto. }
        i. des.
        exploit apply_infrules_sound; eauto; ss. i. des.
        exploit reduce_maydiff_sound; eauto; ss. i. des.
        exploit implies_sound; eauto; ss. i. des.
        exploit implies_sound; eauto; ss. i. des.
        exploit valid_fdef_valid_stmts; eauto. i. des.
        esplits; eauto.
        * econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss.
        * right. apply CIH. econs; ss; eauto; ss; eauto.
      }
    + (* unreachable *)
      exploit nerror_nfinal_nstuck; eauto. i. des. inv x0.
  - (* cmd *)
    destruct (Instruction.isCallInst c) eqn:CALL.
    + (* call *)
      exploit postcond_cmd_is_call; eauto. i.
      destruct c; ss. destruct c0; ss.
      hexploit postcond_call_sound; try exact COND; eauto;
        (try instantiate (2 := (mkState (mkEC _ _ _ _ _ _) _ _))); ss; eauto; ss.
      i. des. subst. do 24 simtac0. des.
      eapply _sim_local_call; ss; eauto; ss.
      exists (memory_blocks_of conf_src Locals0
                          (Invariant.unique (Invariant.src inv))),
        (memory_blocks_of conf_tgt Locals1
                          (Invariant.unique (Invariant.tgt inv))).
      esplits.
      { inv STATE. inv SRC.
        unfold memory_blocks_of. ii.
        exploit filter_map_inv; eauto. i. des.
        des_ifs.
        exploit UNIQUE.
        { apply AtomSetFacts.elements_iff, InA_iff_In. eauto. }
        intro UNIQUE_A. inv UNIQUE_A. ss. clarify.
        exploit MEM0; eauto.
        unfold InvState.Unary.sem_diffblock. des_ifs.
      }
      { inv STATE. inv TGT.
        unfold memory_blocks_of. ii.
        exploit filter_map_inv; eauto. i. des.
        des_ifs.
        exploit UNIQUE.
        { apply AtomSetFacts.elements_iff, InA_iff_In. eauto. }
        intro UNIQUE_A. inv UNIQUE_A. ss. clarify.
        exploit MEM0; eauto.
        unfold InvState.Unary.sem_diffblock. des_ifs.
      }
      i. exploit RETURN; eauto. i. des.
      exploit apply_infrules_sound; eauto; ss. i. des.
      exploit reduce_maydiff_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      exists locals2_tgt, 0%nat, invmem1. splits; ss.
      * etransitivity; eauto.
      * right. apply CIH. econs; eauto.
    + (* non-call *)
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i.
      exploit postcond_cmd_is_call; eauto. i. rewrite CALL in x0.
      exploit sInsn_non_call; eauto; try congruence. i. des. subst. ss.
      exploit postcond_cmd_sound; eauto; ss; try congruence. i. des.
      exploit sInsn_non_call; eauto; try congruence. i. des. subst. ss.
      exploit apply_infrules_sound; eauto; ss. i. des.
      exploit reduce_maydiff_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      esplits; (try by etransitivity; eauto); eauto.
      { econs 1. eauto. }
      right. apply CIH. econs; try exact x1; eauto.
Admitted.

Lemma valid_sim_fdef
      m_src m_tgt
      conf_src conf_tgt
      fdef_src fdef_tgt
      fdef_hint
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint):
  sim_fdef conf_src conf_tgt fdef_src fdef_tgt.
Proof.
  ii.
  exploit valid_init; eauto. i. des.
  esplits; eauto.
  apply valid_sim; eauto.
Grab Existential Variables.
  { exact 0%nat. }
Qed.

Lemma valid_products_lookupFdefViaIDFromProducts
      m_hint m_src m_tgt
      products_src products_tgt
      f fdef_src
      (PRODUCTS: valid_products m_hint m_src m_tgt products_src products_tgt)
      (SRC: lookupFdefViaIDFromProducts products_src f = Some fdef_src):
  exists fdef_tgt,
    <<TGT: lookupFdefViaIDFromProducts products_tgt f = Some fdef_tgt>> /\
    <<FDEF: valid_product m_hint m_src m_tgt (product_fdef fdef_src) (product_fdef fdef_tgt)>>.
Proof.
  revert products_tgt PRODUCTS SRC.
  induction products_src; [done|].
  i. destruct products_tgt; [done|].
  unfold valid_products in PRODUCTS. s in PRODUCTS. apply andb_true_iff in PRODUCTS. des.
  s in SRC. simtac.
  - destruct a, p; simtac. esplits; eauto.
    + destruct (getFdefID fdef0 == getFdefID fdef_src); eauto. congruence.
    + destruct (id_dec (getFdefID fdef_src) (getFdefID fdef0)); ss.
      destruct (valid_fdef m_src m_tgt fdef_src fdef0 f0) eqn:FDEF; ss. congruence.
  - destruct a, p; simtac. congruence.
  - exploit IHproducts_src; eauto. i. des.
    esplits; eauto.
    destruct (lookupFdefViaIDFromProduct p f) eqn:HD; ss.
    destruct a, p; simtac.
  - exploit IHproducts_src; eauto. i. des.
    esplits; eauto.
    destruct (lookupFdefViaIDFromProduct p f) eqn:HD; ss.
    destruct a, p; simtac.
Qed.

Lemma valid_products_genGlobalAndInitMem
      layouts namedts
      hint
      products0_src products_src
      products0_tgt products_tgt
      globals locals mem
      (PRODUCTS: valid_products
                   hint
                   (module_intro layouts namedts products0_src)
                   (module_intro layouts namedts products0_tgt)
                   products_src products_tgt):
  genGlobalAndInitMem (layouts, namedts) products_src globals locals mem =
  genGlobalAndInitMem (layouts, namedts) products_tgt globals locals mem.
Proof.
  revert products_tgt globals locals mem PRODUCTS.
  induction products_src; i; destruct products_tgt; ss.
  unfold valid_products in PRODUCTS. ss. apply andb_true_iff in PRODUCTS. des.
  destruct a, p; simtac.
  - apply Decs.gvar_eqb_spec in COND. subst.
    destruct gvar0; ss.
    + destruct (initGlobal (layouts, namedts) globals mem0 id5 typ5 const5 align5) as [[]|]; eauto.
    + destruct (getExternalGlobal mem0 id5); eauto.
  - eqbtac.
    destruct fdec0. destruct fheader5.
    destruct (initFunTable mem0 id5); eauto.
  - destruct fdef5, fdef0; ss.
    destruct fheader5, fheader0; ss. subst.
    destruct (initFunTable mem0 id0); eauto.
Qed.

Lemma valid_sim_module m_hint:
  (fun p q => valid_module m_hint p q = Some true) <2= sim_module.
Proof.
  s. intros module_src module_tgt MODULE.
  unfold valid_module in MODULE. simtac.
  ii. unfold s_genInitState in SRC. simtac.
  clear COND0 e0. apply infrastructure_props.InProductsB_In in e.
  exploit valid_products_lookupFdefViaIDFromProducts; eauto. i. des. simtac.
  destruct fheader5. inv e0. ss.
  esplits.
  - unfold s_genInitState. ss. rewrite TGT.
    match goal with
    | [|- context [productInModuleB_dec ?a ?b]] => destruct (productInModuleB_dec a b)
    end; simtac; cycle 1.
    { apply infrastructure_props.lookupFdefViaIDFromProducts_inv in TGT. congruence. }
    unfold initTargetData in *.
    erewrite <- valid_products_genGlobalAndInitMem; eauto. rewrite COND2.
    rewrite COND3. eauto.
  - apply sim_local_lift_sim. econs; ss.
    + econs.
    + generalize H0. i.
      unfold forallb2AL in H1. ss. apply andb_true_iff in H1. des. simtac.
      hexploit InvState.Rel.sem_empty; eauto.
      { admit. (* init_locals inject_locals *) }
      i. des.
      apply valid_sim. econs; eauto.
      * ss.
      * (* TODO: reorganize tactics *)
        repeat
          (try match goal with
               | [|- is_true (if ?c then _ else _)] =>
                 let COND := fresh "COND" in
                 destruct c eqn:COND
               end;
           simtac).
        { match goal with
          | [H: proj_sumbool (fheader_dec ?a ?a) = false |- _] => destruct (fheader_dec a a); ss
          end.
        }
        apply andb_true_iff. splits; [|by eauto].
        repeat
          (try match goal with
               | [|- (if ?c then _ else _) = true] =>
                 let COND := fresh "COND" in
                 destruct c eqn:COND
               end;
           simtac).
        { match goal with
          | [H: proj_sumbool (id_dec ?a ?a) = false |- _] => destruct (id_dec a a); ss
          end.
        }
        rewrite COND5, COND6, COND7, COND8, COND9. ss.
      * ss. admit. (* InvMem.Rel.sem init_mem *)
Admitted.
