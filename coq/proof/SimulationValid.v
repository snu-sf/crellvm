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
Require Import SimulationLocal.
Require Import Simulation.
Require Import Inject.
Require InvMem.
Require InvState.
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
    (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
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
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
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

(* TODO: position *)
Lemma if_f
      A B (c:bool) (f:A -> B) a b:
  (if c then f a else f b) = f (if c then a else b).
Proof. destruct c; ss. Qed.

(* TODO: position *)
Lemma inject_decide_nonzero
      TD inv
      val_src decision_src
      val_tgt decision_tgt
      (INJECT: genericvalues_inject.gv_inject inv val_src val_tgt)
      (SRC: decide_nonzero TD val_src decision_src)
      (TGT: decide_nonzero TD val_tgt decision_tgt):
  decision_src = decision_tgt.
Proof.
  inv SRC. inv TGT. unfold GV2int in *.
  destruct val_src; ss. destruct p, v, val_src; ss.
  destruct val_tgt; ss. destruct p, v, val_tgt; ss.
  simtac. inv INJECT. inv H1.
  apply inj_pair2 in H2. apply inj_pair2 in H4. subst. ss.
Qed.

(* TODO: position *)
Lemma sInsn_non_call
      conf fdef bb cmd cmds term locals1 allocas1 ecs mem1
      st2 event
      (NONCALL: ~ Instruction.isCallInst cmd)
      (STEP: sInsn
               conf
               (mkState (mkEC fdef bb (cmd::cmds) term locals1 allocas1) ecs mem1)
               st2
               event):
  exists locals2 allocas2 mem2,
    st2 = mkState (mkEC fdef bb cmds term locals2 allocas2) ecs mem2.
Proof.
  inv STEP; eauto. ss. congruence.
Qed.

(* TODO: position *)
Lemma postcond_cmd_is_call
      c_src c_tgt inv1 inv2
      (POSTCOND: Postcond.postcond_cmd c_src c_tgt inv1 = Some inv2):
  Instruction.isCallInst c_src = Instruction.isCallInst c_tgt.
Proof.
  destruct c_src, c_tgt; ss.
Qed.

(* TODO: position *)
Lemma valid_fdef_valid_stmts
      m_src m_tgt fdef_src fdef_tgt fdef_hint l
      phinodes_src cmds_src terminator_src
      phinodes_tgt cmds_tgt terminator_tgt
      stmts_hint
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint)
      (SRC: lookupAL stmts (get_blocks fdef_src) l = Some (stmts_intro phinodes_src cmds_src terminator_src))
      (TGT: lookupAL stmts (get_blocks fdef_tgt) l = Some (stmts_intro phinodes_tgt cmds_tgt terminator_tgt))
      (HINT: lookupAL _ fdef_hint l = Some stmts_hint):
  exists inv_term,
    <<CMDS: valid_cmds m_src m_tgt cmds_src cmds_tgt
                       stmts_hint.(Hints.ValidationHint.cmds)
                       stmts_hint.(ValidationHint.invariant_after_phinodes) =
            Some inv_term>> /\
    <<TERM: valid_terminator fdef_hint inv_term m_src m_tgt
                             fdef_src.(get_blocks) fdef_tgt.(get_blocks)
                             l terminator_src terminator_tgt>>.
Proof.
Admitted.

Lemma valid_sim
      conf_src conf_tgt:
  (valid_state_sim conf_src conf_tgt) <6= (sim_local conf_src conf_tgt).
Proof.
  intros stack0_src stack0_tgt.
  pcofix CIH.
  intros inv0 idx0 st_src st_tgt SIM. pfold.
  generalize (classic (stuck_state conf_src st_src)). intro STUCK_SRC. des.
  { destruct (s_isFinialState conf_src st_src) eqn:FINAL_SRC; cycle 1.
    - (* error *)
      eapply _sim_local_error; eauto. econs; eauto.
    - (* final *)
      admit.
  }
  destruct st_src, st_tgt. destruct EC0, EC1.
  inv SIM. ss.
  destruct CurCmds0; simtac;
    (try by exfalso; eapply has_false_False; eauto).
  - (* term *)
    unfold valid_terminator in TERM.
    simtac;
      (try by exfalso; eapply has_false_False; eauto).
    apply NNPP in STUCK_SRC. des.
    inv STUCK_SRC; destruct Terminator1; ss.
    (* TODO: switch case *)
    + (* return *)
      simtac.
      unfold returnUpdateLocals in *. simtac.
      exploit InvState.Rel.inject_value_spec; eauto.
      { rewrite InvState.Unary.sem_valueT_physical. eauto. }
      rewrite InvState.Unary.sem_valueT_physical. s. i. des.
      eapply _sim_local_return; eauto; ss.
    + (* return_void *)
      simtac.
      eapply _sim_local_return_void; eauto; ss.
    + (* br *)
      rewrite <- (ite_spec decision l1 l2) in *. simtac. rewrite ite_spec in *.
      exploit InvState.Rel.inject_value_spec; eauto.
      { rewrite InvState.Unary.sem_valueT_physical. eauto. }
      rewrite InvState.Unary.sem_valueT_physical. s. i. des.
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP. ss.
      rewrite VAL_TGT in H16. inv H16.
      inv CONF. inv INJECT0. ss. subst.
      exploit inject_decide_nonzero; eauto. i. subst.
      (* assert (PHINODES: *)
      (*           valid_phinodes fdef_hint inv_term m_src m_tgt *)
      (*                          (get_blocks CurFunction0) (get_blocks CurFunction1) *)
      (*                          (fst CurBB0) (if decision0 then l0 else l3)) *)
      (*   by (destruct decision0; ss). *)
      (* clear COND1 COND2. *)
      (* unfold valid_phinodes in *. *)
      (* rewrite <- (ite_spec decision0 l0 l3) in *. *)
      (* simtac. unfold Postcond.postcond_phinodes in *. simtac. *)
      (* rewrite ite_spec in *. *)
      (* (* TODO: Lemma sound_postcond_phinodes *) *)
      (* esplits; eauto. *)
      (* { econs 1. econs; eauto. } *)
      (* { reflexivity. } *)
      (* right. apply CIH. *)
      (* instantiate (1 := mkState _ _ _). *)
      (* instantiate (3 := mkEC _ _ _ _ _ _). *)
      (* econs; ss; eauto. *)
      (* * admit. (* valid_cmds *) *)
      (* * admit. (* valid_terminator *) *)
      (* * admit. (* InvState.Rel.sem *) *)
      admit.
    + (* switch *)
      admit.
    + (* br_uncond *)
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP. ss.
      simtac. unfold valid_phinodes in *. simtac.
      rewrite add_terminator_cond_br_uncond in *.
      rewrite lookupBlockViaLabelFromFdef_spec in *.
      rewrite COND2 in H9. inv H9.
      rewrite COND3 in H12. inv H12.
      exploit postcond_phinodes_sound;
        (try instantiate (1 := (mkState (mkEC _ _ _ _ _ _) _ _))); s;
        (try eexact COND4; try eexact MEM);
        (try eexact H10; try eexact H13); ss; eauto.
      i. des.
      exploit apply_infrules_sound; eauto; ss. i. des.
      exploit reduce_maydiff_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      exploit valid_fdef_valid_stmts; eauto. i. des.
      esplits; eauto.
      * econs 1. econs; eauto. rewrite lookupBlockViaLabelFromFdef_spec. ss.
      * right. apply CIH. econs; ss; eauto; ss; eauto.
  - (* cmd *)
    destruct (Instruction.isCallInst c) eqn:CALL.
    + (* call *)
      destruct c; ss. destruct c0; ss.
      exploit postcond_call_sound;
        (try instantiate (1 := (mkState (mkEC _ _ _ _ _ _) _ _))); ss; eauto; ss.
      s. i. des. subst.
      eapply _sim_local_call; ss; eauto; ss.
      i. exploit RETURN; eauto. i. des.
      exploit apply_infrules_sound; eauto; ss. i. des.
      exploit reduce_maydiff_sound; eauto; ss. i. des.
      exploit implies_sound; eauto; ss. i. des.
      exists 0%nat, invmem1. splits; ss. right. apply CIH. econs; eauto.
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
      instantiate (1 := mkState (mkEC _ _ _ _ _ _) _ _).
      right. apply CIH. econs; ss; eauto.
Admitted.

Lemma valid_sim_fdef
      m_src m_tgt
      conf_src conf_tgt
      fdef_src fdef_tgt
      fdef_hint
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
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

(* TODO: lemma for module initialization *)
Lemma valid_sim_module m_hint:
  (valid_module m_hint) <2= sim_module.
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
    { admit. (* lookupFdefViaIDFromProducts -> InProductsB *) }
    unfold initTargetData in *.
    erewrite <- valid_products_genGlobalAndInitMem; eauto. rewrite COND2.
    rewrite COND3. eauto.
  - apply sim_local_lift_sim. econs.
    + econs 1.
    + generalize H0. i.
      unfold forallb2AL in H1. ss. apply andb_true_iff in H1. des. simtac.
      hexploit InvState.Rel.sem_empty; eauto.
      { admit. (* init_locals inject_locals *) }
      i. des.
      apply valid_sim. econs; eauto.
      * admit. (* valid_conf *)
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
    + reflexivity.
Admitted.
