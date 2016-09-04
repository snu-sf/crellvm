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
Require Import Validator.
Require Import GenericValues.
Require Import SimulationLocal.
Require Import Simulation.
Require InvMem.
Require InvState.
Require Import SoundBase.
Require Import SoundImplies.
Require Import SoundPostcond.
Require Import SoundInfrules.
Require Import SoundReduceMaydiff.

Set Implicit Arguments.


(* TODO: position *)
Definition get_blocks (f:fdef): blocks :=
  let '(fdef_intro _ blocks) := f in
  blocks.

Inductive vali_state_sim
          (conf_src conf_tgt:Config)
          (stack0_src stack0_tgt:ECStack)
          (invmem:InvMem.Rel.t)
          (idx:nat)
          (st_src st_tgt:State): Prop :=
| vali_state_sim_intro
    m_src m_tgt
    fdef_hint cmds_hint
    inv inv_term
    invst
    (CONF: CONF_TODO) (* m_src, m_tgt, conf_src, conf_tgt *)
    (ECS_SRC: st_src.(ECS) = stack0_src)
    (ECS_TGT: st_tgt.(ECS) = stack0_tgt)
    (FDEF: valid_fdef m_src m_tgt st_src.(EC).(CurFunction) st_tgt.(EC).(CurFunction) fdef_hint)
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

Lemma vali_init
      m_src m_tgt
      conf_src conf_tgt
      stack0_src stack0_tgt
      fdef_src fdef_tgt
      fdef_hint
      args_src args_tgt
      mem_src mem_tgt
      inv
      ec_src
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint)
      (ARGS: list_forall2 (genericvalues_inject.gv_inject inv.(InvMem.Rel.inject)) args_src args_tgt)
      (MEM: InvMem.Rel.sem conf_src conf_tgt mem_src mem_tgt inv)
      (CONF: CONF_TODO)
      (INIT: init_fdef conf_src fdef_src args_src ec_src):
  exists ec_tgt idx,
    init_fdef conf_tgt fdef_tgt args_tgt ec_tgt /\
    vali_state_sim
      conf_src conf_tgt
      stack0_src stack0_tgt
      inv idx
      (mkState ec_src stack0_src mem_src)
      (mkState ec_tgt stack0_tgt mem_tgt).
Proof.
Admitted.

(* TODO: position *)
Ltac condtac :=
  repeat
    (try match goal with
         | [H: ?a = ?a |- _] => clear H
         | [H: is_true true |- _] => clear H
         | [H: Some _ = Some _ |- _] => inv H
         | [H: context[let (_, _) := ?p in _] |- _] => destruct p
         | [H: negb _ = true |- _] =>
           apply negb_true_iff in H
         | [H: negb _ = false |- _] =>
           apply negb_false_iff in H
         | [H: andb _ _ = true |- _] => apply andb_true_iff in H; destruct H

         | [H: proj_sumbool (id_dec ?a ?b) = true |- _] =>
           destruct (id_dec a b)
         | [H: proj_sumbool (typ_dec ?a ?b) = true |- _] =>
           destruct (typ_dec a b)
         | [H: proj_sumbool (l_dec ?a ?b) = true |- _] =>
           destruct (l_dec a b)
         | [H: proj_sumbool (fheader_dec ?a ?b) = true |- _] =>
           destruct (fheader_dec a b)
         | [H: proj_sumbool (layouts_dec ?a ?b) = true |- _] => destruct (layouts_dec a b)
         | [H: proj_sumbool (namedts_dec ?a ?b) = true |- _] => destruct (namedts_dec a b)
         | [H: productInModuleB_dec ?a ?b = left _ |- _] => destruct (productInModuleB_dec a b)

         | [H: context[match ?c with
                       | [] => _
                       | _::_ => _
                       end] |- _] =>
           let COND := fresh "COND" in
           destruct c eqn:COND
         | [H: context[match ?c with
                       | Some _ => _
                       | None => _
                       end] |- _] =>
           let COND := fresh "COND" in
           destruct c eqn:COND
         | [H: context[if ?c then _ else _] |- _] =>
           let COND := fresh "COND" in
           destruct c eqn:COND
         end;
     unfold Debug.debug_print_validation_process in *;
     try subst; ss).


(* TODO: position *)
Lemma inject_value_sound
      conf_src st_src val_src
      conf_tgt st_tgt val_tgt
      invst invmem inv
      gval_src
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem)
      (INJECT: Hints.Invariant.inject_value inv val_src val_tgt)
      (VAL_SRC: InvState.Unary.sem_valueT conf_src st_src invst.(InvState.Rel.src) val_src = Some gval_src):
  exists gval_tgt,
    <<VAL_TGT: InvState.Unary.sem_valueT conf_tgt st_tgt invst.(InvState.Rel.tgt) val_tgt = Some gval_tgt>> /\
    <<INJECT: genericvalues_inject.gv_inject invmem.(InvMem.Rel.inject) gval_src gval_tgt>>.
Proof.
Admitted.

(* TODO: position *)
Lemma sem_valueT_physical
      conf st inv val:
  InvState.Unary.sem_valueT conf st inv (Exprs.ValueT.lift Exprs.Tag.physical val) =
  getOperandValue conf.(CurTargetData) val st.(EC).(Locals) conf.(Globals).
Proof. destruct val; ss. Qed.

Lemma vali_sim
      conf_src conf_tgt:
  (vali_state_sim conf_src conf_tgt) <6= (sim_local conf_src conf_tgt).
Proof.
  intros stack0_src stack0_tgt.
  pcofix CIH.
  intros inv0 idx0 st_src st_tgt SIM. pfold.
  generalize (classic (stuck_state conf_src st_src)). intro STUCK_SRC. des.
  { destruct (s_isFinialState conf_src st_src) eqn:FINAL_SRc; cycle 1.
    - (* error *)
      eapply _sim_local_error; eauto. econs; eauto.
    - (* final *)
      admit.
  }
  destruct st_src, st_tgt. destruct EC0, EC1.
  inv SIM. ss.
  destruct CurCmds0; condtac;
    (try by exfalso; eapply has_false_False; eauto).
  - (* term *)
    unfold valid_terminator in TERM.
    condtac;
      (try by exfalso; eapply has_false_False; eauto).
    apply NNPP in STUCK_SRC. des.
    inv STUCK_SRC; destruct Terminator1; condtac.
    (* TODO: switch case *)
    + (* return *)
      unfold returnUpdateLocals in *. condtac.
      exploit inject_value_sound; eauto.
      { rewrite sem_valueT_physical. eauto. }
      rewrite sem_valueT_physical. s. i. des.
      eapply _sim_local_return; eauto; ss.
    + (* return_void *)
      eapply _sim_local_return_void; eauto; ss.
    + (* br *)
      exploit inject_value_sound; eauto.
      { rewrite sem_valueT_physical. eauto. }
      rewrite sem_valueT_physical. s. i. des.
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP. ss.
      esplits; eauto.
      { econs 1. econs; eauto. rewrite COND3. eauto. }
      { reflexivity. }
      right. apply CIH.
      instantiate (1 := mkState _ _ _). econs; eauto; ss.
      * admit. (* valid_fdef *)
      * admit. (* valid_cmds *)
      * admit. (* valid_terminator *)
      * admit. (* InvState.Rel.sem *)
    + (* br, bogus: see https://github.com/snu-sf/llvmberry/issues/310 *)
      admit.
    + (* br_uncond *)
      eapply _sim_local_step.
      { admit. (* tgt not stuck *) }
      i. inv STEP. ss.
      esplits; eauto.
      { econs 1. econs; eauto. }
      { reflexivity. }
      right. apply CIH.
      instantiate (1 := mkState _ _ _). econs; eauto; ss.
      * admit. (* valid_fdef *)
      * admit. (* valid_cmds *)
      * admit. (* valid_terminator *)
      * admit. (* InvState.Rel.sem *)
  - (* cmd *)
    eapply _sim_local_step.
    { (* tgt not stuck *)
      admit.
    }
    i.
    (* TODO: call is ignored! *)
    exploit postcond_cmd_sound; eauto; ss. i. des.
    exploit apply_infrules_sound; eauto; ss. i. des.
    exploit reduce_maydiff_sound; eauto; ss. i. des.
    exploit implies_sound; eauto; ss. i. des.
    esplits; eauto.
    + econs 1. eauto.
    + right. apply CIH. econs; eauto.
      * admit. (* valid_fdef *)
      * admit. (* valid_cmds *)
      * admit. (* valid_terminator *)
Admitted.

Lemma vali_sim_fdef
      m_src m_tgt
      conf_src conf_tgt
      fdef_src fdef_tgt
      fdef_hint
      (CONF: CONF_TODO)
      (FDEF: valid_fdef m_src m_tgt fdef_src fdef_tgt fdef_hint):
  sim_fdef conf_src conf_tgt fdef_src fdef_tgt.
Proof.
  ii.
  exploit vali_init; eauto. i. des.
  esplits; eauto.
  apply vali_sim; eauto.
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
  s in SRC. condtac.
  - destruct a, p; condtac. esplits; eauto.
    + destruct (getFdefID fdef0 == getFdefID fdef_src); eauto. congruence.
    + destruct (id_dec (getFdefID fdef_src) (getFdefID fdef0)); ss.
      destruct (valid_fdef m_src m_tgt fdef_src fdef0 f0) eqn:FDEF; ss. congruence.
  - destruct a, p; condtac. congruence.
  - exploit IHproducts_src; eauto. i. des.
    esplits; eauto.
    destruct (lookupFdefViaIDFromProduct p f) eqn:HD; ss.
    destruct a, p; condtac.
  - exploit IHproducts_src; eauto. i. des.
    esplits; eauto.
    destruct (lookupFdefViaIDFromProduct p f) eqn:HD; ss.
    destruct a, p; condtac.
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
  destruct a, p; condtac.
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

Lemma vali_sim_module m_hint:
  (valid_module m_hint) <2= sim_module.
Proof.
  s. intros module_src module_tgt MODULE.
  unfold valid_module in MODULE. condtac.
  ii. unfold s_genInitState in SRC. condtac.
  clear COND0 e0. apply infrastructure_props.InProductsB_In in e.
  exploit valid_products_lookupFdefViaIDFromProducts; eauto. i. des. condtac.
  destruct fheader5. inv e0. ss.
  esplits.
  - unfold s_genInitState. ss. rewrite TGT.
    match goal with
    | [|- context [productInModuleB_dec ?a ?b]] => destruct (productInModuleB_dec a b)
    end; condtac; cycle 1.
    { eadmit. (* lookupFdefViaIDFromProducts -> InProductsB *) }
    unfold initTargetData in *.
    erewrite <- valid_products_genGlobalAndInitMem; eauto. rewrite COND2.
    rewrite COND3. eauto.
  - apply sim_local_lift_sim. econs.
    + econs 1.
    + generalize H0. i.
      unfold forallb2AL in H1. ss. apply andb_true_iff in H1. des. condtac.
      apply vali_sim. econs; eauto.
      * admit. (* CONF_TODO *)
      * (* TODO: reorganize tactics *)
        repeat
          (try match goal with
               | [|- is_true (if ?c then _ else _)] =>
                 let COND := fresh "COND" in
                 destruct c eqn:COND
               end;
           condtac).
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
           condtac).
        { match goal with
          | [H: proj_sumbool (id_dec ?a ?a) = false |- _] => destruct (id_dec a a); ss
          end.
        }
        rewrite COND5, COND6, COND7, COND8, COND9. ss.
      * admit. (* state *)
      * admit. (* mem *)
    + reflexivity.
Admitted.
