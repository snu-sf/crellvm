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

Require Import TODO.
Require Import Nop.
Require Import Inject.
Require Import Validator.

Require Import SimulationLocal.
Require Import SimulationValid.
Require Import SimulationNop.
Require Import AdequacyLocal.
Require Import Simulation.
Require Import TODOProof.
Require Import program_sim.
Import Vellvm.program_sim.
(* Print program_sim.program_sim. *)
(* Print Vellvm.program_sim. *)

Inductive transl_product m_src m_tgt
  : forall (prod_src prod_tgt: product), Prop :=
| transl_product_gvar g
  : transl_product
      m_src m_tgt
      (product_gvar g) (product_gvar g)
| transl_product_fdec f
  : transl_product
      m_src m_tgt
      (product_fdec f) (product_fdec f)
| transl_product_fdef_nop
    f_src f_tgt
    (NOP_FDEF: nop_fdef f_src f_tgt)
  : transl_product
      m_src m_tgt
      (product_fdef f_src) (product_fdef f_tgt)
| transl_product_fdef_valid
    f_src f_tgt hint
    (VALID_FDEF: valid_fdef m_src m_tgt f_src f_tgt hint)
  : transl_product
      m_src m_tgt
      (product_fdef f_src) (product_fdef f_tgt)
.

Definition transl_products m_src m_tgt prods_src prods_tgt : Prop :=
  List.Forall2 (transl_product m_src m_tgt) prods_src prods_tgt.

Inductive transl_module : forall m_src m_tgt, Prop :=
| transl_module_intro
    l_src ndts_src prods_src
    l_tgt ndts_tgt prods_tgt
    (LAYOUTS_EQ: layouts_dec l_src l_tgt)
    (NAMEDTS_EQ: namedts_dec ndts_src ndts_tgt)
    (TRANSL_PRODUCTS: transl_products (module_intro l_src ndts_src prods_src)
                     (module_intro l_tgt ndts_tgt prods_tgt)
                     prods_src prods_tgt)
    (WF_SRC: wf_system [(module_intro l_src ndts_src prods_src)])
    (WF_TGT: wf_system [(module_intro l_tgt ndts_tgt prods_tgt)])
  : transl_module (module_intro l_src ndts_src prods_src)
                  (module_intro l_tgt ndts_tgt prods_tgt)
.

Lemma transl_products_lookupFdefViaIDFromProducts
      m_src m_tgt
      products_src products_tgt
      f fdef_src
      (PRODUCTS: transl_products m_src m_tgt products_src products_tgt)
      (SRC: lookupFdefViaIDFromProducts products_src f = Some fdef_src):
  exists fdef_tgt,
    <<TGT: lookupFdefViaIDFromProducts products_tgt f = Some fdef_tgt>> /\
    <<FDEF: transl_product m_src m_tgt (product_fdef fdef_src) (product_fdef fdef_tgt)>>.
Proof.
  revert products_tgt PRODUCTS SRC.
  induction products_src; [done|]. i.
  destruct products_tgt.
  { inv PRODUCTS. }
  ss. inv PRODUCTS.
  match goal with
  | [H: transl_product _ _ _ _ |- _] => inv H
  end.
  - des_ifs. apply IHproducts_src; eauto.
  - des_ifs. apply IHproducts_src; eauto.
  - des_ifs.
    + unfold lookupFdefViaIDFromProduct in *. des_ifs.
      esplits; eauto.
      eapply transl_product_fdef_nop; eauto.
    + inv NOP_FDEF. simtac.
    + inv NOP_FDEF. simtac.
    + apply IHproducts_src; eauto.
  - des_ifs.
    + unfold lookupFdefViaIDFromProduct in *. des_ifs.
      esplits; eauto.
      eapply transl_product_fdef_valid; eauto.
    + unfold valid_fdef in *. simtac.
    + unfold valid_fdef in *. simtac.
    + apply IHproducts_src; eauto.
Qed.

Lemma transl_products_genGlobalAndInitMem
      layouts namedts
      products0_src products_src
      products0_tgt products_tgt
      globals locals mem
      (PRODUCTS: transl_products
                   (module_intro layouts namedts products0_src)
                   (module_intro layouts namedts products0_tgt)
                   products_src products_tgt):
  genGlobalAndInitMem (layouts, namedts) products_src globals locals mem =
  genGlobalAndInitMem (layouts, namedts) products_tgt globals locals mem.
Proof.
  revert products_tgt globals locals mem PRODUCTS.
  induction products_src; i; destruct products_tgt; ss; try by inv PRODUCTS.
  unfold transl_products in PRODUCTS. ss. inv PRODUCTS.
  destruct a, p; simtac; try by inv H2.
  - inv H2. des_ifs; eauto.
  - inv H2. des_ifs; eauto.
  - inv H2.
    + destruct fdef5, fdef0.
      inv NOP_FDEF. des_ifs. eauto.
    + destruct fdef5, fdef0; ss.
      destruct fheader5, fheader0; ss.
      des_ifs; simtac; clarify.
      eauto.
Qed.

Definition empty_invmem : InvMem.Rel.t.
  assert(UNARY: InvMem.Unary.t).
  { econs; eauto.
    - apply nil.
    - apply Memory.Mem.empty.
    - apply nil.
    - apply xH. }
  econs; eauto.
  apply xH.
  econs.
  apply (xH, 0).
Defined.

Lemma transl_products_sim_conf
      gl ft
      md_src md_tgt prods_src prods_tgt
      TD
      (TRANSL_PRODUCTS: transl_products md_src md_tgt prods_src prods_tgt)
      (WF_CONF: wf_ConfigI (mkCfg [md_tgt] TD prods_tgt gl ft))
      (* (WF: wf_prods [md_tgt] md_tgt prods_tgt) *)
      (* (WF_SYST: wf_system sys_tgt) *)
      (* (WF_CONF: wf_ConfigI (mkCfg sys_tgt TD prods_tgt gl ft)) *)
  :
    <<SIM_CONF: sim_conf (mkCfg [md_src] TD prods_src gl ft)
                         (mkCfg [md_tgt] TD prods_tgt gl ft)>>
.
Proof.
  econs; eauto.
  ss.
  econs; eauto.
  - i.
    expl transl_products_lookupFdefViaIDFromProducts.
    esplits; eauto.
    inv FDEF.
    + inv NOP_FDEF.
      eapply nop_sim_fdef; eauto; try (econs; eauto).
      { inv BLOCKS; ss.
        des_ifs. des. clarify. }
    + eapply valid_sim_fdef; eauto.
      { ss. }
  - clear_tac. clear WF_CONF.
    i.
    ginduction prods_src; ii; inv TRANSL_PRODUCTS; ss.
    rename H1 into TRANSL_PRODUCT.
    des_ifsH FDEF_SRC.
    expl IHprods_src.
    inv TRANSL_PRODUCT; ss.
    + des_ifs. exfalso. inv NOP_FDEF. ss.
    + des_ifs. exfalso. unfold valid_fdef in *. des_ifs. ss.
      clear - n Heq0.
      compute in Heq0. des_ifs.
  - clear_tac. clear WF_CONF.
    i.
    ginduction prods_src; ii; inv TRANSL_PRODUCTS; ss.
    rename H1 into TRANSL_PRODUCT.
    des_ifsH FDEC_SRC.
    + esplits; eauto.
      inv TRANSL_PRODUCT; ss. des_ifs.
    + rename a into src_hd.
      rename y into tgt_hd.
      rename prods_src into src_tl.
      rename l' into tgt_tl.
      expl IHprods_src.
      destruct (lookupFdecViaIDFromProduct tgt_hd fid) eqn:T.
      * destruct f; ss.
        unfold lookupFdecViaIDFromProduct in *; des_ifs; inv TRANSL_PRODUCT.
        ss.
      * esplits; eauto.
Qed.

(* TODO: move to proper position *)
(* TODO: Is it replacable by some lemma in stdlib? or tactic? *)
Lemma dependent_split
      (A B: Prop)
      (HYPA: A)
      (HYPB: <<HYPA: A>> -> B)
  :
    <<GOAL: A /\ B>>
.
Proof.
  split; ss.
  apply HYPB; ss.
Qed.

Lemma transl_products_init
      l ndts prods_src prods_tgt
      (TRANSL_PRODUCTS:
         transl_products (module_intro l ndts prods_src)
                         (module_intro l ndts prods_tgt) prods_src prods_tgt)
      conf_src st_src
      main args
      (INIT: s_genInitState [module_intro l ndts prods_src] main args Mem.empty =
             Some (conf_src, st_src))
  :
    exists conf_tgt st_tgt,
    <<INIT: s_genInitState [module_intro l ndts prods_tgt] main args Mem.empty =
             Some (conf_tgt, st_tgt)>>
.
Proof.
  unfold s_genInitState in INIT. des_ifs.
  ss. des_ifs.
  expl transl_products_lookupFdefViaIDFromProducts. ss. rename products5 into prods_src.
  unfold s_genInitState. ss.
  rewrite TGT.
  match goal with
  | [|- context [productInModuleB_dec ?a ?b]] => destruct (productInModuleB_dec a b)
  end; simtac; cycle 1.
  { apply infrastructure_props.lookupFdefViaIDFromProducts_inv in TGT. congruence. }
  unfold initTargetData in *. ss.
  rename Heq1 into INITMEM.
  erewrite <- transl_products_genGlobalAndInitMem; eauto. rewrite INITMEM.
  abstr (module_intro layouts5 namedts5 prods_src) md_src.
  abstr (module_intro layouts5 namedts5 prods_tgt) md_tgt.
  rename Heq3 into INIT_LOCALS.
  clear - FDEF INIT_LOCALS.
  inv FDEF.
  - inv NOP_FDEF. ss. inv BLOCKS. des_ifs_safe ss. des. clarify.
    esplits; eauto.
  - inv VALID_FDEF. des_ifs_safe ss.
    des_bool. des_sumbool. clarify.
    rewrite INIT_LOCALS.
    esplits; eauto.
Qed.

Definition init_invmem (m0: mem): InvMem.Rel.t :=
  InvMem.Rel.mk (InvMem.Unary.mk [] Mem.empty [] m0.(Mem.nextblock))
                (InvMem.Unary.mk [] Mem.empty [] m0.(Mem.nextblock))
                (Mem.nextblock m0 - 1)
                (memory_props.MemProps.inject_init (Mem.nextblock m0 - 1))
.

Lemma init_mem_sem
      (* Do we need prods_src/prods_tgt both? not sure, but this form is sufficient *)
      (* l ndts prods gl fs m0 *)
      (* (INIT: genGlobalAndInitMem (l, ndts) prods [] [] Mem.empty = ret (gl, fs, m0)) *)
      l ndts prods_src prods_tgt gl fs m0
      (INIT_SRC: genGlobalAndInitMem (l, ndts) prods_src [] [] Mem.empty = ret (gl, fs, m0))
      (INIT_TGT: genGlobalAndInitMem (l, ndts) prods_tgt [] [] Mem.empty = ret (gl, fs, m0))
      lc args params
      (INIT_LOCALS: initLocals (l, ndts) args params = ret lc)
      sys_src sys_tgt
  :
      <<SEM: InvMem.Rel.sem
               (mkCfg sys_src (l, ndts) prods_src gl fs)
               (mkCfg sys_tgt (l, ndts) prods_tgt gl fs)
               m0 m0 (init_invmem m0)>>
.
Proof.
  hexploit genGlobalAndInitMem__wf_globals_Mem; eauto; intro WF; des.
  unfold initTargetData in *.
  econs; ss; eauto.
  - econs; ss; eauto.
    + eapply memory_props.MemProps.redundant__wf_globals; eauto.
    + ii. ss.
    + econs; eauto.
    + eapply Pos.le_1_l; eauto.
  - econs; ss; eauto.
    + eapply memory_props.MemProps.redundant__wf_globals; eauto.
    + ii. ss.
    + econs; eauto.
    + eapply Pos.le_1_l; eauto.
Qed.

Lemma transl_sim_module:
  transl_module <2= sim_module.
Proof.
  s. intros module_src module_tgt MODULE.
  inv MODULE.
  ii.
  {
    pose (s_genInitState [module_intro l_src ndts_src prods_src] main args0 Mem.empty)
      as SRC_INIT.
    pose st_src as SRC_ST.

    remember (s_genInitState [module_intro l_tgt ndts_tgt prods_tgt]
                             main args0 Mem.empty) as TI eqn:TGT_INIT0.
    pose (s_genInitState [module_intro l_tgt ndts_tgt prods_tgt]
                         main args0 Mem.empty) as TGT_INIT1.
    assert(EQ: TI = TGT_INIT1) by  ss. rewrite EQ. clarify.
    unfold s_genInitState in SRC, EQ.
    ss.
    des_ifs_safe ss. clarify. rename products5 into prods_src.
    expl transl_products_lookupFdefViaIDFromProducts.
    rewrite TGT in *. ss.
    match goal with
    | [H: context [productInModuleB_dec ?a ?b] |- _] => destruct (productInModuleB_dec a b)
    end; cycle 1.
    { apply infrastructure_props.lookupFdefViaIDFromProducts_inv in TGT. ss. congruence. }
    unfold initTargetData in *. ss.
    rename Heq2 into INITMEM.
    unfold proj_sumbool in *. des_ifs_safe ss. clarify.
    erewrite <- transl_products_genGlobalAndInitMem in EQ; eauto. rewrite INITMEM in *.
    rename Heq10 into INIT_LOCALS.
    (* clear - FDEF INIT_LOCALS. *)
    inv FDEF.



    - (* fheader_intro is different here *)
      (* actually, it is same and this fact is needed for nop_sim_fdef. *)
      (* this fact can only be achieved by *)
      (* inv NOP_FDEF. so I save nop_fdef here, and then inv *)
      (* TODO: generalize nop_sim_fdef, header -> header_src/header_tgt. anyhow they are same *)
      (* by nop_fdef in premise *)
      inversion NOP_FDEF; subst.
      ss. inv BLOCKS. des_ifs_safe ss. des. clarify.
      hexploit nop_sim_fdef; try exact NOP_FDEF.
      { instantiate (1:= {|
                          CurSystem := [module_intro l_tgt ndts_tgt prods_tgt];
                          CurTargetData := (l_tgt, ndts_tgt);
                          CurProducts := prods_tgt;
                          Globals := g;
                          FunTable := g0 |}).
        instantiate (1:= {|
                          CurSystem := [module_intro l_tgt ndts_tgt prods_src];
                          CurTargetData := (l_tgt, ndts_tgt);
                          CurProducts := prods_src;
                          Globals := g;
                          FunTable := g0 |}).
        ss.
      }
      { ss. }
      intro SIM; des.







      hexploit genGlobalAndInitMem__wf_globals_Mem; eauto; []; intro WF; des.
      unfold sim_fdef in *.
      hexploit SIM.
      { eapply init_mem_sem; eauto.
        erewrite <- transl_products_genGlobalAndInitMem; eauto.
      }
      { instantiate (1:= args0).
        instantiate (1:= args0).
        ss.
        rename Heq1 into INIT_LOCALS.
        (* OpsemPP.wf_ExecutionContext__at_beginning_of_function *)
        clear - WF4 WF INIT_LOCALS.
        (* OpsemPP.initLocals_spec' *)
        (* opsem_props.OpsemProps.initLocals_spec *)
        admit.
      }
      {
        (* instantiate *)
        (*   (1:= *)
        (*      {| *)
        (*        CurFunction := fdef_intro *)
        (*                         (fheader_intro fnattrs0 typ0 id0 args1 varg0) *)
        (*                         ((l1, stmts_intro phinodes0 cmds5 terminator0) :: b1); *)
        (*        CurBB := (l1, stmts_intro phinodes0 cmds5 terminator0); *)
        (*        CurCmds := cmds5; *)
        (*        Terminator := terminator0; *)
        (*        Locals := g1; *)
        (*        Allocas := [] |}). *)
        econs; ss; eauto.
      }
      clear SIM. intro SIM_LOCAL; des.
      inv SIM_LOCAL. ss. clarify.




      esplits; eauto.
      + eapply sim_local_lift_sim; eauto.
        { eapply transl_products_sim_conf; eauto.
          subst TGT_INIT1.
          expl s_genInitState__opsem_wf.
          eapply wf_ConfigI_spec; eauto.
        }
        econs; ss; eauto.
        * econs; eauto.
        * eapply SIM_LOCAL0.
          { (* wf *)
            subst TGT_INIT1.
            expl s_genInitState__opsem_wf.
            split; ss.
          }
        * reflexivity.



    - destruct blocks5.
      { ss. des_ifs. }
      assert(args5 = args1).
      { ss. des_ifs_safe ss. des_bool. unfold proj_sumbool in *. des_ifs. }
      clarify.
      rewrite INIT_LOCALS in *.
      des_ifs.
      (* I want "TGT_INIT1 = Some" without breaking VALID_FDEF *)
      (* both "TGT_INIT1 = Soem" && VALID_FDEF is used in next hexploit *)
      (* TODO: can we do this in more smart way? *)
      (* Here, even "ss" breaks VALID_FDEF. It is really truly annoying *)
      hexploit valid_sim_fdef; try exact VALID_FDEF.
      { instantiate (1:= {|
                          CurSystem := [module_intro l_tgt ndts_tgt prods_tgt];
                          CurTargetData := (l_tgt, ndts_tgt);
                          CurProducts := prods_tgt;
                          Globals := g;
                          FunTable := g0 |}).
        instantiate (1:= {|
                          CurSystem := [module_intro l_tgt ndts_tgt prods_src];
                          CurTargetData := (l_tgt, ndts_tgt);
                          CurProducts := prods_src;
                          Globals := g;
                          FunTable := g0 |}).
        ss.
      }
      { subst TGT_INIT1.
        expl s_genInitState__opsem_wf.
        ss.
      }
      intro SIM; des.



      ss. des_ifs_safe ss. clarify. des. des_bool. unfold is_empty in *. des_ifs_safe ss.
      unfold proj_sumbool in *. des_ifs_safe ss. des_ifs_safe. clear_tac.








      hexploit genGlobalAndInitMem__wf_globals_Mem; eauto; []; intro WF; des.
      unfold sim_fdef in *.
      hexploit SIM.
      { eapply init_mem_sem; eauto.
        erewrite <- transl_products_genGlobalAndInitMem; eauto.
      }
      { instantiate (1:= args0).
        instantiate (1:= args0).
        ss.
        (* OpsemPP.wf_ExecutionContext__at_beginning_of_function *)
        clear - WF4 WF INIT_LOCALS.
        (* OpsemPP.initLocals_spec' *)
        (* opsem_props.OpsemProps.initLocals_spec *)
        admit.
      }
      { econs; ss; eauto. }
      clear SIM. intro SIM_LOCAL; des.
      inv SIM_LOCAL. ss. clarify.




      esplits; eauto.
      + eapply sim_local_lift_sim; eauto.
        { eapply transl_products_sim_conf; eauto.
          subst TGT_INIT1.
          expl s_genInitState__opsem_wf.
          eapply wf_ConfigI_spec; eauto.
        }
        econs; ss; eauto.
        * econs; eauto.
        * eapply SIM_LOCAL0.
          { (* wf *)
            subst TGT_INIT1.
            expl s_genInitState__opsem_wf.
            split; ss.
          }
        * reflexivity.
Admitted.

(* Lemma transl_sim_module: *)
(*   transl_module <2= sim_module. *)
(* Proof. *)
(*   s. intros module_src module_tgt MODULE. *)
(*   inv MODULE. *)
(*   ii. *)
(*   expl s_genInitState__opsem_wf (try exact WF_SRC; eauto). *)
(*   apply_all_once wf_ConfigI_spec. apply_all_once wf_StateI_spec. *)
(*   (* Without this, prop will be destructed into multiple parts, and readibility is marred. *) *)
(*   unfold s_genInitState in SRC. simtac. *)
(*   clear COND e0. apply infrastructure_props.InProductsB_In in e. *)
(*   exploit transl_products_lookupFdefViaIDFromProducts; eauto. i. des. *)
(*   destruct fdef_tgt. unfold LLVMinfra.is_true in *. simtac. *)
(*   destruct fheader5. *)
(*   (* TODO: define all_with_term_once *) *)
(*   (* Ltac expl_with H := expl lookupFdefViaIDFromProducts_ideq (idtac H; try exact H; eauto). *) *)
(*   (* all_with_term expl_with lookupFdefViaIDFromProducts. *) *)
(*   expl lookupFdefViaIDFromProducts_ideq (try exact COND3; eauto). clarify. *)
(*   expl lookupFdefViaIDFromProducts_ideq (try exact TGT; eauto). clarify. *)
(*   inv FDEF. *)
(*   { inv NOP_FDEF. *)
(*     assert (NOP_BLOCKS_ENTRY: *)
(*               exists phi' cmds' term' b', *)
(*                 blocks5 = ((l0, stmts_intro phi' cmds' term')::b')). *)
(*     { inv BLOCKS. *)
(*       destruct y. destruct s. *)
(*       assert (LEQ: l1 = l0). *)
(*       { *)
(*         exploit transl_products_lookupFdefViaIDFromProducts; eauto. i. des. *)
(*         clarify. *)
(*       } *)
(*       subst. *)
(*       esplits; eauto. *)
(*     } *)
(*     des. *)



(*     expl genGlobalAndInitMem__wf_globals_Mem. *)

(*     do 3 eexists. *)
(*     apply dependent_split. *)
(*     - unfold s_genInitState. ss. rewrite TGT. *)
(*       match goal with *)
(*       | [|- context [productInModuleB_dec ?a ?b]] => destruct (productInModuleB_dec a b) *)
(*       end; simtac; cycle 1. *)
(*       { apply infrastructure_props.lookupFdefViaIDFromProducts_inv in TGT. congruence. } *)
(*       unfold initTargetData in *. *)
(*       erewrite <- transl_products_genGlobalAndInitMem; eauto. rewrite COND1. *)
(*       rewrite COND2. *)
(*       eauto. *)
(*     - i; des. *)

(*       clear s_genInitState__opsem_wf. *)
(*       hexploit s_genInitState__opsem_wf; eauto; []; intro WF_TGT2; destruct WF_TGT2 as [WF_CONF_TGT WF_ST_TGT]. *)
(*       apply wf_ConfigI_spec in WF_CONF_TGT. apply wf_StateI_spec in WF_ST_TGT. *)

(*       apply sim_local_lift_sim. *)
(*       { eapply transl_products_sim_conf; eauto. } *)
(*       econs; ss. *)
(*       + econs. *)
(*       + apply nop_sim. *)
(*         * econs; eauto. *)
(*         * clarify. *)
(*           inv BLOCKS. des. clarify. *)
(*           econs; eauto. *)
(*           { econs; eauto. *)
(*             econs; eauto. } *)
(*           { econs. esplits; eauto. *)
(*             exact (SF_ADMIT "inject_locals"). } *)
(*           { econs. } *)
(*           { exact (SF_ADMIT "init mem"). } *)
(*           { ss. } *)
(*           { ss. } *)
(*       + reflexivity. *)
(*   } *)
(*   { ss. simtac. *)
(*     inv e0. *)
(*     expl genGlobalAndInitMem__wf_globals_Mem. *)
(*     do 3 eexists. apply dependent_split. *)
(*     - unfold s_genInitState. ss. rewrite TGT. *)
(*       match goal with *)
(*       | [|- context [productInModuleB_dec ?a ?b]] => destruct (productInModuleB_dec a b) *)
(*       end; simtac; cycle 1. *)
(*       { apply infrastructure_props.lookupFdefViaIDFromProducts_inv in TGT. congruence. } *)
(*       unfold initTargetData in *. *)
(*       erewrite <- transl_products_genGlobalAndInitMem; eauto. rewrite COND1. *)
(*       rewrite COND2. eauto. *)
(*     - i; des. *)

(*       clear s_genInitState__opsem_wf. *)
(*       hexploit s_genInitState__opsem_wf; eauto; []; intro WF_TGT2; destruct WF_TGT2 as [WF_CONF_TGT WF_ST_TGT]. *)
(*       apply wf_ConfigI_spec in WF_CONF_TGT. apply wf_StateI_spec in WF_ST_TGT. *)

(*       apply sim_local_lift_sim. *)
(*       { eapply transl_products_sim_conf; eauto. } *)
(*       econs; ss. *)
(*       + econs. *)
(*       + generalize VALID_FDEF. i. *)
(*         unfold forallb2AL in VALID_FDEF0. ss. apply andb_true_iff in VALID_FDEF0. *)
(*         repeat (des; des_bool; des_sumbool; des_ifs_safe). *)
(*         hexploit InvState.Rel.sem_empty; eauto. *)
(*         { exact (SF_ADMIT "init_locals inject_locals"). } *)
(*         i. des. *)
(*         apply valid_sim. econs; eauto. *)
(*         * ss. *)
(*         * *)
(*           cbn in *. *)
(*           clear_tac. *)
(*           unfold Debug.failwith_false in *. *)
(*           repeat multimatch goal with *)
(*                  | H:context [id_dec ?a ?b] |- _ => destruct (id_dec a b); ss *)
(*                  end. *)
(*           repeat (des; des_bool; des_sumbool; des_ifs_safe). *)
(*         (* inject allocas *) *)
(*         (* * ss. econs; eauto. *) *)
(*         * ss. des_ifsH Heq0. *)
(*           { exists []. ss. } *)
(*           { eexists; eauto. } *)
(*         * ss. exact (SF_ADMIT "InvMem.Rel.sem init_mem"). *)
(*       + reflexivity. *)
(*   } *)
(* Unshelve. *)
(* { apply empty_invmem. } *)
(* { by econs; eauto. } *)
(* { apply empty_invmem. } *)
(* (* Qed. *) *)
(* Qed. *)
