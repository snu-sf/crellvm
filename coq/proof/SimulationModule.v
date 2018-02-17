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
      eapply transl_product_fdef_valid; eauto.
    + unfold valid_fdef in *. simtac. clarify.
    + unfold valid_fdef in *. simtac. clarify.
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
    + destruct fdef5, fdef0; ss.
      destruct fheader5, fheader0; ss.
      des_ifs; simtac; clarify.
      eauto.
Qed.

Definition empty_assnmem : AssnMem.Rel.t.
  assert(UNARY: AssnMem.Unary.t).
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
      prods_src prods_tgt
      los nd
      (* los/nd is same for src/tgt *)
      (TRANSL_PRODUCTS: transl_products (module_intro los nd prods_src)
                                        (module_intro los nd prods_tgt) prods_src prods_tgt)
      (WF_SRC: wf_ConfigI (mkCfg [module_intro los nd prods_src] (los, nd) prods_src gl ft))
      (WF_TGT: wf_ConfigI (mkCfg [module_intro los nd prods_tgt] (los, nd) prods_tgt gl ft))
      (WF_SRC_SYS: wf_system [module_intro los nd prods_src])
      (WF_TGT_SYS: wf_system [module_intro los nd prods_tgt])
  :
    <<SIM_CONF: sim_conf (mkCfg [module_intro los nd prods_src] (los, nd) prods_src gl ft)
                         (mkCfg [module_intro los nd prods_tgt] (los, nd) prods_tgt gl ft)>>
.
Proof.
  econs; eauto.
  ss.
  econs; eauto.
  - i.
    expl transl_products_lookupFdefViaIDFromProducts.
    esplits; eauto.
    inv FDEF.
    + eapply valid_sim_fdef; eauto.
      { ss. }
      { ss. }
      { ss. }
      { ss.
        eapply wf_system__wf_fdef; try eassumption.
        - ss. unfold moduleEqB. unfold sumbool2bool. des_ifsG.
        - ss. erewrite lookupFdefViaIDFromProducts_inv; eauto.
      }
      { ss.
        eapply wf_system__wf_fdef; try eassumption.
        - ss. unfold moduleEqB. unfold sumbool2bool. des_ifsG.
        - ss. erewrite lookupFdefViaIDFromProducts_inv; eauto.
      }
  - clear WF_TGT WF_SRC WF_SRC_SYS WF_TGT_SYS. clear_tac.
    i.
    revert TRANSL_PRODUCTS. generalize prods_src at 1. generalize prods_tgt at 1. ii.
    ginduction prods_src; ii; inv TRANSL_PRODUCTS; ss.
    rename H1 into TRANSL_PRODUCT.
    des_ifsH FDEF_SRC.
    expl IHprods_src.
    inv TRANSL_PRODUCT; ss.
    + des_ifs. exfalso. unfold valid_fdef in *. des_ifs. ss.
      clear - n Heq0.
      compute in Heq0. des_ifs.
  - clear WF_TGT WF_SRC WF_SRC_SYS WF_TGT_SYS. clear_tac.
    i.
    revert TRANSL_PRODUCTS. generalize prods_src at 1. generalize prods_tgt at 1. ii.
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
  - inv VALID_FDEF. des_ifs_safe ss.
    des_bool. des_sumbool. clarify.
    rewrite INIT_LOCALS.
    esplits; eauto.
Qed.

Definition init_assnmem (m0: mem): AssnMem.Rel.t :=
  AssnMem.Rel.mk (AssnMem.Unary.mk [] Mem.empty [] m0.(Mem.nextblock))
                (AssnMem.Unary.mk [] Mem.empty [] m0.(Mem.nextblock))
                (Mem.nextblock m0 - 1)
                (memory_props.MemProps.inject_init (Mem.nextblock m0 - 1))
.

Lemma init_mem_sem
      (* Do we need prods_src/prods_tgt both? not sure, but this form is sufficient *)
      l ndts prods_src prods_tgt gl fs m0
      (INIT_SRC: genGlobalAndInitMem (l, ndts) prods_src [] [] Mem.empty = ret (gl, fs, m0))
      (INIT_TGT: genGlobalAndInitMem (l, ndts) prods_tgt [] [] Mem.empty = ret (gl, fs, m0))
      lc args params
      (INIT_LOCALS: initLocals (l, ndts) args params = ret lc)
      sys_src sys_tgt
  :
      <<SEM: AssnMem.Rel.sem
               (mkCfg sys_src (l, ndts) prods_src gl fs)
               (mkCfg sys_tgt (l, ndts) prods_tgt gl fs)
               m0 m0 (init_assnmem m0)>>
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

Lemma not_in_init_locals
      TD args argvs lc
      (INIT_LOCALS: initLocals TD args argvs = Some lc)
      i0
      (NOTIN: ~ In i0 (getArgsIDs args))
      gv
      (LOOKUP: lookupAL GenericValue lc i0 = Some gv)
  :
    False
.
Proof.
  unfold initLocals in *.
  ginduction args; ii; ss; clarify.
  des_ifs_safe.
  des_ifs.
  - ss.
    apply not_or_and in NOTIN. des.
    des_lookupAL_updateAddAL.
    exploit IHargs; eauto.
  - ss.
    apply not_or_and in NOTIN. des.
    des_lookupAL_updateAddAL.
    exploit IHargs; eauto.
Qed.

Lemma init_locals_wf_inv
      TD args argvs lc
      (INIT_LOCALS: initLocals TD args argvs = Some lc)
      (UNIQ: List.NoDup (getArgsIDs args))
      m
      (WF: memory_props.MemProps.wf_lc m lc)
      (FIT: Forall2
              (fun x y => fit_gv TD (fst (fst x)) y = ret y) args argvs)
  :
    <<VALID: Forall (memory_props.MemProps.valid_ptrs (Mem.nextblock m)) argvs>>
.
Proof.
  red.
  ginduction argvs; ii; ss.
  destruct args0; ss; inv FIT.
  unfold initLocals in *. ss. des_ifs.
  econs; eauto.
  - ss.
    exploit WF.
    { des_lookupAL_updateAddAL. }
    i. ss.
  - ss. inv UNIQ.
    eapply IHargvs; eauto.
    ii.
    eapply WF; eauto. instantiate (1:= id0).
    des_lookupAL_updateAddAL.
    exploit not_in_init_locals; eauto. i; ss.
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
    dup SRC. rename SRC0 into SRC_INIT_SUCCESS. sguard in SRC_INIT_SUCCESS.
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

      assert(WF_CONF_SRC: wf_ConfigI (mkCfg [module_intro l_tgt ndts_tgt prods_src]
                                            (l_tgt, ndts_tgt)
                                            prods_src
                                            g g0)).
      { unsguard SRC_INIT_SUCCESS. simpl in SRC_INIT_SUCCESS.
        (* TODO: Was this needed? *)
        (* What if it doesn't work, what should I do? *)
        (* In general, making all the props before (when SRC_INIT_SUCCESS was alive) is not the answer, *)
        (* because it will severly mar readability && the props made itself may not survive ss *)
        expl s_genInitState__opsem_wf (try exact WF_SRC; eauto).
        ss.
      }
      assert(WF_CONF_TGT: wf_ConfigI (mkCfg [module_intro l_tgt ndts_tgt prods_tgt]
                                            (l_tgt, ndts_tgt)
                                            prods_tgt
                                            g g0)).
      { subst TGT_INIT1.
        expl s_genInitState__opsem_wf (try exact WF_TGT; eauto).
        ss.
      }

      hexploit valid_sim_fdef; try exact VALID_FDEF; [| | |exact WF_CONF_SRC|exact WF_CONF_TGT|..]; ss.
      { eapply wf_system__wf_fdef; try eassumption.
        ss.
        unfold moduleEqB. unfold sumbool2bool. des_ifsG.
      }
      { eapply wf_system__wf_fdef; try eassumption.
        ss.
        unfold moduleEqB. unfold sumbool2bool. des_ifsG.
      }
      intro SIM; des.



      ss. des_ifs_safe ss. clarify. des. des_bool. unfold is_empty in *. des_ifs_safe ss.
      unfold proj_sumbool in *. des_ifs_safe ss. des_ifs_safe. clear_tac.








      hexploit genGlobalAndInitMem__wf_globals_Mem; eauto; []; intro WF; des.

      assert(UNIQF: uniqFdef (fdef_intro (fheader_intro fnattrs0 typ0 id0 args1 varg0)
                                         ((l1, stmts_intro [] cmds5 terminator5) :: b1))).
      { eapply wf_system__uniqFdef; revgoals.
        { instantiate (1:= prods_src). ss. }
        { instantiate (1:= [module_intro l_tgt ndts_tgt prods_src]). ss.
          unfold moduleEqB. unfold sumbool2bool. des_ifs.
        }
        { ss. }
      }

      unfold sim_fdef in *.
      hexploit SIM.
      { eapply init_mem_sem; eauto.
        - erewrite <- transl_products_genGlobalAndInitMem; eauto.
      }
      { clear SIM.
        instantiate (1:= args0).
        instantiate (1:= args0).
        ss.
        unfold get_params in *.
        exploit FIT_ARGS.
        { ss. des_ifs. }
        clear FIT_ARGS. intro FIT_ARGS; des.
        clear - WF4 WF INIT_LOCALS UNIQF UNIQF0 FIT_ARGS.
        (* initLocals_type_spec  *)
        assert(NODUP: NoDup (getArgsIDs args1)).
        { inv UNIQF. ss.
          repeat match goal with
                 | [H: NoDup (_ ++ _) |- _ ] => eapply NoDup_split' in H; des
                 end.
          ss.
        } clear UNIQF UNIQF0.
        assert(forall arg (IN: In arg args0), exists id, In id (getArgsIDs args1) /\
                                                         lookupAL GenericValue g1 id = Some arg).
        { clear - NODUP INIT_LOCALS FIT_ARGS.
          unfold initLocals in *.
          i.
          ginduction args0; ii; ss.
          inv FIT_ARGS. ss. des_ifs.
          des.
          - clarify. ss.
            exists i0.
            split; ss.
            { left; ss. }
            rewrite lookupAL_updateAddAL_eq; ss. clarify.
          - exploit IHargs0; eauto.
            { apply NoDup_cons_iff in NODUP. des; ss. }
            i; des.
            exists id0.
            split; ss.
            { right. ss. }
            rewrite <- lookupAL_updateAddAL_neq; ss.
            ii. clarify.
            apply NoDup_cons_iff in NODUP. des; ss.
        }
        clear - H WF4.
        ginduction args0; ii; ss.
        - econs; eauto.
        - econs; eauto.
          exploit H; eauto; []; i; des.
          eapply WF4; eauto.
      }
      {
        exploit FIT_ARGS.
        { unfold get_params. ss. des_ifs. }
        intro FIT.
        eapply init_locals_wf_inv; eauto.
        { ss. des.
          apply NoDup_split in UNIQF0. des. ss.
        }
      }
      {
        exploit FIT_ARGS.
        { unfold get_params. ss. des_ifs. }
        intro FIT.
        eapply init_locals_wf_inv; eauto.
        { ss. des.
          apply NoDup_split in UNIQF0. des. ss.
        }
      }
      { econs; ss; eauto. }
      clear SIM. intro SIM_LOCAL; des.
      inv SIM_LOCAL. ss. clarify.




      esplits; eauto.
      + eapply sim_local_lift_sim; eauto.
        { eapply transl_products_sim_conf; eauto. }
        econs; ss; eauto.
        * econs; eauto.
        * eapply SIM_LOCAL0.
          { (* wf_src *)
            unsguard SRC_INIT_SUCCESS.
            expl s_genInitState__opsem_wf (try exact WF_SRC; eauto).
            split; ss.
          }
          { (* wf_tgt *)
            subst TGT_INIT1.
            expl s_genInitState__opsem_wf (try exact WF_TGT; eauto).
            split; ss.
          }
        * reflexivity.
  }
Unshelve.
all: try (by ss).
Qed.
