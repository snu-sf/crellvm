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

Lemma transl_sim_module:
  transl_module <2= sim_module.
Proof.
  s. intros module_src module_tgt MODULE.
  inv MODULE.
  ii. unfold s_genInitState in SRC. simtac.
  clear COND e0. apply infrastructure_props.InProductsB_In in e.
  exploit transl_products_lookupFdefViaIDFromProducts; eauto. i. des.
  destruct fdef_tgt. unfold LLVMinfra.is_true in *. simtac.
  destruct fheader5.
  inv FDEF.
  { inv NOP_FDEF.
    exploit lookupFdefViaIDFromProducts_ideq; eauto. i.
    assert (NOP_BLOCKS_ENTRY:
              exists phi' cmds' term' b',
                blocks5 = ((l0, stmts_intro phi' cmds' term')::b')).
    { inv BLOCKS.
      destruct y. destruct s.
      assert (LEQ: l1 = l0).
      {
        exploit transl_products_lookupFdefViaIDFromProducts; eauto. i. des.
        clarify.
      }
      subst.
      esplits; eauto.
    }
    des.
    esplits.
    - unfold s_genInitState. ss. rewrite TGT.
      match goal with
      | [|- context [productInModuleB_dec ?a ?b]] => destruct (productInModuleB_dec a b)
      end; simtac; cycle 1.
      { apply infrastructure_props.lookupFdefViaIDFromProducts_inv in TGT. congruence. }
      unfold initTargetData in *.
      erewrite <- transl_products_genGlobalAndInitMem; eauto. rewrite COND1.
      rewrite COND2.
      eauto.
    - apply sim_local_lift_sim.
      { unfold transl_products in TRANSL_PRODUCTS.
        econs.
        exact (SF_ADMIT "sim_conf"). }
      econs; ss.
      + econs.
      + apply nop_sim.
        * econs; eauto.
        * clarify.
          inv BLOCKS. des. clarify.
          econs; eauto.
          { econs; eauto.
            econs; eauto. }
          { econs. esplits; eauto.
            exact (SF_ADMIT "inject_locals"). }
          { econs. }
          { exact (SF_ADMIT "init mem"). }
      + reflexivity.
  }
  { ss. simtac.
    inv e0.
    esplits.
    - unfold s_genInitState. ss. rewrite TGT.
      match goal with
      | [|- context [productInModuleB_dec ?a ?b]] => destruct (productInModuleB_dec a b)
      end; simtac; cycle 1.
      { apply infrastructure_props.lookupFdefViaIDFromProducts_inv in TGT. congruence. }
      unfold initTargetData in *.
      erewrite <- transl_products_genGlobalAndInitMem; eauto. rewrite COND1.
      rewrite COND2. eauto.
    - apply sim_local_lift_sim.
      { exact (SF_ADMIT "sim_conf"). }
      econs; ss.
      + econs.
      + generalize VALID_FDEF. i.
        unfold forallb2AL in VALID_FDEF0. ss. apply andb_true_iff in VALID_FDEF0. des. simtac.
        { admit. (* gen_infrules *) }
        hexploit InvState.Rel.sem_empty; eauto.
        { exact (SF_ADMIT "init_locals inject_locals"). }
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
          des_ifs.
          { simtac.
            match goal with
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
        * ss. exact (SF_ADMIT "InvMem.Rel.sem init_mem").
      + reflexivity.
  }
Unshelve.
{ apply empty_invmem. }
{ apply 0%nat. }
{ apply empty_invmem. }
(* Qed. *)
Admitted.
