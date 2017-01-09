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

(* Definition transl_products m_src m_tgt prods_src prods_tgt : Prop := *)
(*   forall prod_src (IN_SRC: In prod_src prods_src), *)
(*   exists prod_tgt, *)
(*     <<IN_TGT: In prod_tgt prods_tgt>> /\ *)
(*     <<TRANSL_PRODUCT: transl_product m_src m_tgt prod_src prod_tgt>>. *)

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

(* Lemma valid_products_lookupFdefViaIDFromProducts *)
(*       m_hint m_src m_tgt *)
(*       products_src products_tgt *)
(*       f fdef_src *)
(*       (PRODUCTS: valid_products m_hint m_src m_tgt products_src products_tgt) *)
(*       (SRC: lookupFdefViaIDFromProducts products_src f = Some fdef_src): *)
(*   exists fdef_tgt, *)
(*     <<TGT: lookupFdefViaIDFromProducts products_tgt f = Some fdef_tgt>> /\ *)
(*     <<FDEF: valid_product m_hint m_src m_tgt (product_fdef fdef_src) (product_fdef fdef_tgt)>>. *)
(* Proof. *)
(*   revert products_tgt PRODUCTS SRC. *)
(*   induction products_src; [done|]. *)
(*   i. destruct products_tgt; [done|]. *)
(*   unfold valid_products in PRODUCTS. s in PRODUCTS. apply andb_true_iff in PRODUCTS. des. *)
(*   s in SRC. simtac. *)
(*   - destruct a, p; simtac. esplits; eauto. *)
(*     + destruct (getFdefID fdef0 == getFdefID fdef_src); eauto. congruence. *)
(*     + destruct (id_dec (getFdefID fdef_src) (getFdefID fdef0)); ss. *)
(*       destruct (valid_fdef m_src m_tgt fdef_src fdef0 f0) eqn:FDEF; ss. congruence. *)
(*   - destruct a, p; simtac. congruence. *)
(*   - exploit IHproducts_src; eauto. i. des. *)
(*     esplits; eauto. *)
(*     destruct (lookupFdefViaIDFromProduct p f) eqn:HD; ss. *)
(*     destruct a, p; simtac. *)
(*   - exploit IHproducts_src; eauto. i. des. *)
(*     esplits; eauto. *)
(*     destruct (lookupFdefViaIDFromProduct p f) eqn:HD; ss. *)
(*     destruct a, p; simtac. *)
(* Qed. *)

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
Admitted.

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
  { admit. (* nop *) }
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
      { admit. (* sim_conf *) }
      econs; ss.
      + econs.
      + generalize VALID_FDEF. i.
        unfold forallb2AL in VALID_FDEF0. ss. apply andb_true_iff in VALID_FDEF0. des. simtac.
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
        * ss. admit. (* InvMem.Rel.sem init_mem *)
      + reflexivity.
Admitted.
