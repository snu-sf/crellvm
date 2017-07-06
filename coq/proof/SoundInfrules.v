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
Require Import Validator.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.
Require Import TODOProof.
Require Import SoundInfruleIntroGhost.
Require Import SoundInfruleSubstitute.
Require Import SoundInfruleTransitivity.

Set Implicit Arguments.

Lemma apply_infrule_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem0 inv0
      infrule
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem0):
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem1
                              (Infrules.apply_infrule m_src m_tgt infrule inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  destruct infrule.
  - ADMIT "add_commutative_tgt".
  - ADMIT "add_const_not".
  - ADMIT "add_dist_sub".
  - ADMIT "add_sub".
  - ADMIT "add_mask".
  - ADMIT "add_onebit".
  - ADMIT "add_or_and".
  - ADMIT "add_select_zero".
  - ADMIT "add_select_zero2".
  - ADMIT "add_shift".
  - ADMIT "add_signbit".
  - ADMIT "add_xor_and".
  - ADMIT "add_zext_bool".
  - ADMIT "and_de_morgan".
  - ADMIT "and_mone".
  - ADMIT "and_not".
  - ADMIT "and_or".
  - ADMIT "and_or_const2".
  - ADMIT "and_same".
  - ADMIT "and_true_bool".
  - ADMIT "and_true_bool_tgt".
  - ADMIT "and_undef".
  - ADMIT "and_xor_const".
  - ADMIT "and_zero".
  - ADMIT "and_or_not1".
  - ADMIT "bop_associative".
  - ADMIT "bop_commutative".
  - ADMIT "bop_commutative_rev".
  - ADMIT "bop_commutative_tgt".
  - ADMIT "bop_commutative_rev_tgt".
  - ADMIT "fbop_commutative".
  - ADMIT "fbop_commutative_rev".
  - ADMIT "fbop_commutative_tgt".
  - ADMIT "fbop_commutative_rev_tgt".
  - ADMIT "bop_distributive_over_selectinst".
  - ADMIT "bop_distributive_over_selectinst2".
  - ADMIT "bitcastptr".
  - ADMIT "bitcast_bitcast".
  - ADMIT "bitcast_bitcast_rev_tgt".
  - ADMIT "bitcast_double_i64".
  - ADMIT "bitcast_load".
  - ADMIT "bitcast_fpext".
  - ADMIT "bitcast_fptosi".
  - ADMIT "bitcast_fptoui".
  - ADMIT "bitcast_fptrunc".
  - ADMIT "bitcast_inttoptr".
  - ADMIT "bitcast_ptrtoint".
  - ADMIT "bitcast_sext".
  - ADMIT "bitcast_sametype".
  - ADMIT "bitcast_sitofp".
  - ADMIT "bitcast_trunc".
  - ADMIT "bitcast_uitofp".
  - ADMIT "bitcast_zext".
  - (* diffblock_unique *)
    exists invst0, invmem0. splits; eauto; [|reflexivity].
    ss. des_ifs.
    inv STATE. econs; eauto. ss.
    inv SRC. econs; eauto. ss.
    inv NOALIAS. econs; eauto. ss.
    ii. apply Exprs.ValueTPairSetFacts.mem_iff in MEM0.
    repeat (apply Exprs.ValueTPairSetFacts.add_iff in MEM0; des; subst).
    + apply orb_prop in Heq.
      admit.
    + apply orb_prop in Heq.
      admit.
    + eapply (DIFFBLOCK val1 gval1 val2 gval2); eauto.
      eapply Exprs.ValueTPairSetFacts.mem_iff. eauto.
  - ADMIT "!diffblock_global_unique".
  - ADMIT "!diffblock_global_global".
  - ADMIT "!diffblock_lessthan".
  - ADMIT "!diffblock_noalias".
  - ADMIT "fadd_commutative_tgt".
  - ADMIT "fbop_distributive_over_selectinst".
  - ADMIT "fbop_distributive_over_selectinst2".
  - ADMIT "fmul_commutative_tgt".
  - ADMIT "fpext_bitcast".
  - ADMIT "fpext_fpext".
  - ADMIT "fptosi_bitcast".
  - ADMIT "fptosi_fpext".
  - ADMIT "fptoui_bitcast".
  - ADMIT "fptoui_fpext".
  - ADMIT "fptrunc_bitcast".
  - ADMIT "fptrunc_fpext".
  - ADMIT "gepzero".
  -
    exists invst0, invmem0. splits; eauto; [|reflexivity].
    inv STATE. econs; eauto. ss.
    inv SRC. econs; eauto. ss.
    ii.
    destruct gepinst.
    unfold Debug.debug_string, Debug.debug_print2 in H;
      apply LESSDEF; auto.
    unfold Debug.debug_string, Debug.debug_print2 in H;
      apply LESSDEF; auto.
    unfold Debug.debug_string, Debug.debug_print2 in H;
      apply LESSDEF; auto.
    unfold Debug.debug_string, Debug.debug_print2 in H;
      apply LESSDEF; auto.
    admit.
    unfold Debug.debug_string, Debug.debug_print2 in H;
      apply LESSDEF; auto.
    unfold Debug.debug_string, Debug.debug_print2 in H;
      apply LESSDEF; auto.
    unfold Debug.debug_string, Debug.debug_print2 in H;
      apply LESSDEF; auto.
   unfold Debug.debug_string, Debug.debug_print2 in H;
     apply LESSDEF; auto.
   unfold Debug.debug_string, Debug.debug_print2 in H;
     apply LESSDEF; auto.
   unfold Debug.debug_string, Debug.debug_print2 in H;
     apply LESSDEF; auto.
   unfold Debug.debug_string, Debug.debug_print2 in H;
     apply LESSDEF; auto.
   unfold Debug.debug_string, Debug.debug_print2 in H;
     apply LESSDEF; auto.
   admit. admit. admit. admit. admit. admit.
  - ADMIT "gep_inbounds_add".
  - ADMIT "inttoptr_bitcast".
  - ADMIT "inttoptr_ptrtoint".
  - ADMIT "inttoptr_zext".
  - ADMIT "inttoptr_load".
  - (* lessthan_undef *)
    admit.
  - (* lessthan_undef_tgt *)
    admit.
  - (* lessthan_undef_const *)
    (* exists invst0, invmem0. splits; eauto; [|reflexivity]. *)
    (* destruct c eqn:C; (try destruct floating_point5); *)
    (*   (try (inv STATE; econs; eauto; *)
    (*   ss; inv SRC; econs; eauto; ss; *)
    (*   ii; apply Exprs.ExprPairSetFacts.add_iff in H; des)); *)
    (* (try (subst; esplits; ss; eauto; *)
    (*   eapply all_undef_lessdef_aux; apply const2GV_undef in VAL1; des; eauto; *)
    (*   unfold flatten_typ in VAL1; simpl in VAL1; destruct (CurTargetData conf_src); *)
  (*     inv VAL1; eauto)); (try (eapply LESSDEF; auto)). *)
    admit.
  - (* lessthan_undef_const_tgt *)
    admit.
    (* exists invst0, invmem0. splits; eauto; [|reflexivity]. *)
    (* destruct c eqn:C; (try destruct floating_point5); *)
    (*   (try (inv STATE; econs; eauto; *)
    (*   ss; inv TGT; econs; eauto; ss; *)
    (*   ii; apply Exprs.ExprPairSetFacts.add_iff in H; des)); *)
    (* (try (subst; esplits; ss; eauto; *)
    (*   eapply all_undef_lessdef_aux; apply const2GV_undef in VAL1; des; eauto; *)
    (*   unfold flatten_typ in VAL1; simpl in VAL1; destruct (CurTargetData conf_tgt); *)
    (*     inv VAL1; eauto)); (try (eapply LESSDEF; auto)). *)
  - admit.
    (* ADMIT "lessthan_undef_const_gep_or_cast" *)
  - ADMIT "mul_bool".
  - ADMIT "mul_mone".
  - ADMIT "mul_neg".
  - ADMIT "mul_shl".
  - ADMIT "neg_val".
  - ADMIT "or_and".
  - ADMIT "or_and_xor".
  - ADMIT "or_commutative_tgt".
  - ADMIT "or_false".
  - ADMIT "or_false_tgt".
  - ADMIT "or_mone".
  - ADMIT "or_not".
  - ADMIT "or_or ".
  - ADMIT "or_or2 ".
  - ADMIT "or_same".
  - ADMIT "or_undef".
  - ADMIT "or_xor".
  - ADMIT "or_xor2".
  - ADMIT "or_xor3".
  - ADMIT "or_xor4".
  - ADMIT "or_zero".
  - ADMIT "ptrtoint_bitcast".
  - ADMIT "ptrtoint_inttoptr".
  - ADMIT "ptrtoint_load".
  - ADMIT "ptrtoint_zero".
  - ADMIT "!replace_rhs".
  - ADMIT "!replace_rhs_opt".
  - ADMIT "rem_neg".
  - ADMIT "sdiv_mone".
  - ADMIT "sdiv_sub_srem".
  - ADMIT "select_icmp_eq".
  - ADMIT "select_icmp_eq_xor1".
  - ADMIT "select_icmp_eq_xor2".
  - ADMIT "select_icmp_ne".
  - ADMIT "select_icmp_ne_xor1".
  - ADMIT "select_icmp_ne_xor2".
  - ADMIT "select_icmp_sgt_const".
  - ADMIT "select_icmp_sgt_xor1".
  - ADMIT "select_icmp_sgt_xor2".
  - ADMIT "select_icmp_slt_const".
  - ADMIT "select_icmp_slt_xor1".
  - ADMIT "select_icmp_slt_xor2".
  - ADMIT "select_icmp_slt_one".
  - ADMIT "select_icmp_ugt_const".
  - ADMIT "select_icmp_ult_const".
  - ADMIT "sext_bitcast".
  - ADMIT "sext_sext".
  - ADMIT "sext_trunc_ashr".
  - ADMIT "sext_zext".
  - ADMIT "shift_undef1".
  - ADMIT "shift_undef2".
  - ADMIT "shift_zero1".
  - ADMIT "shift_zero2".
  - ADMIT "sitofp_bitcast".
  - ADMIT "sitofp_sext".
  - ADMIT "sitofp_zext".
  - ADMIT "sub_add".
  - ADMIT "sub_const_add".
  - ADMIT "sub_const_not".
  - ADMIT "sub_mone".
  - ADMIT "sub_onebit".
  - ADMIT "sub_or_xor".
  - ADMIT "sub_remove".
  - ADMIT "sub_sdiv".
  - ADMIT "sub_sub".
  - ADMIT "sub_shl".
  - (* transitivity *)
    exists invst0, invmem0. splits; eauto; [|reflexivity].
    ss.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c eqn:C
    end; ss.
    inv STATE. econs; eauto. ss. clear TGT MAYDIFF ALLOCAS.
    (* inv SRC. econs; eauto. ss. clear NOALIAS UNIQUE PRIVATE ALLOCAS_PARENT ALLOCAS_VALID *)
    (*                                  WF_LOCAL WF_PREVIOUS WF_GHOST UNIQUE_PARENT_LOCAL WF_FDEF WF_EC. *)
    econs; try apply SRC; eauto; ss.
    red. i. apply Exprs.ExprPairSetFacts.add_iff in H.
    des; cycle 1.
    { eapply SRC; eauto. }
    destruct x; ss. clarify.
    rename t into __e0__.
    rename e2 into __e1__.
    rename t0 into __e2__.
    des_bool; des.
    abstr (InvState.Rel.src invst0) invst.
    (* abstr (Hints.Invariant.lessdef (Hints.Invariant.src inv0)) LD. *)
    clear MEM CONF. clear_tac.
    assert(LD01: InvState.Unary.sem_lessdef conf_src st_src invst (__e0__, __e1__)).
    { clear C0. repeat (des_bool; des).
      - eapply InvState.Rel.lessdef_expr_spec2; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
    }
    assert(LD12: InvState.Unary.sem_lessdef conf_src st_src invst (__e1__, __e2__)).
    { clear C. repeat (des_bool; des).
      - eapply InvState.Rel.lessdef_expr_spec2; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
    }
    eapply InvState.Unary.sem_lessdef_trans; eauto.
  - (* transitivity_tgt *)
    exists invst0, invmem0.
    esplits; eauto; [ | reflexivity ].
    ss.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c eqn:C
    end; ss.
    econs; eauto; try apply STATE. ss.
    inv STATE. clear - TGT C.
    des_bool; des.
    abstr (InvState.Rel.tgt invst0) invst.
    econs; try apply TGT; eauto; ss.
    red. i. apply Exprs.ExprPairSetFacts.add_iff in H.
    des; cycle 1.
    { eapply TGT; eauto. }
    destruct x; ss. clarify.
    rename t into __e0__.
    rename e2 into __e1__.
    rename t0 into __e2__.
    assert(LD01: InvState.Unary.sem_lessdef conf_tgt st_tgt invst (__e0__, __e1__)).
    { clear C0. repeat (des_bool; des).
      - eapply InvState.Rel.lessdef_expr_spec2; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
    }
    assert(LD12: InvState.Unary.sem_lessdef conf_tgt st_tgt invst (__e1__, __e2__)).
    { clear C. repeat (des_bool; des).
      - eapply InvState.Rel.lessdef_expr_spec2; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
      - eapply InvState.Rel.lessdef_expr_spec2; eauto;
          repeat rewrite <- load_realign_sem_expr; eauto.
    }
    eapply InvState.Unary.sem_lessdef_trans; eauto.
  - (* transitivity-pointer-lhs *)
    exists invst0, invmem0. splits; eauto; [|reflexivity].
    ss.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c eqn:C
    end; ss.
    econs; eauto; try apply STATE. ss.
    inv STATE. clear - C SRC.
    des_bool. des.
    rename p into from. rename q into to.
    hexploit InvState.Rel.lessdef_expr_spec2; eauto. intro LD0; des. clear C0.
    hexploit InvState.Rel.lessdef_expr_spec2; eauto. intro LD1; des. clear C.
    rename v into v0.
    destruct from; ss; cycle 1.
    { econs; eauto; try apply SRC.
      inv SRC. clear - LESSDEF LD0 LD1.
      ii. ss.
      apply Exprs.ExprPairSetFacts.add_iff in H. des.
      - clarify. ss. des_ifs.
        exploit LD1; eauto. i; des. ss.
        eapply LD0; eauto. ss. des_ifs.
        eapply InvState.Rel.mload_lessdef_sim_eq; eauto.
      - eapply LESSDEF; eauto.
    }
    rename x into from.
    exploit substitute_spec_unary; eauto.
    instantiate (1:= Exprs.Expr.load (Exprs.ValueT.id from) ty a).
    intro SRC1; des. ss. des_ifs.
    econs; eauto; try apply SRC1.
    (* inv SRC1. clear - LESSDEF LD0 LD1. ss. *)
    ii.
    apply Exprs.ExprPairSetFacts.add_iff in H. des.
    { clarify. ss. des_ifs.
      eapply LD0; eauto. ss.
      exploit LD1; eauto. i; des. ss.
      des_ifs.
      erewrite InvState.Rel.mload_lessdef_sim_eq; eauto.
    }
    destruct x; ss.
    hexploit InvState.Rel.lessdef_expr_spec; try apply H; eauto.
    { ss.
      eapply Exprs.ExprPairSetFacts.mem_iff; eauto.
      eapply Exprs.ExprPairSetFacts.add_iff; eauto.
    }
  - (* transitivity-pointer-rhs *)
    exists invst0, invmem0. splits; eauto; [|reflexivity].
    ss.
    match goal with
    | [|- context[if ?c then _ else _]] => destruct c eqn:C
    end; ss.
    econs; eauto; try apply STATE. ss.
    inv STATE. clear - C SRC.
    des_bool. des.
    rename p into from. rename q into to.
    hexploit InvState.Rel.lessdef_expr_spec2; eauto. intro LD0; des. clear C0.
    hexploit InvState.Rel.lessdef_expr_spec2; eauto. intro LD1; des. clear C.
    rename v into v0.
    destruct from; ss; cycle 1.
    { econs; eauto; try apply SRC.
      inv SRC. clear - LESSDEF LD0 LD1.
      ii. ss.
      apply Exprs.ExprPairSetFacts.add_iff in H. des.
      - clarify. ss.
        exploit LD0; eauto. i; des. ss. des_ifs_safe.
        exploit LD1; eauto. i; des. ss. des_ifs_safe.
        esplits; eauto.
        erewrite InvState.Rel.mload_lessdef_sim_eq; eauto.
      - eapply LESSDEF; eauto.
    }
    rename x into from.
    exploit substitute_spec_unary; eauto.
    instantiate (1:= Exprs.Expr.load (Exprs.ValueT.id from) ty a).
    intro SRC1; des. ss. des_ifs.
    econs; eauto; try apply SRC1.
    (* inv SRC1. clear - LESSDEF LD0 LD1. ss. *)
    ii.
    apply Exprs.ExprPairSetFacts.add_iff in H. des.
    {
      destruct x; ss. clarify.
      eapply InvState.Unary.sem_lessdef_trans; [apply LD0|..]; eauto; ss.
      ii. ss. des_ifs_safe.
      exploit LD1; eauto. i; des. ss.
      des_ifs_safe. clear - VAL0 VAL.
      erewrite InvState.Rel.mload_lessdef_sim_eq; eauto.
      esplits; eauto.
      apply GVs.lessdef_refl.
    }
    destruct x; ss.
    hexploit InvState.Rel.lessdef_expr_spec; try apply H; eauto.
    { ss.
      eapply Exprs.ExprPairSetFacts.mem_iff; eauto.
      eapply Exprs.ExprPairSetFacts.add_iff; eauto.
    }
  - ADMIT "trunc_onebit".
  - ADMIT "trunc_zext".
  - ADMIT "trunc_sext".
  - ADMIT "trunc_bitcast".
  - ADMIT "trunc_ptrtoint".
  - ADMIT "trunc_trunc".
  - ADMIT "trunc_trunc_rev_tgt".
  - ADMIT "trunc_load_bitcast_rev_tgt".
  - ADMIT "trunc_load_const_bitcast_rev_tgt".
  - (* substitute *)
    exists invst0, invmem0.
    esplits; eauto; [ | reflexivity ].
    ss. des_ifs.
    econs; eauto; try apply STATE.
    hexploit InvState.Rel.lessdef_expr_spec2; eauto; try apply STATE.
    intro LD; des. clear Heq.
    inv STATE. clear - SRC LD.
    eapply substitute_spec_unary; eauto.
  - (* substitute_rev *)
    exists invst0, invmem0.
    esplits; eauto; [ | reflexivity ].
    ss. des_ifs.
    econs; eauto; try apply STATE.
    hexploit InvState.Rel.lessdef_expr_spec2; eauto; try apply STATE.
    intro LD; des. clear Heq.
    inv STATE. clear - SRC LD.
    eapply substitute_spec_unary_rev; eauto.
  - (* substitute_tgt *)
    exists invst0, invmem0.
    esplits; eauto; [ | reflexivity ].
    ss. des_ifs.
    econs; eauto; try apply STATE.
    hexploit InvState.Rel.lessdef_expr_spec2; eauto; try apply STATE.
    intro LD; des. clear Heq.
    inv STATE. clear - TGT LD.
    eapply substitute_spec_unary; eauto.
  - ADMIT "udiv_sub_urem".
  - ADMIT "udiv_zext".
  - ADMIT "udiv_zext_const".
  - ADMIT "uitofp_bitcast".
  - ADMIT "uitofp_zext".
  - ADMIT "urem_zext".
  - ADMIT "urem_zext_const".
  - ADMIT "xor_commutative_tgt".
  - ADMIT "xor_not".
  - ADMIT "xor_same".
  - ADMIT "xor_undef".
  - ADMIT "xor_zero".
  - ADMIT "zext_bitcast".
  - ADMIT "zext_trunc_and".
  - ADMIT "zext_trunc_and_xor".
  - ADMIT "zext_xor".
  - ADMIT "zext_zext".
  - ADMIT "!intro_ghost_src".
  - ss. des_ifs; cycle 1.
    { esplits; eauto. reflexivity. }
    repeat (des_bool; des).
    rename g into i0.
    rename x into x0.
    Local Opaque InvState.Unary.clear_idt.
    destruct (InvState.Unary.sem_expr conf_src st_src
             (InvState.Rel.clear_idt (Exprs.Tag.ghost, i0) invst0).(InvState.Rel.src) x0) eqn:T0; cycle 1.
    {
      exists (InvState.Rel.clear_idt (Exprs.Tag.ghost, i0) invst0), invmem0.
      splits; ss; eauto; [|reflexivity].
      exploit clear_idt_ghost_spec; eauto.
      { instantiate (1:= (Exprs.Tag.ghost, i0)). ss. }
      intro STATE_CLEAR; des.
      clear - STATE_CLEAR T0.
      unfold Hints.Invariant.update_tgt, Hints.Invariant.update_src, Hints.Invariant.update_lessdef. ss.
      econs; eauto; try apply STATE_CLEAR.
      + ss.
        inv STATE_CLEAR. clear - SRC T0.

        econs; eauto; try apply SRC.
        ss.
        inv SRC. clear - LESSDEF T0.

        ii.
        apply Exprs.ExprPairSetFacts.add_iff in H. des.
        * clarify. ss. rewrite T0 in *. clarify.
        * eapply LESSDEF; eauto.
      + ss.
        inv STATE_CLEAR. clear - TGT T0.

        econs; eauto; try apply TGT.
        ss.
        inv TGT. clear - LESSDEF T0.

        ii.
        apply Exprs.ExprPairSetFacts.add_iff in H. des.
        * clarify. ss.
          assert(NONE: InvState.Unary.sem_idT
                         st_tgt (InvState.Rel.tgt
                                   (InvState.Rel.clear_idt
                                      (Exprs.Tag.ghost, i0) invst0)) (Exprs.Tag.ghost, i0) = None).
          { clear - i0.
            unfold InvState.Unary.sem_idT. ss.
            ss.
            Local Transparent InvState.Unary.clear_idt. ss.
            rewrite lookup_AL_filter_spec. des_ifs. des_bool; des_sumbool. ss.
            Local Opaque InvState.Unary.clear_idt.
          }
          unfold InvState.Rel.clear_idt in *. ss.
          rewrite NONE in *. clarify.
        * ss. eapply LESSDEF; eauto.
    }
    rename T0 into GV_SRC.
    rename g into gv_src.
    assert(GV_TGT: exists gv_tgt,
              InvState.Unary.sem_expr conf_tgt st_tgt
                   (InvState.Rel.clear_idt (Exprs.Tag.ghost, i0) invst0).(InvState.Rel.tgt) x0
              = Some gv_tgt
              /\ genericvalues_inject.gv_inject invmem0.(InvMem.Rel.inject) gv_src gv_tgt).
    {
      hexploit InvState.Rel.not_in_maydiff_expr_spec; try apply GV_SRC; try apply STATE; eauto.
      { ii.
        assert(id0 <> (Exprs.Tag.ghost, i0)).
        {
          ii. clarify. ss.
          exploit clear_idt_inv_spec_id; try eassumption; ss.
          i. unfold proj_sumbool in *. des_ifs.
        }
        ss.
        erewrite <- clear_idt_spec_id; ss; cycle 1.
        { unfold proj_sumbool. des_ifs. }
        inv STATE.
        eapply MAYDIFF; ss.
        erewrite clear_idt_spec_id; try eassumption; cycle 1.
        unfold proj_sumbool. des_ifs.
      }
    }
    des. rename GV_TGT0 into GV_INJ.
    des.

    exploit clear_idt_ghost_spec; eauto.
    { instantiate (1:= (Exprs.Tag.ghost, i0)). ss. }
    intro STATE_CLEAR; des.
    clear - STATE_CLEAR GV_SRC GV_TGT GV_INJ MEM.

    exists (cons_idt (Exprs.Tag.ghost, i0) gv_src gv_tgt
                     (InvState.Rel.clear_idt (Exprs.Tag.ghost, i0) invst0)), invmem0.
    splits; ss; eauto; [|reflexivity].
    {
      econs; eauto; try apply STATE_CLEAR.
      - ss.
        eapply Subset_unary_sem; eauto.
        eapply cons_ghost_unary_spec; try apply STATE_CLEAR; eauto.
        { eapply sem_expr_preserves_valid_ptr; try apply STATE_CLEAR; try apply MEM; eauto. }
        unfold compose.
        econs; ss; eauto.
        + ii. apply Exprs.ExprPairSetFacts.add_iff. right. ss.
        + split; ss.
      - ss.
        eapply Subset_unary_sem; eauto.
        eapply cons_ghost_unary_spec; try apply STATE_CLEAR; eauto.
        { eapply sem_expr_preserves_valid_ptr; try apply STATE_CLEAR; try apply MEM; eauto. }
        unfold compose.
        econs; ss; eauto.
        + ii.
          apply Exprs.ExprPairSetFacts.add_iff in H. des.
          { apply Exprs.ExprPairSetFacts.add_iff. left. ss. }
          apply Exprs.ExprPairSetFacts.add_iff. right.
          apply Exprs.ExprPairSetFacts.add_iff. right. ss.
        + split; ss.
      - i.
        unfold Hints.Invariant.update_lessdef in NOTIN. ss.
        inv STATE_CLEAR.
        clear SRC TGT TGT_NOUNIQ ALLOCAS.
        ii. ss.
        destruct (Exprs.IdT.eq_dec id0 (Exprs.Tag.ghost, i0)).
        { clarify.
          unfold InvState.Unary.sem_idT in *. ss. des_ifs.
          esplits; eauto.
        }
        erewrite <- cons_idt_spec_id in VAL_SRC; cycle 1.
        { unfold proj_sumbool; des_ifs. }
        erewrite <- cons_idt_spec_id; cycle 1.
        { unfold proj_sumbool; des_ifs. }
        eapply MAYDIFF; eauto.
    }
  - (* intro_eq *)
    exists invst0, invmem0. splits; eauto; [|reflexivity].
    inv STATE. econs; eauto. ss.
    inv SRC. econs; eauto. ss.
    ii. apply Exprs.ExprPairSetFacts.add_iff in H. des.
    + subst. esplits; eauto. apply GVs.lessdef_refl.
    + eapply LESSDEF; eauto.
  - (* intro_eq_tgt *)
    exists invst0, invmem0. splits; eauto; [|reflexivity].
    inv STATE. econs; eauto. ss.
    inv TGT. econs; eauto. ss.
    ii. apply Exprs.ExprPairSetFacts.add_iff in H. des.
    + subst. esplits; eauto. apply GVs.lessdef_refl.
    + eapply LESSDEF; eauto.
  - ADMIT "icmp_inverse".
  - ADMIT "icmp_inverse_rhs".
  - ADMIT "icmp_inverse_tgt".
  - ADMIT "icmp_inverse_rhs_tgt".
  - ADMIT "icmp_swap_operands".
  - ADMIT "icmp_swap_operands_rev".
  - ADMIT "icmp_swap_operands_tgt".
  - ADMIT "icmp_swap_operands_rev_tgt".
  - ADMIT "fcmp_swap_operands".
  - ADMIT "fcmp_swap_operands_rev".
  - ADMIT "fcmp_swap_operands_tgt".
  - ADMIT "fcmp_swap_operands_rev_tgt".
  - ADMIT "icmp_eq_add_add".
  - ADMIT "icmp_eq_same".
  - ADMIT "icmp_eq_same_tgt".
  - ADMIT "icmp_eq_sub_sub".
  - ADMIT "icmp_eq_xor_not".
  - ADMIT "icmp_eq_xor_xor".
  - ADMIT "icmp_eq_sub".
  - ADMIT "icmp_eq_srem".
  - ADMIT "icmp_ne_add_add".
  - ADMIT "icmp_ne_sub".
  - ADMIT "icmp_ne_sub_sub".
  - ADMIT "icmp_ne_srem".
  - ADMIT "icmp_ne_xor".
  - ADMIT "icmp_ne_xor_xor".
  - ADMIT "icmp_neq_same".
  - ADMIT "icmp_neq_same_tgt".
  - ADMIT "icmp_sge_or_not".
  - ADMIT "icmp_sgt_and_not".
  - ADMIT "icmp_sle_or_not".
  - ADMIT "icmp_slt_and_not".
  - ADMIT "icmp_uge_or_not".
  - ADMIT "icmp_ugt_and_not".
  - ADMIT "icmp_ule_or_not".
  - ADMIT "icmp_ult_and_not".
  - ADMIT "!implies_false".
  - (* remove_maydiff *)
    exists invst0, invmem0. splits; eauto. reflexivity.
    (* remove it *)
  - (* remove_maydiff_rhs *)
    exists invst0, invmem0. splits; eauto. reflexivity.
    (* remove it *)
  - ADMIT "!stash_variable".
  - ADMIT "add_mul_fold".
  - ADMIT "add_distributive".
  - ADMIT "rem_neg2".
  - ADMIT "select_trunc".
  - ADMIT "select_add".
  - ADMIT "select_const_gt".
  - ADMIT "cmp_eq_sub".
  - ADMIT "cmp_ne_sub".
  - ADMIT "cmp_eq_srem".
  - ADMIT "cmp_eq_srem2".
  - ADMIT "cmp_ne_srem".
  - ADMIT "cmp_ne_srem2".
  - ADMIT "cmp_eq_xor".
  - ADMIT "cmp_ne_xor".
Admitted.

(*  ADMIT "Infrule
We will not prove soundness of infrules in this submission.
All the infrules are simple, and we carefully installed it, so it is less likely to introduce a bug.
Also, even in case some infrules contain bugs, the bugs does not affect the whole system,
and it should be easy to fix. Moreover, we did prove most of the infrules in the former version of simplberry.
To our experience, proving infrules can be done withn reasonable amount of engineering effort (maybe 2 weeks)
by using automation techniques. However, we skip it for now.".
Qed.*)

Lemma apply_infrules_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem0 inv0
      infrules
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem0 inv0)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem0):
  exists invst1 invmem1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem1
                              (Infrules.apply_infrules m_src m_tgt infrules inv0)>> /\
    <<MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem1>> /\
    <<MEMLE: InvMem.Rel.le invmem0 invmem1>>.
Proof.
  unfold Infrules.apply_infrules. rewrite <- fold_left_rev_right.
  move infrules at top. revert_until infrules. induction (rev infrules); i.
  - esplits; eauto. reflexivity.
  - exploit IHl0; eauto. i. des.
    exploit apply_infrule_sound; eauto. i. des.
    esplits; eauto.
    etransitivity; eauto.
Qed.
