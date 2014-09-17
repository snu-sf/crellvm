Require Import vgtac.

Require Import vellvm.
Require Import program_sim.

Require Import syntax_ext.
Require Import validator_aux.
Require Import validator.
Require Import validator_props.
Require Import logical_step.
Require Import state_props.
Require Import hints.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import syntax_ext.
Require Import basic_const_inject.

Require Import hint_sem_props_implies.
Require Import hint_sem_props_resolve_defs.
Require Import hint_sem_props_resolve.
Require Import hint_sem_props_proceed.
Require Import hint_sem_props_proceed_call.
Require Import hint_sem_props_proceed_call_void.
Require Import hint_sem_props_proceed_branch.

Require Import lopsem.
Require Import simulation_local.
Require Import excall.
Require Import paco.

Import Opsem.

Section Sems.
  Variable (cfg1 cfg2: Config).
  Variable (lc1 lc2: @GVsMap DGVs).
  Variable (Mem1 Mem2: mem).

  Definition eqs_sem_nomem (cfg: Config) (olc: @GVsMap DGVs) (lc: @GVsMap DGVs)
    (Mem:mem) (gmax: Z) (e:eqs_t) : Prop :=
    eqs_eq_reg_sem cfg olc lc Mem gmax (eqs_eq_reg e) /\
    eqs_neq_reg_sem cfg olc lc (eqs_neq_reg e).
  
  Definition invariant_sem_nomem (olc1 olc2: @GVsMap DGVs)
    (gmax: Z) (li1 li2: list mblock)
    (inv: hints.invariant_t) : Prop := 
    eqs_sem_nomem cfg1 olc1 lc1 Mem1 gmax (invariant_original inv) /\
    eqs_sem_nomem cfg2 olc2 lc2 Mem2 gmax (invariant_optimized inv) /\
    isolated_sem (CurTargetData cfg1) olc1 lc1 li1 (iso_original inv) /\
    isolated_sem (CurTargetData cfg2) olc2 lc2 li2 (iso_optimized inv).

  Definition hint_sem_nomem (alpha: meminj) (gmax: Z) (li1 li2: list mblock)
    (h: hints.insn_hint_t) : Prop :=
    exists olc1, exists olc2,
      maydiff_sem lc1 lc2 alpha olc1 olc2 (hint_maydiff h) /\
      invariant_sem_nomem olc1 olc2 gmax li1 li2 (hint_invariant h).
End Sems.

Section Relations.
  Variable
    (m1 m2:module)
    (cfg1 cfg2:OpsemAux.Config)
    (Hmatch: matched_module_cfg m1 m2 cfg1 cfg2)
    (Hcfg1: OpsemPP.wf_Config cfg1)
    (Hcfg2: OpsemPP.wf_Config cfg2)
    (fn_al1 fn_al2:AssocList fdef_noop_t)
    (fh_al:hints.products_hint_t)
    (gmax:Z).

  Variable
    (Hgna1: globals_no_alias (Globals cfg1))
    (Hgna2: globals_no_alias (Globals cfg2))
    (Htd: CurTargetData cfg1 = CurTargetData cfg2).
  
  Variable
    (Hvalid_products1_1:
     forall id fd1 (Hfdef1: ret fd1 = lookupFdefViaIDFromProducts (CurProducts cfg1) id),
     exists fd2,
     ret fd2 = lookupFdefViaIDFromProducts (CurProducts cfg2) id)
    (Hvalid_products1_2:
     forall id fd2 (Hfdef2: ret fd2 = lookupFdefViaIDFromProducts (CurProducts cfg2) id),
     exists fd1,
     ret fd1 = lookupFdefViaIDFromProducts (CurProducts cfg1) id)
    (Hvalid_products2:
     forall id,
       lookupFdecViaIDFromProducts (CurProducts cfg1) id =
       lookupFdecViaIDFromProducts (CurProducts cfg2) id).

  Fixpoint concat {A} (l: list (list A)) : list A :=
    match l with
      | nil => nil
      | a::l => a ++ (concat l)
    end.

  Inductive hint_sem_insn_nomem
    (hint: insn_hint_t)
    (pecs1 pecs2: @ECStack DGVs) (pns1 pns2: noop_stack_t)
    (pi1 pi2: list mblock) (li1 li2: list mblock) :
    meminj -> Z ->
    OpsemAux.Config -> (@ECStack DGVs) -> mem -> noop_stack_t -> 
    OpsemAux.Config -> (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
  | hint_sem_insn_intro :
    forall alpha gmax cfg1 cfg2 mem1 mem2 ec1 ec2 n1 n2
      (Hsem: hint_sem_nomem cfg1 cfg2 (Locals ec1) (Locals ec2)
        mem1 mem2 alpha gmax li1 li2 hint)
      (Haequiv: allocas_equivalent alpha li1 li2 (Allocas ec1) (Allocas ec2))
      (Hgequiv: globals_equivalent alpha gmax (Globals cfg1) (Globals cfg2))
      (Hvals: valid_allocas mem1 mem2 (Allocas ec1) (Allocas ec2))
      (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2),
      hint_sem_insn_nomem hint pecs1 pecs2 pns1 pns2 pi1 pi2 li1 li2
      alpha gmax cfg1 (ec1::pecs1) mem1 (n1::pns1)
      cfg2 (ec2::pecs2) mem2 (n2::pns2).

  Inductive readonly_gen m cfg (rel: (@State DGVs) -> list (monad mem) -> Prop) :
    (@State DGVs) -> list (monad mem) -> Prop :=
  | readonly_gen_ordinary :
    forall st mems
      (Hncall: forall fid, ~ is_call cfg st fid)
      (Hnret: ~ is_return st)
      (Hnext: forall st' tr (Hstep: sInsn cfg st st' tr),
        (if is_call_readonly''' m st
         then memory_extends (CurTargetData cfg) (Mem st') (Mem st)
         else True) /\
        rel st' mems),
      readonly_gen m cfg rel st mems
  | readonly_gen_call :
    forall st mems
      st' tr (Hstep: sInsn cfg st st' tr)
      fid (Hcall: is_call cfg st fid)
      (Hst': rel st'
        ((if is_call_readonly''' m st
          then ret (Mem st)
          else merror)::mems)),
      readonly_gen m cfg rel st mems
  | readonly_gen_return :
    forall st mem mems
      st' tr (Hstep: sInsn cfg st st' tr)
      (Hret: is_return st)
      (Hextends: match mem with
                   | ret mem => memory_extends (CurTargetData cfg) (Mem st') mem
                   | merror => True
                 end)
      (Hst': rel st' mems),
      readonly_gen m cfg rel st (mem::mems)
  .

  Lemma readonly_gen_mon m cfg: monotone2 (readonly_gen m cfg).
  Proof.
    ii. inv IN.
    - eapply readonly_gen_ordinary; eauto.
      intros. exploit Hnext; eauto. intros [? ?]. split; auto.
    - by eapply readonly_gen_call; eauto.
    - by eapply readonly_gen_return; eauto.
  Qed.
  Hint Resolve readonly_gen_mon: paco.

  Definition readonly m cfg : (@State DGVs) -> list (monad mem) -> Prop :=
    paco2 (readonly_gen m cfg) bot2.

  Lemma readonly_ordinary m cfg st mems
    (Hncall: forall fid : id, ~ is_call cfg st fid)
    (Hnret: ~ is_return st)
    (Hrd: readonly m cfg st mems)
    st' tr (Hstep: sInsn cfg st st' tr) :
    (if is_call_readonly''' m st
     then memory_extends (CurTargetData cfg) (Mem st') (Mem st)
     else True) /\
    readonly m cfg st' mems.
  Proof.
    punfold Hrd. inv Hrd.
    - exploit Hnext; eauto. intros [? ?]. by pclearbot.
    - exfalso. by eapply Hncall; eauto.
    - exfalso. by apply Hnret.
  Qed.

  Lemma readonly_ordinary' m cfg pnoops st n ns mems
    (Hncall: forall fid : id, ~ is_call cfg st fid)
    (Hnret: ~ is_return st)
    (Hrd: readonly m cfg st mems)
    (Hn: noop_idx_zero_exists n = false)
    st' ns' na tr (Hstep: logical_semantic_step cfg pnoops st st' (n::ns) ns' na tr) :
    (if is_call_readonly''' m st
     then memory_extends (CurTargetData cfg) (Mem st') (Mem st)
     else True) /\
    readonly m cfg st' mems.
  Proof.
    inv Hstep. inv Hpn. destruct st as [ecs' mem]. simpl in Hec. subst.
    destruct ec.
    inv Hpop; unfold pop_one_X in *; rewrite Hn in *.
    - destruct CurCmds0; [done|]. simpl in *. inv Hpop0.
      eapply readonly_ordinary; eauto.
    - destruct CurCmds0; [|done]. simpl in *. inv Hpop0.
      eapply readonly_ordinary; eauto.
  Qed.    

  Lemma readonly_ordinary'' m cfg pnoops st ns mems
    (Hord: is_ordinary cfg st ns)
    (Hrd: readonly m cfg st mems)
    st' ns' na tr (Hstep: logical_semantic_step cfg pnoops st st' ns ns' na tr) :
    readonly m cfg st' mems.
  Proof.
    destruct st as [ecs mem]. remember Hstep as H. inv H. simpl in Hec. subst.
    remember (noop_idx_zero_exists hpn) as zn. destruct zn.
    - inv Hpop; unfold pop_one_X in *; rewrite <- Heqzn in *; [|by inv Hpop0].
      inv Hpop0. destruct Hstep0. by subst.
    - inv Hord.
      + apply stutter_num_noop_idx_zero_exists in Hstut.
        inv Hns. by rewrite <- Heqzn in Hstut.
      + eapply readonly_ordinary'; eauto.
  Qed.

  Lemma readonly_call m cfg st mems
    fid (Hcall: is_call cfg st fid)
    (Hrd: readonly m cfg st mems)
    st' tr (Hstep: sInsn cfg st st' tr) :
    readonly m cfg st'
    ((if is_call_readonly''' m st
      then ret (Mem st)
      else merror)::mems).
  Proof.
    punfold Hrd. inv Hrd.
    - exfalso. by eapply Hncall; eauto.
    - pclearbot.
      destruct st as [[|ec ecs] mem]; [done|].
      destruct ec. destruct CurCmds0 as [|c cmds]; [done|].
      destruct c; try done. simpl in *.
      exploit call_uniq; [apply Hcall|apply Hcall0|]. intro. subst.
      rewrite (destruct_cfg cfg) in Hstep, Hstep0.
      inv Hstep.
      + inv Hstep0.
        * rewrite H21 in H27. inv H27.
          inv H22. inv H28.
          rewrite H23 in H29. inv H29.
          rewrite H24 in H30. inv H30.
          rewrite H25 in H31. inv H31.
          rewrite H26 in H32. inv H32.
          done.
        * by exploit call_excall'; eauto.
      + by exploit call_excall'; eauto.
    - destruct st as [[|ec ecs] mem]; [done|].
      destruct ec. destruct CurCmds0 as [|c cmds]; [done|].
      by inv Hret.
  Qed.

  Lemma readonly_call' m cfg pnoops st n ns mems
    fid (Hcall: is_call cfg st fid)
    (Hrd: readonly m cfg st mems)
    (Hn: noop_idx_zero_exists n = false)
    st' ns' na tr (Hstep: logical_semantic_step cfg pnoops st st' (n::ns) ns' na tr) :
    readonly m cfg st'
    ((if is_call_readonly''' m st
      then ret (Mem st)
      else merror)::mems).
  Proof.
    inv Hstep. inv Hpn. destruct st as [ecs' mem]. simpl in Hec. subst.
    destruct ec. destruct CurCmds0; [done|]. simpl in *.
    inv Hpop; unfold pop_one_X in *; rewrite Hn in *; inv Hpop0.
    eapply readonly_call; eauto.
  Qed.

  Lemma readonly_return m cfg st mem mems
    (Hret: is_return st)
    (Hrd: readonly m cfg st (mem::mems))
    st' tr (Hstep: sInsn cfg st st' tr) :
    (match mem with
       | ret mem => memory_extends (CurTargetData cfg) (Mem st') mem
       | merror => True
     end) /\
    readonly m cfg st' mems.
  Proof.
    punfold Hrd. inv Hrd.
    - exfalso. by eapply Hnret; eauto.
    - idtac. destruct st as [[|ec ecs] mem']; [done|].
      destruct ec. destruct CurCmds0 as [|c cmds]; [done|].
      by inv Hret.
    - pclearbot.
      destruct st as [[|ec ecs] mem']; [done|].
      destruct ec. destruct CurCmds0 as [|c cmds]; [|by inv Hret].
      rewrite (destruct_cfg cfg) in Hstep, Hstep0.
      destruct Hret as [? ?]. simpl in *. destruct Terminator0; try done.
      + inv Hstep. inv Hstep0. simpl in *.
        rewrite H18 in H28. inv H28.
        rewrite H19 in H29. inv H29.
        done.
      + inv Hstep. inv Hstep0. simpl in *.
        rewrite H16 in H26. inv H26.
        rewrite H17 in H27. inv H27.
        done.
  Qed.

  Lemma readonly_return' m cfg pnoops st n ns mem mems
    (Hret: is_return st)
    (Hrd: readonly m cfg st (mem::mems))
    (Hn: noop_idx_zero_exists n = false)
    st' ns' na tr (Hstep: logical_semantic_step cfg pnoops st st' (n::ns) ns' na tr) :
    (match mem with
       | ret mem => memory_extends (CurTargetData cfg) (Mem st') mem
       | merror => True
     end) /\
    readonly m cfg st' mems.
  Proof.
    inv Hstep. inv Hpn. destruct st as [ecs' mem']. simpl in Hec. subst.
    destruct ec. destruct Hret as [? Hret]. simpl in *. subst.
    inv Hpop; unfold pop_one_X in *; rewrite Hn in *; inv Hpop0.
    eapply readonly_return; eauto.
    by split.
  Qed.
  
  Inductive hint_sem_global_bot :
    list (monad mem) -> list (monad mem) ->
    mem -> mem -> meminj ->
    list (list mblock) -> list (list mblock) ->
    (@ECStack DGVs) -> noop_stack_t ->
    (@ECStack DGVs) -> noop_stack_t ->
    Prop :=
  | hint_sem_global_bot_nil :
    forall mem1 mem2 alpha,
    hint_sem_global_bot nil nil mem1 mem2 alpha nil nil nil nil nil nil
  | hint_sem_global_bot_cons :
    forall mems1 mems2 mem1 mem2 alpha li1 pi1 li2 pi2 fid bid
      ec1 phis1 all_cmds1 cmds1 term1 locals1 allocas1 pecs1 n1 pns1
      ec2 phis2 all_cmds2 cmds2 term2 locals2 allocas2 pecs2 n2 pns2
      fdef1 (Hfdef1: ret fdef1 = lookupFdefViaIDFromProducts (CurProducts cfg1) fid)
      fdef2 (Hfdef2: ret fdef2 = lookupFdefViaIDFromProducts (CurProducts cfg2) fid)
      fh (Hfh: ret fh = lookupAL _ fh_al fid)
      (Hec1: ec1 = mkEC fdef1 (bid, stmts_intro phis1 all_cmds1 term1) cmds1 term1 locals1 allocas1)
      (Hec2: ec2 = mkEC fdef2 (bid, stmts_intro phis2 all_cmds2 term2) cmds2 term2 locals2 allocas2)
      (Hstmts1: ret (stmts_intro phis1 all_cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid)
      (Hstmts2: ret (stmts_intro phis2 all_cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)
      id1 noret1 clattrs1 typ1 varg1 value1 params1
      id2 noret2 clattrs2 typ2 varg2 value2 params2
      ncmds1 nn1 (Hpop1: ret_pop_cmd (ret (insn_call id1 noret1 clattrs1 typ1 varg1 value1 params1)) ncmds1 nn1 = pop_one_X cmds1 n1)
      ncmds2 nn2 (Hpop2: ret_pop_cmd (ret (insn_call id2 noret2 clattrs2 typ2 varg2 value2 params2)) ncmds2 nn2 = pop_one_X cmds2 n2)
      (Hnoret: noret_dec noret1 noret2)
      (Htyp: typ_dec typ1 typ2)

      (Hftable: ftable_simulation alpha (FunTable cfg1) (FunTable cfg2))

      an1 (Han1: an1 = get_noop_by_bb bid (lookupALOpt _ fn_al1 fid))
      an2 (Han2: an2 = get_noop_by_bb bid (lookupALOpt _ fn_al2 fid))
      block_hint (Hblock_hint: ret block_hint = lookupAL _ (block_hints fh) bid)
      pbid hints (Hhints: ret hints = lookupAL _ (cmds_hint block_hint) pbid)
      hint (Hhint: hint_lookup hint cmds1 cmds2 n1 n2 all_cmds1 all_cmds2 an1 an2 hints)

      (Hdisj1: list_disjoint li1 (concat pi1))
      (Hdisj2: list_disjoint li2 (concat pi2))
      (Hvalid_allocas: valid_allocas mem1 mem2 allocas1 allocas2)

      lmem1 lmem2
      lmem1' (Hlmem1': lmem1' = if is_call_readonly''' m1 (mkState (ec1::pecs1) mem1)
                                then ret lmem1
                                else merror)
      lmem2' (Hlmem2': lmem2' = if is_call_readonly''' m2 (mkState (ec2::pecs2) mem2)
                                then ret lmem2
                                else merror)

      (Hnext:
        forall alpha' (Hincr: inject_incr' alpha alpha' li1 (concat pi1) li2 (concat pi2))
          mem1' mem2'
          (Hvmem: valid_memories alpha' gmax mem1' mem2' li1 (concat pi1) li2 (concat pi2))
          (Hvals: valid_allocas mem1' mem2' allocas1 allocas2)
          (Hmem1: Mem.nextblock mem1 <= Mem.nextblock mem1')
          (Hmem2: Mem.nextblock mem2 <= Mem.nextblock mem2')
          (Hreadonly1: is_call_readonly' m1 (mkState (ec1::pecs1) mem1) -> memory_extends (CurTargetData cfg1) mem1' lmem1)
          (Hreadonly2: is_call_readonly' m2 (mkState (ec2::pecs2) mem2) -> memory_extends (CurTargetData cfg2) mem2' lmem2)

          ec1' ec2'
          (Hnoret: if noret1
           then ec1' = mkEC fdef1 (bid, stmts_intro phis1 all_cmds1 term1) ncmds1 term1 locals1 allocas1 /\
                ec2' = mkEC fdef2 (bid, stmts_intro phis2 all_cmds2 term2) ncmds2 term2 locals2 allocas2
           else
             exists rv1, exists rv2,
               genericvalues_inject.gv_inject alpha' rv1 rv2 /\
               ec1' = mkEC fdef1 (bid, stmts_intro phis1 all_cmds1 term1) ncmds1 term1 (updateAddAL GVs locals1 id1 rv1) allocas1 /\
               ec2' = mkEC fdef2 (bid, stmts_intro phis2 all_cmds2 term2) ncmds2 term2 (updateAddAL GVs locals2 id2 rv2) allocas2)

          (Hwf1': OpsemPP.wf_State cfg1 (mkState (ec1'::pecs1) mem1'))
          (Hwf2': OpsemPP.wf_State cfg2 (mkState (ec2'::pecs2) mem2'))
          hint' (Hhint': hint_lookup hint' ncmds1 ncmds2 nn1 nn2 all_cmds1 all_cmds2 an1 an2 hints),

          hint_sem_insn hint' pecs1 pecs2 pns1 pns2 (concat pi1) (concat pi2) li1 li2
            alpha' gmax
            cfg1 (ec1'::pecs1) mem1' (nn1::pns1)
            cfg2 (ec2'::pecs2) mem2' (nn2::pns2))

      (Hcons:
        hint_sem_global_bot mems1 mems2 mem1 mem2 alpha pi1 pi2
        pecs1 pns1
        pecs2 pns2),

      hint_sem_global_bot (lmem1'::mems1) (lmem2'::mems2) mem1 mem2 alpha (li1::pi1) (li2::pi2)
      (ec1::pecs1) ((noop_idx_decrease n1)::pns1)
      (ec2::pecs2) ((noop_idx_decrease n2)::pns2).

  Lemma hint_sem_global_bot_noret_dec
    mems1 mems2 mem1 mem2 alpha pi1 pi2 ecs1 ns1 ecs2 ns2 (H: hint_sem_global_bot mems1 mems2 mem1 mem2 alpha pi1 pi2 ecs1 ns1 ecs2 ns2) :
    list_forall2
    (fun ec1 ec2 =>
      match CurCmds ec1, CurCmds ec2 with
        | (insn_call _ noret1 _ _ _ _ _)::_, (insn_call _ noret2 _ _ _ _ _)::_ =>
          noret_dec noret1 noret2
        | _, _ =>
          False
      end)
    ecs1 ecs2.
  Proof.
    induction H; econs; [|done].
    subst. simpl.
    clear -Hpop1 Hpop2 Hnoret.
    unfold pop_one_X in *.
    destruct (noop_idx_zero_exists n1); [done|].
    destruct (noop_idx_zero_exists n2); [done|].
    destruct cmds1; [done|]. destruct cmds2; [done|].
    inv Hpop1. inv Hpop2. done.
  Qed.

  Inductive hint_sem_global :
    meminj ->
    list (list mblock) -> list (list mblock) ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
  | hint_sem_global_def :
    forall alpha li1 pi1 li2 pi2 fid bid
      ec1 phis1 all_cmds1 cmds1 term1 locals1 allocas1 pecs1 mem1 n1 pns1
      ec2 phis2 all_cmds2 cmds2 term2 locals2 allocas2 pecs2 mem2 n2 pns2
      fdef1 (Hfdef1: ret fdef1 = lookupFdefViaIDFromProducts (CurProducts cfg1) fid)
      fdef2 (Hfdef2: ret fdef2 = lookupFdefViaIDFromProducts (CurProducts cfg2) fid)
      fh (Hfh: ret fh = lookupAL _ fh_al fid)
      (Hec1: ec1 = mkEC fdef1 (bid, stmts_intro phis1 all_cmds1 term1) cmds1 term1 locals1 allocas1)
      (Hec2: ec2 = mkEC fdef2 (bid, stmts_intro phis2 all_cmds2 term2) cmds2 term2 locals2 allocas2)
      (Hstmts1: ret (stmts_intro phis1 all_cmds1 term1) = lookupBlockViaLabelFromFdef fdef1 bid)
      (Hstmts2: ret (stmts_intro phis2 all_cmds2 term2) = lookupBlockViaLabelFromFdef fdef2 bid)

      (Hwf1: OpsemPP.wf_State cfg1 (mkState (ec1::pecs1) mem1))
      (Hwf2: OpsemPP.wf_State cfg2 (mkState (ec2::pecs2) mem2))

      (Hftable: ftable_simulation alpha (FunTable cfg1) (FunTable cfg2))

      an1 (Han1: an1 = get_noop_by_bb bid (lookupALOpt _ fn_al1 fid))
      an2 (Han2: an2 = get_noop_by_bb bid (lookupALOpt _ fn_al2 fid))
      block_hint (Hblock_hint: ret block_hint = lookupAL _ (block_hints fh) bid)
      pbid hints (Hhints: ret hints = lookupAL _ (cmds_hint block_hint) pbid)
      hint (Hhint: hint_lookup hint cmds1 cmds2 n1 n2 all_cmds1 all_cmds2 an1 an2 hints)

      (Hinsn:
        hint_sem_insn
        hint pecs1 pecs2 pns1 pns2 (concat pi1) (concat pi2) li1 li2
        alpha gmax
        cfg1 (ec1::pecs1) mem1 (n1::pns1)
        cfg2 (ec2::pecs2) mem2 (n2::pns2))

      mems1 mems2
      (Hreadonly1: readonly m1 cfg1 (mkState (ec1::pecs1) mem1) mems1)
      (Hreadonly2: readonly m2 cfg2 (mkState (ec2::pecs2) mem2) mems2)
      (Hcons:
        hint_sem_global_bot mems1 mems2 mem1 mem2 alpha pi1 pi2
        pecs1 pns1
        pecs2 pns2),

      hint_sem_global alpha (li1::pi1) (li2::pi2)
      (ec1::pecs1) mem1 (n1::pns1)
      (ec2::pecs2) mem2 (n2::pns2).

  Variable (Hvalid: valid_products m1 m2 (CurProducts cfg1) (CurProducts cfg2) fn_al1 fn_al2 fh_al).

  Definition F_global_step
    (rel:
      meminj -> list (list mblock) -> list (list mblock) ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      Prop) :
    meminj -> list (list mblock) -> list (list mblock) ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
    fun alpha lpi1 lpi2
      ecs1 mem1 ns1
      ecs2 mem2 ns2 =>

      forall
        ecs1' mem1' ns1' na1' tr1
        (Hstep1: logical_semantic_step cfg1 fn_al1 (mkState ecs1 mem1) (mkState ecs1' mem1') ns1 ns1' na1' tr1),

        exists li1, exists pi1, exists li2, exists pi2,
          (lpi1 = li1::pi1) /\ (lpi2 = li2::pi2) /\
          (* logical step *)
          (forall 
            ecs2' mem2' ns2' na2' tr
            (Hstep: logical_semantic_step cfg2 fn_al2 (mkState ecs2 mem2) (mkState ecs2' mem2') ns2 ns2' na2' tr),
            exists alpha', exists li1', exists li2', exists ecs1', exists mem1', exists ns1', exists na1', 
              logical_semantic_step cfg1 fn_al1 (mkState ecs1 mem1) (mkState ecs1' mem1') ns1 ns1' na1' tr /\
              inject_incr' alpha alpha' li1 (concat pi1) li2 (concat pi2) /\
              rel alpha' li1' li2' ecs1' mem1' ns1' ecs2' mem2' ns2').  

  Definition F_global
    (rel:
      meminj -> list (list mblock) -> list (list mblock) ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      (@ECStack DGVs) -> mem -> noop_stack_t ->
      Prop) :
    meminj -> list (list mblock) -> list (list mblock) ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    (@ECStack DGVs) -> mem -> noop_stack_t ->
    Prop :=
    fun alpha lpi1 lpi2
      ecs1 mem1 ns1
      ecs2 mem2 ns2 =>

      F_progress cfg1 cfg2 fn_al1 fn_al2
      ecs1 mem1 ns1
      ecs2 mem2 ns2 /\

      F_global_step rel
      alpha lpi1 lpi2
      ecs1 mem1 ns1
      ecs2 mem2 ns2.

  Lemma get_noop_by_fname_lookupALOpt fname pnoop :
    get_noop_by_fname fname pnoop = lookupALOpt _ pnoop fname.
  Proof. done. Qed.

  Lemma valid_products_valid_fdef
    fid
    fdef1 (Hfdef1: ret fdef1 = lookupFdefViaIDFromProducts (CurProducts cfg1) fid) :
    exists fdef2, (ret fdef2 = lookupFdefViaIDFromProducts (CurProducts cfg2) fid) /\
      exists fh, (ret fh = lookupAL fdef_hint_t fh_al fid) /\
        valid_fdef m1 m2 fdef1 fdef2 (lookupALOpt one_noop_t fn_al1 fid)
        (lookupALOpt one_noop_t fn_al2 fid) fh.
  Proof.
    generalize dependent fid.
    generalize dependent Hvalid.
    generalize (CurProducts cfg2).
    generalize (CurProducts cfg1).
    induction l0; intros [|hd2 tl2] Hv fid H1; try by inv H1.
    - destruct a; simpl in Hv; try destruct fdec5; try done.
    - destruct a, hd2; simpl in *;
      repeat
        match goal with
          | [H: vgtac.is_true (false) |- _] =>
            inv H
          | [H: vgtac.is_true (_ && _) |- _] =>
            apply andb_true_iff in H
          | [H: (_ && _) = true |- _] =>
            apply andb_true_iff in H
          | [H: _ /\ _ |- _] =>
            destruct H
          | [H: proj_sumbool (id_dec ?a ?b) = true |- _] =>
            destruct (id_dec a b); [|done]
          | [fd: fdec |- _] => destruct fd
        end;
      try by (apply IHl0; eauto).
      rewrite e in *.
      destruct (getFdefID fdef0 == fid); [subst|].
      + eexists; split; [done|].
        remember (lookupAL fdef_hint_t fh_al (getFdefID fdef0)) as fh; destruct fh as [fh|]; [|done].
        exists fh; split; [done|].
        rewrite ? get_noop_by_fname_lookupALOpt in H2.
        by inv H1.
      + by eapply IHl0; eauto.
  Qed.

  Lemma valid_products_valid_fdef_1
    fid
    fdef2 (Hfdef2: ret fdef2 = lookupFdefViaIDFromProducts (CurProducts cfg2) fid) :
    exists fdef1, (ret fdef1 = lookupFdefViaIDFromProducts (CurProducts cfg1) fid) /\
      exists fh, (ret fh = lookupAL fdef_hint_t fh_al fid) /\
        valid_fdef m1 m2 fdef1 fdef2 (lookupALOpt one_noop_t fn_al1 fid)
        (lookupALOpt one_noop_t fn_al2 fid) fh.
  Proof.
    generalize dependent fid.
    generalize dependent Hvalid.
    generalize (CurProducts cfg1).
    generalize (CurProducts cfg2).
    induction l0; intros [|hd1 tl1] Hv fid H2; try by inv H2.
    - destruct a, hd1; simpl in *;
      repeat
        match goal with
          | [H: vgtac.is_true (false) |- _] =>
            inv H
          | [H: vgtac.is_true (_ && _) |- _] =>
            apply andb_true_iff in H
          | [H: (_ && _) = true |- _] =>
            apply andb_true_iff in H
          | [H: _ /\ _ |- _] =>
            destruct H
          | [H: proj_sumbool (id_dec ?a ?b) = true |- _] =>
            destruct (id_dec a b); [|done]
          | [fd: fdec |- _] => destruct fd
        end;
      try by (apply IHl0; eauto).
      rewrite e in *.
      destruct (getFdefID fdef5 == fid); [subst|].
      + eexists; split; [done|].
        remember (lookupAL fdef_hint_t fh_al (getFdefID fdef5)) as fh; destruct fh as [fh|]; [|done].
        exists fh; split; [done|].
        rewrite ? get_noop_by_fname_lookupALOpt in H2.
        by inv H2.
      + by eapply IHl0; eauto.
  Qed.

  Lemma valid_products_valid_fdef'
    fid
    fdef1 (Hfdef1: ret fdef1 = lookupFdefViaIDFromProducts (CurProducts cfg1) fid)
    fdef2 (Hfdef2: ret fdef2 = lookupFdefViaIDFromProducts (CurProducts cfg2) fid)
    fh (Hfh: ret fh = lookupAL fdef_hint_t fh_al fid) :
    valid_fdef m1 m2 fdef1 fdef2 (lookupALOpt one_noop_t fn_al1 fid)
    (lookupALOpt one_noop_t fn_al2 fid) fh.
  Proof.
    exploit valid_products_valid_fdef; eauto.
    intros [fdef2' [Hfdef2' [fh' [Hfh' Hfdef']]]].
    rewrite <- Hfdef2 in Hfdef2'. inv Hfdef2'.
    rewrite <- Hfh in Hfh'. inv Hfh'.
    done.
  Qed.

  Lemma valid_products_fdec fid :
    lookupFdecViaIDFromProducts (CurProducts cfg1) fid = lookupFdecViaIDFromProducts (CurProducts cfg2) fid.
  Proof.
    generalize dependent fid.
    generalize dependent Hvalid.
    generalize (CurProducts cfg2).
    generalize (CurProducts cfg1).
    induction l0; intros [|hd2 tl2] Hv fid; try by inv Hv.
    - destruct a; simpl in Hv; try destruct fdec5; try done.
    - destruct a, hd2; simpl in *;
      repeat
        match goal with
          | [H: vgtac.is_true (false) |- _] =>
            inv H
          | [H: vgtac.is_true (_ && _) |- _] =>
            apply andb_true_iff in H
          | [H: (_ && _) = true |- _] =>
            apply andb_true_iff in H
          | [H: _ /\ _ |- _] =>
            destruct H
          | [H: proj_sumbool (id_dec ?a ?b) = true |- _] =>
            destruct (id_dec a b); [subst|done]
          | [H: proj_sumbool (fheader_dec ?a ?b) = true |- _] =>
            destruct (fheader_dec a b); [subst|done]
          | [H: proj_sumbool (deckind_dec ?a ?b) = true |- _] =>
            destruct (deckind_dec a b); [subst|done]
          | [fd: fdec |- _] => destruct fd
        end;
      try by (apply IHl0; eauto).
      destruct (if getFdecID (fdec_intro fheader5 deckind0) == fid
        then ret fdec_intro fheader5 deckind0
        else merror); [done|].
      by apply IHl0.
  Qed.

  Lemma params_gv_list_inject
    alpha
    params1 lc1 gvs1 (Hgvs1: ret gvs1 = @params2GVs DGVs (CurTargetData cfg1) params1 lc1 (Globals cfg1))
    params2 lc2 gvs2 (Hgvs2: ret gvs2 = @params2GVs DGVs (CurTargetData cfg2) params2 lc2 (Globals cfg2))
    (Hparams: list_forall2
      (fun p1 p2 : typ * attributes * value =>
        exists gvs1 : GVs,
          exists gvs2 : GVs,
            ret gvs1 =
            getOperandValue (CurTargetData cfg1) 
            (snd p1) lc1 (Globals cfg1) /\
            ret gvs2 =
            getOperandValue (CurTargetData cfg2) 
            (snd p2) lc2 (Globals cfg2) /\
            genericvalues_inject.gv_inject alpha gvs1 gvs2) params1 params2) :
    genericvalues_inject.gv_list_inject alpha gvs1 gvs2.
  Proof.
    generalize dependent gvs2.
    generalize dependent gvs1.
    generalize dependent params2.
    induction params1; intros params2 Hparams gvs1 Hgvs1 gvs2 Hgvs2.
    - inv Hparams. simpl in *. inv Hgvs1. inv Hgvs2. done.
    - inv Hparams.
      destruct H1 as [gv1 [gv2 [Hgv1 [Hgv2 Hgv]]]].
      destruct a, b1. simpl in *. rewrite <- Hgv1 in Hgvs1. rewrite <- Hgv2 in Hgvs2.
      remember (params2GVs (CurTargetData cfg1) params1 lc1 (Globals cfg1)) as gvs1'. destruct gvs1' as [gvs1'|]; [|done].
      remember (params2GVs (CurTargetData cfg2) bl lc2 (Globals cfg2)) as gvs2'. destruct gvs2' as [gvs2'|]; [|done].
      inv Hgvs1. inv Hgvs2.
      exploit IHparams1; eauto. intro.
      by constructor.
  Qed.

  Lemma valid_memories_weaken'
    alpha gm mem1 mem2 li1 pi1 li2 pi2 li1' li2'
    (H: valid_memories alpha gm mem1 mem2 li1 pi1 li2 pi2)
    (H1: sublist li1' li1) (H2: sublist li2' li2) :
    valid_memories alpha gm mem1 mem2 li1' pi1 li2' pi2.
  Proof.
    inv H. constructor; try done.
    - intros. apply Hli1none. eapply sublist_In; eauto.
    - intros. apply Hli2none. eapply sublist_In; eauto.
    - intros. apply Hli1free. eapply sublist_In; eauto.
    - intros. apply Hli2free. eapply sublist_In; eauto.
    - intros x y Hx Hy. apply Hlipidisj1; auto. eapply sublist_In; eauto.
    - intros x y Hx Hy. apply Hlipidisj2; auto. eapply sublist_In; eauto.
    - eapply sublist_Forall. apply Hvli1. auto.
    - eapply sublist_Forall. apply Hvli0. auto.
  Qed.

  Lemma valid_memories_weaken
    alpha gm mem1 mem2 li1 pi1 li2 pi2
    (H: valid_memories alpha gm mem1 mem2 li1 pi1 li2 pi2) :
    valid_memories alpha gm mem1 mem2 nil pi1 nil pi2.
  Proof.
    eapply valid_memories_weaken'; eauto.
    econs. econs.
  Qed.

  Lemma valid_memories_concat
    alpha gm mem1 mem2 li1 pi1 li2 pi2
    (H: valid_memories alpha gm mem1 mem2 li1 pi1 li2 pi2) :
    valid_memories alpha gm mem1 mem2 nil (li1 ++ pi1) nil (li2 ++ pi2).
  Proof.
    inv H. constructor;
    (try done);
    (try (intros; apply in_app in H; destruct H)).
    - by apply Hli1none.
    - by apply Hpi1none.
    - by apply Hli2none.
    - by apply Hpi2none.
    - by apply Hli1free.
    - by apply Hpi1free.
    - by apply Hli2free.
    - by apply Hpi2free.
    - by apply Forall_app.
    - by apply Forall_app.
  Qed.

  Lemma valid_memories_concat'
    alpha gm mem1 mem2 li1 pi1 li2 pi2
    (H: valid_memories alpha gm mem1 mem2 nil (li1 ++ pi1) nil (li2 ++ pi2))
    (Hdis1: list_disjoint li1 pi1) (Hdis2: list_disjoint li2 pi2) :
    valid_memories alpha gm mem1 mem2 li1 pi1 li2 pi2.
  Proof.
    inv H. constructor;
    (try done);
    (try (intros; apply in_app in H; destruct H)).
    - intros. apply Hpi1none. apply in_app. by left.
    - intros. apply Hpi2none. apply in_app. by left.
    - intros. apply Hpi1none. apply in_app. by right.
    - intros. apply Hpi2none. apply in_app. by right.
    - intros. apply Hpi1free. apply in_app. by left.
    - intros. apply Hpi2free. apply in_app. by left.
    - intros. apply Hpi1free. apply in_app. by right.
    - intros. apply Hpi2free. apply in_app. by right.
    - apply Forall_split in Hvpi1. by destruct Hvpi1.
    - apply Forall_split in Hvpi1. by destruct Hvpi1.
    - apply Forall_split in Hvpi0. by destruct Hvpi0.
    - apply Forall_split in Hvpi0. by destruct Hvpi0.
  Qed.

Definition discard_block b i :=
  List.filter (fun c => negb (eq_block b c)) i.

Lemma discard_block_in b c l :
  In b (discard_block c l) <-> b <> c /\ In b l.
Proof.
  induction l; simpl.
  - econs; intro. inv H. destruct H. inv H0.
  - destruct (eq_block c a); [subst|]; simpl.
    + eapply iff_trans; [by apply IHl|].
      econs; intros [? ?]; split; auto.
      by destruct H0; subst.
    + econs.
      * intros [?|?]; subst.
        split; [clear IHl; omega|]. by left.
        apply IHl in H. destruct H. split; [done|]. by right.
      * intros [? [?|?]]; subst.
        by left.
        right. apply IHl. by split.
Qed.

Lemma discard_block_sublist c l :
  sublist (discard_block c l) l.
Proof.
  induction l; [by econs|]. simpl.
  destruct (eq_block c a); [subst|]; simpl.
  - by apply sl_cons_r.
  - by apply sl_cons.
Qed.

Lemma discard_block_length c l :
  (@length mblock (discard_block c l) <= @length mblock l /\
   (In c l -> @length mblock (discard_block c l) < @length mblock l))%nat.
Proof.
  induction l; [done|]. simpl in *. destruct IHl.
  destruct (eq_block c a); [subst|]; simpl.
  - split; omega.
  - split; [omega|].
    intros [?|?]; [by subst|].
    exploit H0; eauto. omega.
Qed.

Lemma free_preserves_freeable
  td b1 b2 (Hb: b1 <> b2) mem1 mem2 (H: free td mem1 (blk2GV td b1) = ret mem2) :
  (let (l, h) := Mem.bounds mem1 b2 in Mem.free mem1 b2 l h <> merror) ->
  (let (l, h) := Mem.bounds mem2 b2 in Mem.free mem2 b2 l h <> merror).
Proof.
  exploit memory_props.MemProps.bounds_mfree; eauto. intro Hbd. rewrite Hbd.
  unfold free in H. simpl in H.
  remember (Mem.bounds mem1 b1) as bd1. destruct bd1 as [l1 h1].
  remember (Mem.bounds mem1 b2) as bd2. destruct bd2 as [l2 h2].
  Local Transparent Mem.free.
  intros Hf Hc. unfold Mem.free in Hc.
  destruct (Mem.range_perm_dec mem2 b2 l2 h2 Freeable); [done|].
  assert (~ Mem.range_perm mem1 b2 l2 h2 Freeable).
  - intro Hc'. contradict n.
  unfold Mem.range_perm in *. intros.
  exploit Hc'; eauto. intro Hp.
  eapply Mem.perm_free_1; eauto.
  unfold Mem.free in Hf.
  by destruct (Mem.range_perm_dec mem1 b2 l2 h2 Freeable).
  Global Opaque Mem.free.
Qed.

Lemma free_preserves_valid_memories_1:
  forall alpha gmax td mem1 mem2 mem1' li1 pi1 li2 pi2
    b1 (Hb1: In b1 li1)
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2)
    (Hfree1: free td mem1 (blk2GV td b1) = ret mem1'),
    valid_memories alpha gmax mem1' mem2 (discard_block b1 li1) pi1 li2 pi2.
Proof.
  intros.
  inv Hvmem.

  (* utilities *)
  exploit free_inv; try eapply Hfree1; eauto;
    intros [blk1 [ofs1 [hi1 [lo1 [Hp1 [Hofs1 [Hblk1 Hfree1']]]]]]].
  exploit Mem.nextblock_free; try eapply Hfree1'; eauto; intro Hfeq1.

  inv Hp1.
  exploit genericvalues_inject.mem_inj__pfree; eauto.
  intros [Hwfmi Hinj].

  econs; try done; try (by rewrite Hfeq1); try (by rewrite Hfeq2).
  - intros b Hb. apply discard_block_in in Hb. destruct Hb. by apply Hli1none.
  - intros b Hb. apply discard_block_in in Hb. destruct Hb.
    exploit Hli1free; eauto. intro Hres.
    by eapply free_preserves_freeable; eauto.
  - intros b Hb. exploit Hpi1free; eauto. intro Hres.
    by eapply free_preserves_freeable; eauto.
  - intros x y Hx Hy. apply discard_block_in in Hx. destruct Hx. by apply Hlipidisj1.
  - rewrite Hfeq1. eapply sublist_Forall. apply Hvli1. apply discard_block_sublist.
Qed.

Lemma free_preserves_valid_memories_2:
  forall alpha gmax td mem1 mem2 mem2' li1 pi1 li2 pi2
    b2 (Hb2: In b2 li2)
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 pi1 li2 pi2)
    (Hfree1: free td mem2 (blk2GV td b2) = ret mem2'),
    valid_memories alpha gmax mem1 mem2' li1 pi1 (discard_block b2 li2) pi2.
Proof.
  intros.
  inv Hvmem.

  (* utilities *)
  exploit free_inv; try eapply Hfree1; eauto;
    intros [blk2 [ofs2 [hi2 [lo2 [Hp2 [Hofs2 [Hblk2 Hfree2']]]]]]].
  exploit Mem.nextblock_free; try eapply Hfree2'; eauto; intro Hfeq2.

  inv Hp2.
  exploit mem_inj__ppfree; eauto.
  - inv Hwf. repeat intro. exploit mi_range_block; eauto. intro. subst.
    exploit Hli2none; eauto.
  intros [Hwfmi Hinj].

  econs; try done; try (by rewrite Hfeq1); try (by rewrite Hfeq2).
  - intros b Hb. apply discard_block_in in Hb. destruct Hb. by apply Hli2none.
  - intros b Hb. apply discard_block_in in Hb. destruct Hb.
    exploit Hli2free; eauto. intro Hres.
    by eapply free_preserves_freeable; eauto.
  - intros b Hb. exploit Hpi2free; eauto. intro Hres.
    by eapply free_preserves_freeable; eauto.
  - intros x y Hx Hy. apply discard_block_in in Hx. destruct Hx. by apply Hlipidisj2.
  - rewrite Hfeq2. eapply sublist_Forall. apply Hvli0. apply discard_block_sublist.
Qed.

Lemma allocas_equivalent_not_in_1
  alpha li1 li2 als1 als2
  (H: allocas_equivalent alpha li1 li2 als1 als2) :
  forall b (Hb: ~ In b als1),
  allocas_equivalent alpha (discard_block b li1) li2 als1 als2.
Proof.
  induction H; intros b Hb.
  - econs.
  - apply allocas_equivalent_ignore_left.
    + apply discard_block_in. split; [|done].
      destruct (eq_block b1 b); [|done].
      contradict Hb. by left.
    + apply IHallocas_equivalent.
      intro. apply Hb. by right.
  - apply allocas_equivalent_ignore_right; auto.
  - apply allocas_equivalent_map; auto.
    + intro. apply Hbin1.
      apply discard_block_in in FH. by destruct FH.
    + apply IHallocas_equivalent.
      intro. apply Hb. by right.
Qed.

Lemma allocas_equivalent_not_in_2
  alpha li1 li2 als1 als2
  (H: allocas_equivalent alpha li1 li2 als1 als2) :
  forall b (Hb: ~ In b als2),
  allocas_equivalent alpha li1 (discard_block b li2) als1 als2.
Proof.
  induction H; intros b Hb.
  - econs.
  - apply allocas_equivalent_ignore_left; auto.
  - apply allocas_equivalent_ignore_right.
    + apply discard_block_in. split; [|done].
      destruct (eq_block b2 b); [|done].
      contradict Hb. by left.
    + apply IHallocas_equivalent.
      intro. apply Hb. by right.
  - apply allocas_equivalent_map; auto.
    + intro. apply Hbin1.
      apply discard_block_in in FH. by destruct FH.
    + apply IHallocas_equivalent.
      intro. apply Hb. by right.
Qed.

      Lemma nat_strong_ind' (P: nat -> Prop)
        (H: forall n, (forall m, (m < n)%nat -> P m) -> P n) :
        forall n, (forall m, (m < n)%nat -> P m).
      Proof.
        induction n; intros m Hm; [by inv Hm|].
        destruct (eq_nat_dec m n); [subst|].
        - by apply H.
        - apply IHn. omega.
      Qed.

      Lemma nat_strong_ind (P: nat -> Prop)
        (H: forall n, (forall m, (m < n)%nat -> P m) -> P n) :
        forall n, P n.
      Proof.
        intro. exploit nat_strong_ind'; eauto.
      Qed.

  Lemma free_allocas_valid_memories :
    forall li1 li2 allocas1 allocas2 alpha
    (Hequiv: allocas_equivalent alpha li1 li2 allocas1 allocas2)
    (Halc1: NoDup allocas1) (Halc2: NoDup allocas2)
    li1' li2' pi1 pi2
    mem1 mem1' (Hmem1': free_allocas (CurTargetData cfg1) mem1 allocas1 = ret mem1')
    mem2 mem2' (Hmem2': free_allocas (CurTargetData cfg2) mem2 allocas2 = ret mem2')
    (Hdisj1 : list_disjoint li1' pi1)
    (Hdisj1' : list_disjoint li1 pi1)
    (Hdisj2 : list_disjoint li2' pi2)
    (Hdisj2' : list_disjoint li2 pi2)
    (Hvmem: valid_memories alpha gmax mem1 mem2 li1 (li1' ++ pi1) li2 (li2' ++ pi2)),
    valid_memories alpha gmax mem1' mem2' li1' pi1 li2' pi2.
  Proof.
    intros li1 li2 allocas1 allocas2.
    remember (length li1 + length li2 + length allocas1 + length allocas2)%nat as x.
    generalize dependent allocas2.
    generalize dependent allocas1.
    generalize dependent li2.
    generalize dependent li1.
    generalize dependent x.
    refine (nat_strong_ind _ _). intros.
    inv Hequiv.
    - inv Hmem1'. inv Hmem2'.
      apply valid_memories_concat'; auto.
      by eapply valid_memories_weaken; eauto.
    - inv Halc1. exploit allocas_equivalent_not_in_1; eauto. clear Hequiv0. intro Hequiv.
      simpl in Hmem1', Hmem2'.
      remember (free (CurTargetData cfg1) mem1 (blk2GV (CurTargetData cfg1) b1)) as mem1''. destruct mem1'' as [mem1''|]; [|done].
      eapply H; eauto.
      + destruct (discard_block_length b1 li1) as [_ ?]. exploit H0; eauto. simpl. omega.
      + intros x y Hx Hy. apply Hdisj1'; auto. eapply sublist_In; eauto. apply discard_block_sublist.
      + assert (alpha b1 = merror); [by inv Hvmem; exploit Hli1none; eauto|].
        exploit free_preserves_valid_memories_1; eauto.
    - inv Halc2. exploit allocas_equivalent_not_in_2; eauto. clear Hequiv0. intro Hequiv.
      simpl in Hmem1', Hmem2'.
      remember (free (CurTargetData cfg2) mem2 (blk2GV (CurTargetData cfg2) b2)) as mem2''. destruct mem2'' as [mem2''|]; [|done].
      eapply H; eauto.
      + destruct (discard_block_length b2 li2) as [_ ?]. exploit H0; eauto. simpl. omega.
      + intros x y Hx Hy. apply Hdisj2'; auto. eapply sublist_In; eauto. apply discard_block_sublist.
      + assert (forall sb : Values.block, alpha sb <> ret (b2, 0)); [by inv Hvmem; apply Hli2none|].
        exploit free_preserves_valid_memories_2; eauto.
    - inv Halc1. inv Halc2.
      exploit allocas_equivalent_not_in_1; eauto. clear Hequiv0. intro Hequiv.
      exploit allocas_equivalent_not_in_2; eauto. clear Hequiv. intro Hequiv.
      simpl in Hmem1', Hmem2'.
      remember (free (CurTargetData cfg1) mem1 (blk2GV (CurTargetData cfg1) b1)) as mem1''. destruct mem1'' as [mem1''|]; [|done].
      remember (free (CurTargetData cfg2) mem2 (blk2GV (CurTargetData cfg2) b2)) as mem2''. destruct mem2'' as [mem2''|]; [|done].
      eapply H; eauto.
      + destruct (discard_block_length b1 li1) as [? _].
        destruct (discard_block_length b2 li2) as [? _].
        simpl. omega.
      + intros x y Hx Hy. apply Hdisj1'; auto. eapply sublist_In; eauto. apply discard_block_sublist.
      + intros x y Hx Hy. apply Hdisj2'; auto. eapply sublist_In; eauto. apply discard_block_sublist.
      + eapply free_preserves_valid_memories; [eauto|idtac|eauto|eauto].
        * by eapply valid_memories_weaken'; eauto;
             apply discard_block_sublist.
        rewrite Htd. eapply genericvalues_inject.gv_inject_cons; [|done].
        by econs; eauto.
  Qed.
  
  Lemma inject_incr'_concat
    alpha alpha' li1 pi1 li2 pi2
    (H: inject_incr' alpha alpha' nil (li1++pi1) nil (li2++pi2)) :
    inject_incr' alpha alpha' li1 pi1 li2 pi2.
  Proof.
    unfold inject_incr' in *. destruct_and.
    splits; auto.
    - intros. apply H1; auto. apply in_app. by left.
    - intros. apply H1; auto. apply in_app. by right.
    - intros. apply H3; auto. apply in_app. by left.
    - intros. apply H3; auto. apply in_app. by right.
  Qed.

  Lemma inject_incr'_weaken
    alpha alpha' li1 pi1 li2 pi2
    (H: inject_incr' alpha alpha' li1 pi1 li2 pi2) :
    inject_incr' alpha alpha' nil pi1 nil pi2.
  Proof.
    unfold inject_incr' in *. destruct_and.
    splits; auto.
    intros. inv H4.
  Qed.

  Lemma inject_incr'_trans
    alpha1 alpha2 alpha3 li1 pi1 li2 pi2
    (H12: inject_incr' alpha1 alpha2 li1 pi1 li2 pi2)
    (H23: inject_incr' alpha2 alpha3 li1 pi1 li2 pi2) :
    inject_incr' alpha1 alpha3 li1 pi1 li2 pi2.
  Proof.
    unfold inject_incr' in *. destruct_and.
    splits; auto.
    eapply inject_incr_trans; eauto.
  Qed.

  Lemma logical_semantic_step_mem_nextblock
    cfg fn_al ecs1 ecs2 mem1 mem2 ns1 ns2 na tr
    (H: logical_semantic_step cfg fn_al (mkState ecs1 mem1) (mkState ecs2 mem2) ns1 ns2 na tr) :
    Mem.nextblock mem1 <= Mem.nextblock mem2.
  Proof.
    inv H. simpl in *. subst. destruct ec. simpl in *.
    inv Hpop; unfold pop_one_X in *.
    - remember (noop_idx_zero_exists hpn) as zn. destruct zn.
      + inv Hpop0. destruct Hstep. inv H. omega.
      + destruct CurCmds0; [done|]. inv Hpop0.
        inv Hstep; try by omega.
        * exploit memory_props.MemProps.nextblock_malloc; eauto. omega.
        * exploit memory_props.MemProps.nextblock_free; eauto. intro. rewrite H. omega.
        * exploit memory_props.MemProps.nextblock_malloc; eauto. omega.
        * exploit memory_props.MemProps.nextblock_mstore; eauto. intro. rewrite H. omega.
        * by eapply callExternalOrIntrinsics_prop_1; eauto.
    - remember (noop_idx_zero_exists hpn) as zn. destruct zn; [done|].
      destruct CurCmds0; [|done].
      inv Hstep; try by omega.
      + exploit memory_props.MemProps.nextblock_free_allocas; eauto. intro. rewrite H. omega.
      + exploit memory_props.MemProps.nextblock_free_allocas; eauto. intro. rewrite H. omega.
  Qed.

  Lemma noop_idx_zero_remove_decrease x (H: noop_idx_zero_exists x) :
    (length (noop_idx_zero_remove x) < length x)%nat.
  Proof.
    generalize dependent H. induction x; [done|].
    simpl. destruct (idx_noop a).
    - intros _. omega.
    - simpl in *. intro. exploit IHx; [done|]. omega.
  Qed.

  Lemma pop_one_X_ineq
    {A} a b c d e (H: ret_pop_cmd a b c = pop_one_X (d:list A) e) :
    (length b + length c < length d + length e)%nat.
  Proof.
    unfold pop_one_X in H.
    remember (noop_idx_zero_exists e) as z. destruct z.
    - inv H.
      exploit noop_idx_zero_remove_decrease; eauto.
      by instantiate (1 := e).
      omega.
    - destruct d; [done|]. inv H.
      unfold noop_idx_decrease. rewrite list_length_map.
      simpl. omega.    
  Qed.

  Lemma hint_lookup_ineq
    hint cmds1 cmds2 ns1 ns2 all_cmds1 all_cmds2 an1 an2 hints
    (H: hint_lookup hint cmds1 cmds2 ns1 ns2 all_cmds1 all_cmds2 an1 an2 hints) :
    (length cmds1 + length ns1 <= length all_cmds1 + length an1 /\
    length cmds2 + length ns2 <= length all_cmds2 + length an2)%nat.
  Proof.
    induction H; [done|].
    destruct IHhint_lookup.
    exploit (pop_one_X_ineq cmd_opt1); eauto. intro.
    exploit (pop_one_X_ineq cmd_opt2); eauto. intro.
    omega.
  Qed.

  Lemma hint_lookup_uniq
    hint1 hint2 cmds1 cmds2 ns1 ns2 all_cmds1 all_cmds2 an1 an2 hints
    (H1: hint_lookup hint1 cmds1 cmds2 ns1 ns2 all_cmds1 all_cmds2 an1 an2 hints)
    (H2: hint_lookup hint2 cmds1 cmds2 ns1 ns2 all_cmds1 all_cmds2 an1 an2 hints) :
    hint1 = hint2.
  Proof.
    generalize dependent an2.
    generalize dependent an1.
    generalize dependent all_cmds2.
    generalize dependent all_cmds1.
    generalize dependent hint2.
    generalize dependent hint1.
    induction hints; intros hint1 hint2 all_cmds1 all_cmds2 an1 an2 H1 H2; [by inv H1|].
    inv H1.
    - inv H2; [done|]. exfalso.
      exploit hint_lookup_ineq; eauto. intros [H _].
      exploit (pop_one_X_ineq cmd_opt1); eauto. intro.
      omega.
    - inv H2.
      + exploit hint_lookup_ineq; eauto. intros [H _].
        exploit (pop_one_X_ineq cmd_opt1); eauto. intro.
        exfalso. omega.
      + rewrite <- Hpop1 in Hpop0. inv Hpop0.
        rewrite <- Hpop2 in Hpop3. inv Hpop3.
        eapply IHhints; eauto.
  Qed.

  Lemma inject_incr'_hint_sem_global_bot
    mems1 mems2 mem1 mem2 alpha pi1 pi2 pecs1 pns1 pecs2 pns2
    (H: hint_sem_global_bot mems1 mems2 mem1 mem2 alpha pi1 pi2 pecs1 pns1 pecs2 pns2)
    mem1' (Hmem1: Mem.nextblock mem1 <= Mem.nextblock mem1')
    mem2' (Hmem2: Mem.nextblock mem2 <= Mem.nextblock mem2')
    alpha' (Hincr: inject_incr' alpha alpha' nil (concat pi1) nil (concat pi2)) :
    hint_sem_global_bot mems1 mems2 mem1' mem2' alpha' pi1 pi2 pecs1 pns1 pecs2 pns2.
  Proof.
    induction H; [by econs|].
    econs; eauto.
    - eapply inject_incr__preserves__ftable_simulation; eauto.
      by destruct Hincr.
    - unfold valid_allocas in *. destruct_and. splits; auto.
      + generalize H0. clear -Hmem1.
        induction allocas1; [done|]; intros H. inv H.
        econs; [|by auto]. omega.
      + generalize H1. clear -Hmem2.
        induction allocas2; [done|]; intros H. inv H.
        econs; [|by auto]. omega.
    - intros. apply Hnext; auto.
      + eapply inject_incr'_trans; eauto.
        by eapply inject_incr'_concat; eauto.
      + omega.
      + omega.
      + intro. apply Hreadonly1.
        apply is_call_readonly_iff in H0.
        apply is_call_readonly_iff.
        done.
      + intro. apply Hreadonly2.
        apply is_call_readonly_iff in H0.
        apply is_call_readonly_iff.
        done.
    - apply IHhint_sem_global_bot.
      + omega.
      + omega.
      + eapply inject_incr'_weaken; eauto.
        by eapply inject_incr'_concat; eauto.
  Qed.    

  Lemma is_ordinary_logical_semantic_step cfg pnoops
    ec ecs mem n ns (Hord: is_ordinary cfg (mkState (ec::ecs) mem) (n::ns))
    ec' ecs' mem' n' ns' na tr
    (Hstep: logical_semantic_step cfg pnoops (mkState (ec::ecs) mem) (mkState (ec'::ecs') mem') (n::ns) (n'::ns') na tr) :
    ecs = ecs' /\ ns = ns'.
  Proof.
    inv Hstep. inv Hec. inv Hpn.
    remember (noop_idx_zero_exists hpn) as zhpn. destruct zhpn.
    - inv Hpop; unfold pop_one_X in Hpop0; rewrite <- Heqzhpn in Hpop0; inv Hpop0.
      inv Hstep0. inv H. inv Hnoop; [|done]. inv Hnnn; try done. inv H0.
      done.
    - inv Hord.
      + inv Hns. exploit stutter_num_noop_idx_zero_exists; eauto.
        intro Hnhd. rewrite Hnhd in Heqzhpn. done.
        inv Hpop; unfold pop_one_X in Hpop0; rewrite <- Heqzhpn in Hpop0; inv Hpop0.
      + destruct ec0. simpl in *. destruct CurCmds0; [done|]. inv H0.
        inv Hnoop; [|done]. inv Hnnn; simpl in *; try done.
        * inv H0. destruct c; try by inv Hstep0.
        * inv H0. destruct c; try done.
          by exploit Hncall; eauto.
        * inv H0. destruct c; try done.
          destruct Hexcall as [fptrs [fptr [fd [? [? ?]]]]].
          by exploit Hnexcall; eauto.
      + destruct ec0. simpl in *. destruct CurCmds0; [|done].
        inv Hnoop; [by inv Hnnn|]. inv Hnnn; try done. inv H1.
        destruct Terminator0; try by contradict Hnret.
        * by inv Hstep0.
        * by inv Hstep0.
  Qed.            

  Lemma valid_phis_nil id hint1 hint2
    (H2: valid_phis m1 m2 nil nil id hint1 hint2) :
    invariant_implies (infrules_resolve m1 m2 hint1) hint2.
  Proof.
    unfold valid_initial_phi_hint in *. destruct_and.
    unfold valid_initial_newdefs_eqs in *. destruct_and.
    unfold valid_phis in *.
    unfold invariant_proceed_phis in *. simpl in *.
    repeat match goal with
             | [H: context[if ?c then _ else _] |- _] =>
               let b := fresh "b" in
                 remember c as b; destruct b; try done
           end.
    destruct hint1. destruct hint_invariant. simpl in *.
    destruct invariant_original, invariant_optimized. simpl in *.
    auto.
  Qed.

  Lemma free_allocas_valid_allocas
    mem1 mem2 allocas1 allocas2
    (Halc: valid_allocas mem1 mem2 allocas1 allocas2)
    mem1' allocas1' (Hmem1': free_allocas (CurTargetData cfg1) mem1 allocas1' = ret mem1')
    mem2' allocas2' (Hmem2': free_allocas (CurTargetData cfg2) mem2 allocas2' = ret mem2') :
    valid_allocas mem1' mem2' allocas1 allocas2.
  Proof.
    exploit memory_props.MemProps.nextblock_free_allocas; [by apply Hmem1'|]. intro Hnb1.
    exploit memory_props.MemProps.nextblock_free_allocas; [by apply Hmem2'|]. intro Hnb2.
    unfold valid_allocas in *. destruct_and. splits; auto.
    - by rewrite <- Hnb1.
    - by rewrite <- Hnb2.
  Qed.

  Lemma gv2gvs_prop v t : (@gv2gvs DGVs) v t = v.
  Proof. done. Qed.

  Lemma _initializeFrameValues_nil_nil td la lc
    (H: ret lc = _initializeFrameValues td la nil nil)
    k v (Hkv: ret v = lookupAL GVs lc k) :
    exists t, ret v = gundef td t.
  Proof.
    generalize dependent v.
    generalize dependent k.
    generalize dependent lc.
    induction la; intros lc Hlc k v Hv.
    - inv Hlc. inv Hv.
    - destruct a. destruct p. simpl in Hlc.
      remember (@_initializeFrameValues DGVs td la nil nil) as lc'. destruct lc'; [|done].
      remember (gundef td t) as udf. destruct udf as [udf|]; [|done].
      inv Hlc.
      destruct (id_dec k i0); [subst|].
      + rewrite lookupAL_updateAddAL_eq in Hv. inv Hv.
        rewrite gv2gvs_prop. by exists t.
      + rewrite <- lookupAL_updateAddAL_neq in Hv; auto.
        eapply IHla; eauto.
  Qed.    

  Lemma initLocals_hint_sem
    td mb alpha mem1 mem2 (Hwf: genericvalues_inject.wf_sb_mi mb alpha mem1 mem2)
    la (gvs1 gvs2: list GVs) (Hgvs: genericvalues_inject.gv_list_inject alpha gvs1 gvs2)
    lc1 (H1: initLocals td la gvs1 = ret lc1)
    lc2 (H2: initLocals td la gvs2 = ret lc2) :
    maydiff_sem lc1 lc2 alpha nil nil IdExtSetImpl.empty.
  Proof.
    intros x Hx. destruct x. destruct n; [done|].
    unfold variable_equivalent. simpl.
    unfold initLocals in *.
    generalize dependent lc2.
    generalize dependent lc1.
    generalize dependent gvs2.
    generalize dependent gvs1.
    induction la; intros gvs1 gvs2 Hinj lc1 Hlc1 lc2 Hlc2.
    - inv Hlc1. inv Hlc2. done.
    - destruct a. destruct p. simpl in *.
      inv Hinj.
      + remember (@_initializeFrameValues DGVs td la nil nil) as lc. destruct lc as [lc|]; [|done].
        remember (gundef td t) as udf. destruct udf as [udf|]; [|done].
        inv Hlc1. inv Hlc2.
        destruct (id_dec i0 i1); [subst|].
        * rewrite lookupAL_updateAddAL_eq.
          rewrite gv2gvs_prop.
          eapply genericvalues_inject.gv_inject_gundef; eauto.
        * rewrite <- lookupAL_updateAddAL_neq; [|done].
          remember (lookupAL GVs lc i0) as gv. destruct gv as [gv|]; [|done].
          exploit _initializeFrameValues_nil_nil; eauto.
          intros [t' Ht'].
          eapply genericvalues_inject.gv_inject_gundef; eauto.
      + remember (@_initializeFrameValues DGVs td la l0 nil) as lc1'. destruct lc1'; [|done].
        remember (@_initializeFrameValues DGVs td la l' nil) as lc1'. destruct lc1'; [|done].
        rewrite lift_op1_prop in *.
        remember (fit_gv td t x) as gv1. destruct gv1 as [gv1|]; [|done].
        remember (fit_gv td t y) as gv2. destruct gv2 as [gv2|]; [|done].
        inv Hlc1. inv Hlc2.
        destruct (id_dec i0 i1); [subst|].
        * rewrite lookupAL_updateAddAL_eq.
          rewrite lookupAL_updateAddAL_eq.
          exploit genericvalues_inject.simulation__fit_gv; eauto.
          intros [gv2' [Hgv2' Hinj]]. rewrite <- Heqgv2 in Hgv2'.
          by inv Hgv2'.
        * rewrite <- lookupAL_updateAddAL_neq; [|done].
          rewrite <- lookupAL_updateAddAL_neq; [|done].
          exploit IHla; eauto.
  Qed.

  Lemma callExternalOrIntrinsics_mem td gl mem1 fid rt targs dck gvs ores tr mem2
    (H: callExternalOrIntrinsics td gl mem1 fid rt targs dck gvs = ret (ores, tr, mem2)) :
    mem1 = mem2.
  Proof.
    Ltac destruct_add_empty_trace :=
      repeat match goal with
               | [H: add_empty_trace ?R = ret _ |- _] =>
                 unfold add_empty_trace in H;
                   remember R as Q; destruct Q as [[]|]; [|done]
               | [H: ret _ = ret _ |- _] => inv H
             end.
    destruct dck; simpl in H; destruct_add_empty_trace.
    - exploit callIntrinsics__extcall_properties; eauto.
    intro H. by inv H.
    destruct external_id5; destruct_add_empty_trace.
    - exploit callMalloc__extcall_properties; eauto.
    instantiate (1 := globals2Genv td gl).
    intro H. by inv H.
    - exploit callFree__extcall_properties; eauto.
    instantiate (1 := globals2Genv td gl).
    intro H. by inv H.
    - exploit callIOFunction__extcall_io_sem; eauto.
    intro H'. by inv H'.
    - exploit callExternalFunction__extcall_other_sem; eauto.
    intro H. by inv H.
  Qed.

  Lemma global_hint_sem_F_step_hint_sem
    alpha lpi1 lpi2
    ecs1 mem1 ns1
    ecs2 mem2 ns2
    (Hsem: hint_sem_global alpha lpi1 lpi2 ecs1 mem1 ns1 ecs2 mem2 ns2) :
    F_global_step hint_sem_global alpha lpi1 lpi2 ecs1 mem1 ns1 ecs2 mem2 ns2.
  Proof.
    inv Hsem. repeat intro.
    exploit valid_products_valid_fdef'; eauto. intro Hvalid_fdef.
    exploit hint_sem_F_step_hint_sem; eauto.
    - constructor; simpl.
      + exploit lookupFdefViaIDFromProducts_ideq.
        * symmetry. apply Hfdef1.
        * done.
      + exploit lookupFdefViaIDFromProducts_ideq.
        * symmetry. apply Hfdef2.
        * done.
    - econstructor; eauto.
      constructor; simpl.
      + exploit lookupFdefViaIDFromProducts_ideq.
        * symmetry. apply Hfdef1.
        * intro. subst. destruct fdef1. destruct fheader5. auto.
      + exploit lookupFdefViaIDFromProducts_ideq.
        * symmetry. apply Hfdef2.
        * intro. subst. destruct fdef2. destruct fheader5. auto.
      + eapply hint_sem_global_bot_noret_dec; eauto.

    (** main **)
    intro Hlocal. exploit Hlocal; eauto.
    clear Hlocal. intro Hlocal.
    eexists. eexists. eexists. eexists.
    split; [by eauto|].
    split; [by eauto|].
    intros.
    destruct Hlocal as [Hlocal|[Hlocal|Hlocal]].

    (* ordinary: cmd + call + return *)
    - destruct Hlocal as [Hord1 [Hord2 Hlocal]]. exploit Hlocal; eauto.
      clear Hlocal. intros [pbid' [alpha' [li1' [li2' [ecs1'0 [mem1'0 [ns1'0 [na1'0 [Hlocal0 [Hlocal1 Hlocal2]]]]]]]]]].
      exists alpha'. exists (li1'::pi1). exists (li2'::pi2). exists ecs1'0. exists mem1'0. exists ns1'0. exists na1'0.
      repeat (split; [done|]).
      inv Hlocal2. 
      exploit (is_ordinary_logical_semantic_step cfg1); eauto. intros [? ?]; subst.
      exploit (is_ordinary_logical_semantic_step cfg2); eauto. intros [? ?]; subst.
      econs; eauto.
      + eapply readonly_ordinary''; eauto.
      + eapply readonly_ordinary''; eauto.

      eapply inject_incr'_hint_sem_global_bot; eauto.
      + by eapply logical_semantic_step_mem_nextblock; eauto.
      + by eapply logical_semantic_step_mem_nextblock; eauto.
      + by eapply inject_incr'_weaken; eauto.

    (* call *)
    inv Hlocal.
    unfold pop_one_X in *.
    remember (noop_idx_zero_exists n1) as zn1; destruct zn1; [done|].
    remember (noop_idx_zero_exists n2) as zn2; destruct zn2; [done|].
    destruct cmds1 as [|[]]; try done.
    destruct cmds2 as [|[]]; try done.
    inv Hpop1. inv Hpop2.
    inv Hsame_call.
    - simpl in *.
      generalize H1. intro H1'. destruct H1' as [fptrs [fptr [fdef1' [Hfptrs [Hfptr [Hfdef1' Hfid]]]]]].
      unfold lookupFdefViaPtr in Hfdef1'.
      remember (lookupFdefViaGVFromFunTable (FunTable cfg1) fptr) as fn. destruct fn; [simpl in *|done].
      exploit lookupFdefViaIDFromProducts_ideq; eauto.
      intro. subst.
      exploit (valid_products_valid_fdef (getFdefID fdef1')); eauto.
      intros [fdef2' [Hfdef2' [fh' [Hfh' Hvalid_fdef']]]].
      destruct fdef1', fdef2'. simpl in Hvalid_fdef'.
      apply andb_true_iff in Hvalid_fdef'. destruct Hvalid_fdef' as [Hfdef' Hblocks'].
      apply andb_true_iff in Hfdef'. destruct Hfdef' as [Hdec' Hinit'].
      destruct blocks5 as [|[]];
        destruct blocks0 as [|[]];
        try by inv Hinit'.
      infrule_tac.
      exists alpha. exists (nil::li1::pi1). exists (nil::li2::pi2).
      destruct s.
      generalize Hstep1. intro Hstep1'. rewrite (destruct_cfg cfg1) in Hstep1'. inv Hstep1'. inv Hpn. inv Hec. simpl in *.
      generalize Hstep. intro Hstep'. rewrite (destruct_cfg cfg2) in Hstep'. inv Hstep'. inv Hpn. inv Hec. simpl in *.
      inv Hpop; unfold pop_one_X in *; try rewrite <- Heqzn1 in *; inv Hpop1.
      inv Hpop0; unfold pop_one_X in *; try rewrite <- Heqzn2 in *; inv Hpop.
      inv Hnoop; [|by inv Hnnn].
      inv Hnoop0; [|by inv Hnnn].
      inv Hnnn; simpl in *; try done; [|by exploit (call_excall cfg1); eauto].
      inv Hnnn0; simpl in *; try done; [|by exploit (call_excall cfg2); eauto].
      exploit (call_uniq cfg1 value0 locals1 (getFheaderID fheader5) fid0); eauto.
      intro; subst.
      rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0; [|by exploit (call_excall' cfg1); eauto].
      rewrite (destruct_cfg cfg2) in Hstep2. inv Hstep2; [|by exploit (call_excall' cfg2); eauto].
      eexists. eexists. eexists. eexists. (repeat split); (try by eauto).

      exploit valid_products_valid_fdef; eauto.
      intros [fdef2' [Hfdef2'' [fh'' [Hfh'' Hvalid_fdef']]]].
      rewrite <- Hfdef2' in Hfdef2''. inv Hfdef2''.
      rewrite <- Hfh' in Hfh''. inv Hfh''.
      destruct fdef0. simpl in Hvalid_fdef'. infrule_tac.
      destruct (fheader_dec fheader1 fheader0); [subst|done].
      destruct (fheader_dec fheader5 fheader0); [subst|done].
      rewrite Hfptrs in H24. inv H24.
      inv Hfptr. inv H25.
      unfold lookupFdefViaPtr in H26. rewrite <- Heqfn in H26. simpl in H26.
      rewrite Hfdef1' in H26. inv H26.
      destruct blocks1; [done|]. simpl in H3. destruct b. infrule_tac.
      unfold getEntryBlock in H33, H27, Hbid.
      destruct lb0; [done|inv H33]. inv H27. inv Hbid. simpl in *.
      exploit (call_uniq' cfg2 value3 locals2); eauto. simpl. intro. subst.
      exploit (call_uniq cfg2 value3 locals2 fid0 fid1); eauto. intro. subst.
      rewrite <- Hfdef2' in Hfdef0. inv Hfdef0.
      infrule_tac.
      rewrite <- Hfdef in Hfdef1'. inv Hfdef1'.
      exploit lookupFdefViaPtr_inversion; eauto.
      intros [fn [Hfn Hfn']].
      exploit infrastructure_props.lookupFdefViaIDFromProducts_ideq; eauto. intro. subst.
      unfold lookupFdefViaPtr in H32. rewrite Hfn in H32. simpl in H32.
      rewrite Hfn' in H32. inv H32.
      rewrite <- Hfdef2' in Hfn'. inv Hfn'.
      remember (lookupAL block_hint_t (block_hints fh') l') as bh'. destruct bh' as [bh'|]; [|done].
      destruct bh'. simpl in *. destruct_and. destruct ps'; [|done]. destruct ps'0; [|done].
      destruct phi_hint as [|[phihd_id phihd_hint] [|]]; try done. simpl in *. infrule_tac.
      destruct cmds_hint as [|[cmdhd_id [|cmdhd_hint cmdhd_hints]] cmdtl]; try done. infrule_tac.
      destruct cmdtl; try done.
      inv Hbid0.
      econstructor; eauto.
      + simpl. by destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l'0 l'0).
      + simpl. by destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) l'0 l'0).
      + by eapply logical_step_preservation; eauto.
      + by eapply logical_step_preservation; eauto.
      + instantiate (1 := cmdhd_id).
        instantiate (1 := cmdhd_hint::cmdhd_hints).
        simpl. by destruct (@eq_dec atom (EqDec_eq_of_EqDec atom EqDec_atom) cmdhd_id cmdhd_id).
      + by apply hint_lookup_nil.
      + simpl in *.
        exploit valid_phis_nil; eauto. intro Himpl.
        exploit invariant_implies_preserves_hint_sem_fdef; [idtac|eauto|eauto].
        eapply infrules_resolve_preserves_hint_sem_fdef; eauto.
        * apply infrules_correct.
        econs; simpl; eauto.
        * inv Hinsn. destruct Hsem as [olc1 [olc2 [Hmd Hinv]]].
          destruct Hparams as [gvs1 [Hgvs1 [gvs2 [Hgvs2 Hinj]]]].
          rewrite <- Hgvs1 in H28. inv H28.
          rewrite <- Hgvs2 in H34. inv H34.
          exists nil. exists nil. split.
            intros x Hx.
            exploit initLocals_hint_sem.
              by inv Hvmem; eauto.
              by eauto. by eauto. by rewrite Htd; eauto.
              by apply set_facts2.IdExtSetFacts2.F.empty_b.
              by eauto.

            clear -H8.
            unfold valid_initial_phi_hint in H8. destruct_and.
            unfold valid_initial_newdefs_eqs in *. destruct_and.
            apply EqRegSetFacts.is_empty_iff in H.
            apply EqRegSetFacts.is_empty_iff in H2.
            apply EqHeapSetFacts.is_empty_iff in H6.
            apply EqHeapSetFacts.is_empty_iff in H4.
            apply NeqRegSetFacts.is_empty_iff in H5.
            apply NeqRegSetFacts.is_empty_iff in H3.
            apply IdExtSetFacts.is_empty_iff in H1.
            apply IdExtSetFacts.is_empty_iff in H0.

            unfold invariant_sem, eqs_sem; splits; repeat intro.
            apply EqRegSetFacts.mem_iff in H7. by exploit H; eauto.
            apply EqHeapSetFacts.mem_iff in H7. by exploit H6; eauto.
            apply NeqRegSetFacts.mem_iff in H7. by exploit H5; eauto.
            apply EqRegSetFacts.mem_iff in H7. by exploit H2; eauto.
            apply EqHeapSetFacts.mem_iff in H7. by exploit H4; eauto.
            apply NeqRegSetFacts.mem_iff in H7. by exploit H3; eauto.
            by exploit H1; eauto.
            by exploit H0; eauto.
        * by econs.
        * by inv Hinsn.
        * by inv Hinsn.
        * inv Hinsn.
          by apply valid_memories_concat.
      + exploit readonly_call'; [idtac|idtac|idtac|apply Hstep1|idtac]; eauto.
      + exploit readonly_call'; [idtac|idtac|idtac|apply Hstep|idtac]; eauto.
      + econs; [idtac|idtac|idtac|f_equal|f_equal|idtac|idtac|idtac|idtac|idtac
               |idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac
               |reflexivity|reflexivity|idtac|idtac]; eauto.
        * unfold pop_one_X. rewrite <- Heqzn1. eauto.
        * unfold pop_one_X. rewrite <- Heqzn2. eauto.
        * by destruct (noret_dec noret0 noret0).
        * by destruct (typ_dec typ0 typ0).
        * inv Hinsn. inv Hvmem. done.
        * inv Hinsn. inv Hvmem. done.
        * by inv Hinsn.
        * intros. exploit Hnext; eauto.
          intro Hsim. inv Hsim.
          destruct noret0.
            destruct Hnoret as [Hec1 Hec2]. inv Hec1. inv Hec2.
            rewrite <- Hblock_hint in Hblock_hint0. inv Hblock_hint0.
            rewrite <- Hhints in Hhints0. inv Hhints0.
            exploit hint_lookup_uniq; [apply Hhint'|apply Hhint0|].
            intro. by subst.
            
            destruct Hnoret as [rv1 [rv2 [Hrv [Hec1 Hec2]]]]. inv Hec1. inv Hec2.
            rewrite <- Hblock_hint in Hblock_hint0. inv Hblock_hint0.
            rewrite <- Hhints in Hhints0. inv Hhints0.
            exploit hint_lookup_uniq; [apply Hhint'|apply Hhint0|].
            intro. by subst.

    (* excall *)
    - simpl in *.
      generalize H1. intro H1'. destruct H1' as [fptrs1 [fptr1 [Hfptrs1 [Hfptr1 Hfdec1]]]].
      generalize H2. intro H2'. destruct H2' as [fptrs2 [fptr2 [Hfptrs2 [Hfptr2 Hfdec2]]]].
      exploit lookupFdefViaIDFromProducts_ideq; eauto.
      intro. subst.
      infrule_tac.
      exists alpha. exists (li1::pi1). exists (li2::pi2).
      generalize Hstep1. intro Hstep1'. rewrite (destruct_cfg cfg1) in Hstep1'. inv Hstep1'. inv Hpn. inv Hec. simpl in *.
      generalize Hstep. intro Hstep'. rewrite (destruct_cfg cfg2) in Hstep'. inv Hstep'. inv Hpn. inv Hec. simpl in *.
      inv Hpop; unfold pop_one_X in *; try rewrite <- Heqzn1 in *; inv Hpop1.
      inv Hpop0; unfold pop_one_X in *; try rewrite <- Heqzn2 in *; inv Hpop.
      inv Hnoop; [|by inv Hnnn].
      inv Hnoop0; [|by inv Hnnn0].
      inv Hnnn; simpl in *; try done; [by exploit (call_excall' cfg1); eauto|].
      inv Hnnn0; simpl in *; try done; [by exploit (call_excall' cfg2); eauto|].
      rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0; [by exploit (call'_excall cfg1); eauto|].
      rewrite (destruct_cfg cfg2) in Hstep2. inv Hstep2; [by exploit (call'_excall cfg2); eauto|].
      exploit (excall_uniq' cfg1 value0 locals1 fdec0 (fdec_intro (fheader_intro fa rt fid la va) dck)).
      + apply Hfptrs1. eauto. eauto. apply H24. eauto. eauto.
      exploit (excall_uniq' cfg2 value3 locals2 fdec0 (fdec_intro (fheader_intro fa0 rt0 fid0 la0 va0) dck0)).
      + apply Hfptrs2. eauto. eauto. apply H31. eauto. eauto.
      intros [? [? ?]] [? [? ?]]. subst. inv H6.
      exploit dos_in_list_gvs_inv; eauto. intro. subst. clear H35.
      exploit dos_in_list_gvs_inv; eauto. intro. subst. clear H28.
      destruct Hparams as [gvs1 [Hgvs1 [gvs2 [Hgvs2 Hpinj]]]].
      rewrite <- Hgvs1 in H27. inv H27.
      rewrite <- Hgvs2 in H34. inv H34.
      generalize Hinsn. intro Hinsn'. inv Hinsn'.
      exploit callExternalOrIntrinsics_prop_2; eauto.
      + by inv Hvmem; eauto.
      intros [oresult2 [mem2'' [Horesult2 [Hvmem' [Halc' Horesult1]]]]]. simpl in Halc'.
      rewrite Htd, H36 in Horesult2. inv Horesult2.
      generalize (callExternalOrIntrinsics_prop_1 _ _ _ _ _ _ _ _ _ _ _ H29). intro Hmem1'.
      generalize (callExternalOrIntrinsics_prop_1 _ _ _ _ _ _ _ _ _ _ _ H36). intro Hmem2'.
      eexists. eexists. eexists. eexists. (repeat split); (try by eauto).
      exploit Hvalid_cmd; eauto.
      * unfold pop_one_X. rewrite <- Heqzn2. eauto.
      intros [? [? [? [hint' [hint'' [Hpop [Hhint' [Hhint'' Himpl]]]]]]]].
      unfold pop_one_X in Hpop. rewrite <- Heqzn1 in Hpop. inv Hpop.
      econs; eauto.
      + by eapply logical_step_preservation; eauto.
      + by eapply logical_step_preservation; eauto.
      + destruct noret0.
        * unfold exCallUpdateLocals in *.
          inv H30. inv H37.
          exploit Hnext; [idtac|idtac|idtac|idtac|idtac
                         |idtac|idtac|idtac
                         |by eapply logical_step_preservation; eauto
                         |by eapply logical_step_preservation; eauto
                         |idtac]; eauto.
            by apply inject_incr'_refl.
            (* *) intro Hrd1. apply is_call_readonly_iff in Hrd1.
                  exploit readonly_ordinary'; [idtac|idtac|idtac|idtac|apply Hstep1|idtac]; eauto.
                  intros. by exploit call_excall; eauto.
                  by intros [? _].
                  simpl. rewrite Hrd1. by intros [? _].
            (* *) intro Hrd2. apply is_call_readonly_iff in Hrd2.
                  exploit readonly_ordinary'; [idtac|idtac|idtac|idtac|apply Hstep|idtac]; eauto.
                  intros. by exploit call_excall; eauto.
                  by intros [? _].
                  simpl. rewrite Hrd2. by intros [? _].

            intro Hsim. inv Hsim. inv Hec1. inv Hec2. simpl in *.
            rewrite <- Hblock_hint in Hblock_hint0. inv Hblock_hint0.
            rewrite <- Hhints in Hhints0. inv Hhints0.
            exploit hint_lookup_uniq; [apply Hhint''|apply Hhint0|].
            intro. by subst.
        * unfold exCallUpdateLocals in *.
          destruct oresult as [oresult1|]; [|done].
          exploit Horesult1; eauto. clear Horesult1.
          intros [results2 [Hresult2 Hinj]]. subst.
          remember (fit_gv (CurTargetData cfg1) typ0 oresult1) as oresult1'. destruct oresult1' as [oresult1'|]; [|done].
          exploit genericvalues_inject.simulation__fit_gv; eauto;
            [by inv Hvmem; eauto|].
          intros [oresult2' [Horesult2' Hinj']].
          rewrite Htd in Horesult2'. rewrite Horesult2' in *.
          inv H30. inv H37.
          exploit Hnext; [idtac|idtac|idtac|idtac|idtac
                         |idtac|idtac|idtac
                         |by eapply logical_step_preservation; eauto
                         |by eapply logical_step_preservation; eauto
                         |idtac]; eauto.
            by apply inject_incr'_refl.
            (* *) intro Hrd1. apply is_call_readonly_iff in Hrd1.
                  exploit readonly_ordinary'; [idtac|idtac|idtac|idtac|apply Hstep1|idtac]; eauto.
                  intros. by exploit call_excall; eauto.
                  by intros [? _].
                  simpl. rewrite Hrd1. by intros [? _].
            (* *) intro Hrd2. apply is_call_readonly_iff in Hrd2.
                  exploit readonly_ordinary'; [idtac|idtac|idtac|idtac|apply Hstep|idtac]; eauto.
                  intros. by exploit call_excall; eauto.
                  by intros [? _].
                  simpl. rewrite Hrd2. by intros [? _].

            intro Hsim. inv Hsim. inv Hec1. inv Hec2. simpl in *.
            rewrite <- Hblock_hint in Hblock_hint0. inv Hblock_hint0.
            rewrite <- Hhints in Hhints0. inv Hhints0.
            exploit hint_lookup_uniq; [apply Hhint''|apply Hhint0|].
            intro. by subst.
      + eapply readonly_ordinary'; [idtac|idtac|idtac|idtac|apply Hstep1]; eauto.
        * intros. unfold is_call in FH. simpl in *.
          by exploit call_excall; eauto.
        * by intros [? _].
      + eapply readonly_ordinary'; [idtac|idtac|idtac|idtac|apply Hstep]; eauto.
        * intros. unfold is_call in FH. simpl in *.
          by exploit call_excall; eauto.
        * by intros [? _].
      + eapply inject_incr'_hint_sem_global_bot; eauto.
        eapply inject_incr'_weaken; eauto.
        instantiate (1 := nil). instantiate (1 := nil). done.

    (* return *)
    exists alpha. exists pi1. exists pi2.
    inv Hlocal.
    - generalize Hstep1. intro Hstep1'. rewrite (destruct_cfg cfg1) in Hstep1'. inv Hstep1'. inv Hpn. inv Hec. simpl in *.
      generalize Hstep. intro Hstep'. rewrite (destruct_cfg cfg2) in Hstep'. inv Hstep'. inv Hpn. inv Hec. simpl in *.
      apply negb_true_iff in Hn1. apply negb_true_iff in Hn2.
      repeat match goal with
               | [H: pop_one nil ?n _ _ _, H': noop_idx_zero_exists ?n = false |- _] =>
                 inv H; unfold pop_one_X in *; rewrite H' in *; [done|]
             end.
      inv Hnoop; [by inv Hnnn|].
      inv Hnoop0; [by inv Hnnn0|].
      inv Hnnn; [clear Hret|by inv Hbrc].
      inv Hnnn0; [clear Hret|by inv Hbrc].
      inv Hstep2. inv Hstep0.
      eexists. eexists. eexists. eexists. (repeat split); (try by eauto).
      simpl in *.
      inv Hcons. inv Hec1. inv Hec2.
      exploit (valid_products_valid_fdef fid0); eauto.
      intros [fdef4 [Hfdef4 [fh' [Hfh' Hfdef']]]].
      rewrite <- Hfdef3 in Hfdef4. inv Hfdef4.
      rewrite <- Hfh0 in Hfh'. inv Hfh'.
      exploit Hvalid_cmd; eauto.
      intros [? [? [? [hint' [hint'' [Hpop' [Hhint' [Hhint'' Himpl]]]]]]]].
      rewrite <- Hpop3 in Hpop'. inv Hpop'.
      unfold pop_one_X in Hpop3. remember (noop_idx_zero_exists n1) as hn1. destruct hn1; [done|]. inv Hpop3.
      unfold pop_one_X in Hpop4. remember (noop_idx_zero_exists n2) as hn2. destruct hn2; [done|]. inv Hpop4.
      econstructor; auto; eauto.
      + by eapply logical_step_preservation; eauto.
      + by eapply logical_step_preservation; eauto.
      + unfold returnUpdateLocals in H18, H21.
        rewrite <- Hretval1, <- Hretval2 in *.
        destruct (noret_dec noret1 noret2); [subst|done].
        destruct (typ_dec typ0 typ3); [subst|done].
        destruct noret2.
        * inv Hinsn. simpl in *.
          destruct Hvals as [Halc1 [Halc2 [Halc1' Halc2']]].
          exploit free_allocas_valid_memories; [idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|eauto|idtac]; eauto.
            inv Hvmem. intros x y Hx Hy. apply Hlipidisj1; auto. apply in_app. by right.
            inv Hvmem. intros x y Hx Hy. apply Hlipidisj2; auto. apply in_app. by right.
          intro Hvmem'.
          inv H18. inv H21.
          assert (Hnextblock1: Mem.nextblock mem1 <= Mem.nextblock mem1');
            [by eapply logical_semantic_step_mem_nextblock; eauto|].
          assert (Hnextblock2: Mem.nextblock mem2 <= Mem.nextblock mem2');
            [by eapply logical_semantic_step_mem_nextblock; eauto|].
          exploit Hnext; [idtac|idtac|idtac|idtac|idtac
                         |idtac|idtac|idtac
                         |by eapply logical_step_preservation; eauto
                         |by eapply logical_step_preservation; eauto
                         |idtac|idtac]; eauto.
            by apply inject_incr'_refl.
            by eapply free_allocas_valid_allocas; eauto.
            punfold Hreadonly1. inv Hreadonly1; [by exfalso; apply Hnret|by inv Hcall|].
            intro Hrd1. apply is_call_readonly_iff in Hrd1. rewrite Hrd1 in Hextends.
            rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0. simpl in *.
            rewrite H27 in H20. inv H20. done.
            punfold Hreadonly2. inv Hreadonly2; [by exfalso; apply Hnret|by inv Hcall|].
            intro Hrd2. apply is_call_readonly_iff in Hrd2. rewrite Hrd2 in Hextends.
            rewrite (destruct_cfg cfg2) in Hstep0. inv Hstep0. simpl in *.
            rewrite H27 in H17. inv H17. done.

        * rewrite lift_op1_prop in *.
          remember (fit_gv (CurTargetData cfg1) typ3 retval1) as retval1'. destruct retval1' as [retval1'|]; [|done].
          inv Hinsn. simpl in *.
          destruct Hvals as [Halc1 [Halc2 [Halc1' Halc2']]].
          exploit free_allocas_valid_memories; [idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|eauto|idtac]; eauto.
            inv Hvmem. intros x y Hx Hy. apply Hlipidisj1; auto. apply in_app. by right.
            inv Hvmem. intros x y Hx Hy. apply Hlipidisj2; auto. apply in_app. by right.
          intro Hvmem'.
          exploit genericvalues_inject.simulation__fit_gv; eauto; [by inv Hvmem'; eauto|].
          intros [retval2' [Hretval2' Hinj']]. rewrite Htd in Hretval2'. rewrite Hretval2' in *.
          inv H18. inv H21.
          assert (Hnextblock1: Mem.nextblock mem1 <= Mem.nextblock mem1');
            [by eapply logical_semantic_step_mem_nextblock; eauto|].
          assert (Hnextblock2: Mem.nextblock mem2 <= Mem.nextblock mem2');
            [by eapply logical_semantic_step_mem_nextblock; eauto|].
          exploit Hnext; [idtac|idtac|idtac|idtac|idtac
                         |idtac|idtac|idtac
                         |by eapply logical_step_preservation; eauto
                         |by eapply logical_step_preservation; eauto
                         |idtac|idtac]; eauto.
            by apply inject_incr'_refl.
            by eapply free_allocas_valid_allocas; eauto.
            punfold Hreadonly1. inv Hreadonly1; [by exfalso; apply Hnret|by inv Hcall|].
            intro Hrd1. apply is_call_readonly_iff in Hrd1. rewrite Hrd1 in Hextends.
            rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0. simpl in *.
            rewrite H27 in H20. inv H20. done.
            punfold Hreadonly2. inv Hreadonly2; [by exfalso; apply Hnret|by inv Hcall|].
            intro Hrd2. apply is_call_readonly_iff in Hrd2. rewrite Hrd2 in Hextends.
            rewrite (destruct_cfg cfg2) in Hstep0. inv Hstep0. simpl in *.
            rewrite H27 in H17. inv H17. done.
            punfold Hreadonly1. inv Hreadonly1; [by exfalso; apply Hnret|by inv Hcall|].
            pclearbot. rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0. simpl in *.
            rewrite H29 in H20. inv H20.
            rewrite H30 in H21. inv H21.
            by eauto.
            punfold Hreadonly2. inv Hreadonly2; [by exfalso; apply Hnret|by inv Hcall|].
            pclearbot. rewrite (destruct_cfg cfg2) in Hstep0. inv Hstep0. simpl in *.
            rewrite H29 in H17. inv H17.
            rewrite H30 in H18. inv H18.
            by eauto.

      + eapply inject_incr'_hint_sem_global_bot; eauto.
        * eapply logical_semantic_step_mem_nextblock. eauto.
        * eapply logical_semantic_step_mem_nextblock. eauto.
        * by apply inject_incr'_refl.

    - generalize Hstep1. intro Hstep1'. rewrite (destruct_cfg cfg1) in Hstep1'. inv Hstep1'. inv Hpn. inv Hec. simpl in *.
      generalize Hstep. intro Hstep'. rewrite (destruct_cfg cfg2) in Hstep'. inv Hstep'. inv Hpn. inv Hec. simpl in *.
      apply negb_true_iff in Hn1. apply negb_true_iff in Hn2.
      repeat match goal with
               | [H: pop_one nil ?n _ _ _, H': noop_idx_zero_exists ?n = false |- _] =>
                 inv H; unfold pop_one_X in *; rewrite H' in *; [done|]
             end.
      inv Hnoop; [by inv Hnnn|].
      inv Hnoop0; [by inv Hnnn0|].
      inv Hnnn; [clear Hret|by inv Hbrc].
      inv Hnnn0; [clear Hret|by inv Hbrc].
      inv Hstep2. inv Hstep0.
      eexists. eexists. eexists. eexists. (repeat split); (try by eauto).
      inv Hcons. inv Hec1. inv Hec2.
      exploit (valid_products_valid_fdef fid0); eauto.
      intros [fdef4 [Hfdef4 [fh' [Hfh' Hfdef']]]].
      rewrite <- Hfdef3 in Hfdef4. inv Hfdef4.
      rewrite <- Hfh0 in Hfh'. inv Hfh'.
      exploit Hvalid_cmd; eauto.
      intros [? [? [? [hint' [hint'' [Hpop' [Hhint' [Hhint'' Himpl]]]]]]]].
      rewrite <- Hpop3 in Hpop'. inv Hpop'.
      unfold pop_one_X in Hpop3. remember (noop_idx_zero_exists n1) as hn1. destruct hn1; [done|]. inv Hpop3.
      unfold pop_one_X in Hpop4. remember (noop_idx_zero_exists n2) as hn2. destruct hn2; [done|]. inv Hpop4.
      econstructor; auto; eauto.
      + by eapply logical_step_preservation; eauto.
      + by eapply logical_step_preservation; eauto.
      + destruct (noret_dec noret1 noret2); [subst|done].
        destruct (typ_dec typ1 typ2); [subst|done].
        inv H16. destruct noret2; [|done].
        inv Hinsn. simpl in *.
        destruct Hvals as [Halc1 [Halc2 [Halc1' Halc2']]].
        exploit free_allocas_valid_memories; [idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|idtac|eauto|idtac]; eauto.
        * inv Hvmem. intros x y Hx Hy. apply Hlipidisj1; auto. apply in_app. by right.
        * inv Hvmem. intros x y Hx Hy. apply Hlipidisj2; auto. apply in_app. by right.
        intro Hvmem'.
        assert (Hnextblock1: Mem.nextblock mem1 <= Mem.nextblock mem1');
          [by eapply logical_semantic_step_mem_nextblock; eauto|].
        assert (Hnextblock2: Mem.nextblock mem2 <= Mem.nextblock mem2');
          [by eapply logical_semantic_step_mem_nextblock; eauto|].
          exploit Hnext; [idtac|idtac|idtac|idtac|idtac
                         |idtac|idtac|idtac
                         |by eapply logical_step_preservation; eauto
                         |by eapply logical_step_preservation; eauto
                         |idtac|idtac]; eauto.
            by apply inject_incr'_refl.
            by eapply free_allocas_valid_allocas; eauto.
            punfold Hreadonly1. inv Hreadonly1; [by exfalso; apply Hnret|by inv Hcall|].
            intro Hrd1. apply is_call_readonly_iff in Hrd1. rewrite Hrd1 in Hextends.
            rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0. simpl in *.
            rewrite H27 in H18. inv H18. done.
            punfold Hreadonly2. inv Hreadonly2; [by exfalso; apply Hnret|by inv Hcall|].
            intro Hrd2. apply is_call_readonly_iff in Hrd2. rewrite Hrd2 in Hextends.
            rewrite (destruct_cfg cfg2) in Hstep0. inv Hstep0. simpl in *.
            rewrite H27 in H15. inv H15. done.
            punfold Hreadonly1. inv Hreadonly1; [by exfalso; apply Hnret|by inv Hcall|].
            pclearbot. rewrite (destruct_cfg cfg1) in Hstep0. inv Hstep0. simpl in *.
            rewrite H27 in H18. inv H18.
            by eauto.
            punfold Hreadonly2. inv Hreadonly2; [by exfalso; apply Hnret|by inv Hcall|].
            pclearbot. rewrite (destruct_cfg cfg2) in Hstep0. inv Hstep0. simpl in *.
            rewrite H27 in H15. inv H15.
            by eauto.

      + eapply inject_incr'_hint_sem_global_bot; eauto.
        * eapply logical_semantic_step_mem_nextblock. eauto.
        * eapply logical_semantic_step_mem_nextblock. eauto.
        * by apply inject_incr'_refl.
  Qed.

  Lemma global_hint_sem_F_progress_hint_sem
    alpha li1 li2
    ecs1 mem1 ns1
    ecs2 mem2 ns2
    (Hsem: hint_sem_global alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2) :
    F_progress cfg1 cfg2 fn_al1 fn_al2 ecs1 mem1 ns1 ecs2 mem2 ns2.
  Proof.
    inv Hsem. eapply hint_sem_F_progress_hint_sem; eauto.
    - instantiate (1 := fh).
      instantiate (1 := fid).
      instantiate (1 := fdef2).
      instantiate (1 := fdef1).
      clear -Hfh Hfdef1 Hfdef2 Hvalid.
      generalize dependent fid.
      generalize dependent Hvalid.
      generalize (CurProducts cfg2).
      generalize (CurProducts cfg1).
      induction l0; intros [|hd2 tl2] Hv fid H1 H2 Hfh;
        try by inv H1.
      destruct a, hd2; simpl in Hv; try destruct fdec5; try done.
      + simpl in H1, H2.
        eapply IHl0; eauto.
        apply andb_true_iff in Hv. destruct Hv.
        done.
      + simpl in H1, H2.
        eapply IHl0; eauto.
        destruct fdec0.
        apply andb_true_iff in Hv. destruct Hv.
        done.
      + apply andb_true_iff in Hv. destruct Hv.
        apply andb_true_iff in H. destruct H.
        destruct id_dec in H; [|done].
        simpl in H1, H2. rewrite e in H1.
        destruct (getFdefID fdef0 == fid).
        * inv H1. inv H2.
          rewrite <- e in Hfh. rewrite <- Hfh in H3.
          rewrite e in H3.
          rewrite ? get_noop_by_fname_lookupALOpt in H3.
          done.
        * by eapply IHl0; eauto.
    - econstructor; eauto.
      constructor; simpl.
      + destruct fdef1. destruct fheader5. symmetry in Hfdef1.
        exploit lookupFdefViaIDFromProducts_ideq; eauto.
      + destruct fdef2. destruct fheader5. symmetry in Hfdef2.
        exploit lookupFdefViaIDFromProducts_ideq; eauto.
      + eapply hint_sem_global_bot_noret_dec; eauto.
  Qed.

  Theorem global_hint_sem_F_hint_sem
    alpha li1 li2
    ecs1 mem1 ns1
    ecs2 mem2 ns2
    (Hsem: hint_sem_global alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2) :
    F_global hint_sem_global alpha li1 li2 ecs1 mem1 ns1 ecs2 mem2 ns2.
  Proof.
    split.
    - by eapply global_hint_sem_F_progress_hint_sem; eauto.
    - by eapply global_hint_sem_F_step_hint_sem; eauto.
  Qed.
End Relations.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
