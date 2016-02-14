Require Import sflib.

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
Require Import hint_sem_props_proceed_branch.

Require Import lopsem.
Require Import behavior.
Require Import paco.

Import Opsem.

Definition lstuck_state cfg pnoops lst :=
  ~ exists lst', exists tr, lsInsn cfg pnoops lst lst' tr.

(** logical behavior **)
Inductive lbehmatch (cfg:Config) (pnoops: products_noop_t) lbehave : lState -> observation -> Prop :=
| lbeh_err ls obs
  (STUCK: lstuck_state cfg pnoops ls)
  (NFINAL: s_isFinialState cfg ls.(state) = None)
  : lbehmatch cfg pnoops lbehave ls obs
| lbeh_done ls
  (STUCK: lstuck_state cfg pnoops ls)
  (FINAL: s_isFinialState cfg ls.(state) <> None)
  : lbehmatch cfg pnoops lbehave ls obs_done
| lbeh_inftau ls ls'
    (ST: lsInsn cfg pnoops ls ls' E0)
    (INF: lbehave ls' obs_inftau : Prop)
  : lbehmatch cfg pnoops lbehave ls obs_inftau
| lbeh_evt ls ls' tr obs
    (ST: lsInsn cfg pnoops ls ls' tr)
    (TR: tr <> E0)
    (INF: lbehave ls' obs : Prop)
  : lbehmatch cfg pnoops lbehave ls (trace_observation tr obs)
.
Hint Constructors lbehmatch.

Inductive lbehave_ cfg pnoops lbehave ls obs : Prop :=
lbehave_intro ls'
  (MAT: lbehmatch cfg pnoops lbehave ls' obs)
  (TAU: lsop_star cfg pnoops ls ls' E0).
Hint Constructors lbehave_.

Definition lbehave cfg pnoops : _ -> _ -> Prop := paco2 (lbehave_ cfg pnoops) bot2.

Lemma lbehave_mon cfg pnoops: monotone2 (@lbehave_ cfg pnoops).
Proof.
  ii; destruct IN; destruct MAT; eauto.
Qed.
Hint Resolve lbehave_mon: paco.

Program Definition mkInitLState ec ecs mem n :=
  mkLState (mkState ec [ecs] mem) [n] (_match_state_ns _ _ eq_refl).

Lemma mkInitLState_state ec ecs mem n :
  state (mkInitLState ec ecs mem n) = mkState ec [ecs] mem.
Proof. done. Qed.

Lemma mkInitLState_ns ec ecs mem n :
  ns (mkInitLState ec ecs mem n) = [n].
Proof. done. Qed.

Definition ls_genInitState (S:system) pnoops (main:id) (Args:list GVs) (initmem:mem)
  : option (Config * lState) :=
match (lookupFdefViaIDFromSystem S main) with
| None => None
| Some CurFunction =>
  match (getParentOfFdefFromSystem CurFunction S) with
  | None => None
  | Some (module_intro CurLayouts CurNamedts CurProducts) =>
    let initargetdata :=
      initTargetData CurLayouts CurNamedts initmem in
    match (genGlobalAndInitMem initargetdata CurProducts nil nil
      initmem) with
    | None => None
    | Some (initGlobal, initFunTable, initMem) =>
      match (getEntryBlock CurFunction) with
      | None => None
      | Some (l, stmts_intro ps cs tmn) =>
          match CurFunction with
          | fdef_intro (fheader_intro _ rt fid la _) _ =>
            match initLocals initargetdata la Args with
            | Some Values =>
              Some
              (mkCfg
                S
                initargetdata
                CurProducts
                initGlobal
                initFunTable,
                mkInitLState
                 (
                  mkEC
                  CurFunction
                  (l, stmts_intro ps cs tmn)
                  cs
                  tmn
                  Values
                  nil
                 )
                 (
                  mkEC
                  CurFunction
                  (l, stmts_intro ps cs tmn)
                  cs
                  tmn
                  Values
                  nil
                 )
                 initMem
                 (get_noop_by_bb l (lookupALOpt _ pnoops fid)))
            | None => None
            end
        end
      end
    end
  end
end.

Lemma s_genInitState_ls_genInitState s pnoops main args mem cfg ist
  (H: s_genInitState s main args mem = Some (cfg, ist)) :
  exists ist',
    ls_genInitState s pnoops main args mem = Some (cfg, ist') /\
    ist = (state ist').
Proof.
  generalize dependent H.
  unfold s_genInitState, ls_genInitState.
  destruct (lookupFdefViaIDFromSystem s main); [|done].
  destruct (getParentOfFdefFromSystem f s); [|done].
  destruct m.
  destruct (genGlobalAndInitMem (initTargetData layouts5 namedts5 mem) products5 nil nil mem); [|done].
  destruct p. destruct p.
  destruct (getEntryBlock f); [|done].
  destruct b. destruct s0. destruct f. destruct fheader5.
  destruct (initLocals (initTargetData layouts5 namedts5 mem) args5 args); [|done].
  intro H. admit. (* inv H.
  eexists. eauto. *)
Qed.

Lemma ls_genInitState_s_genInitState s pnoops main args mem cfg ist
  (H: ls_genInitState s pnoops main args mem = Some (cfg, ist)) :
  s_genInitState s main args mem = Some (cfg, state ist).
Proof.
  generalize dependent H.
  unfold s_genInitState, ls_genInitState.
  destruct (lookupFdefViaIDFromSystem s main); [|done].
  destruct (getParentOfFdefFromSystem f s); [|done].
  destruct m.
  destruct (genGlobalAndInitMem (initTargetData layouts5 namedts5 mem) products5 nil nil mem); [|done].
  destruct p. destruct p.
  destruct (getEntryBlock f); [|done].
  destruct b. destruct s0. destruct f. destruct fheader5.
  destruct (initLocals (initTargetData layouts5 namedts5 mem) args5 args); [|done].
  intro H. admit. (* by inv H. *)
Qed.

Inductive lbehave_prog m pnoops main args obs : Prop :=
| _lbehave_prog :
  forall cfg ist
    (Hinit: ls_genInitState [m] pnoops main args Mem.empty = Some (cfg, ist))
    (Hobs: lbehave cfg pnoops ist obs),
    lbehave_prog m pnoops main args obs.

Lemma Eapp_E0_inv tr1 tr2 (H: tr1 ** tr2 = E0) :
  tr1 = E0 /\ tr2 = E0.
Proof. by destruct tr1, tr2. Qed.

Lemma stutter_lbehave cfg pnoops lst1 lst2 obs
  (Hbeh: lbehave cfg pnoops lst1 obs)
  (Hsem: lsInsn cfg pnoops lst1 lst2 E0)
  (Huniq: lsInsn_uniq cfg pnoops lst1)
  (Hsts: lst1.(state) = lst2.(state)) :
  lbehave cfg pnoops lst2 obs.
Proof.
  punfold Hbeh. inv Hbeh.
  inv TAU.
  - generalize (Huniq lst2 E0 Hsem). clear Huniq. intro Huniq.
    inv MAT.
    + unfold lstuck_state in STUCK. contradict STUCK.
      eexists. eexists. eauto.
    + by exploit STUCK; eauto.
    + pclearbot.
      exploit Huniq; eauto. intros [Hlst Htr].
      by subst.
    + pclearbot.
      exploit Huniq; eauto. intros [Hlst Htr].
      by subst.
  - exploit Eapp_E0_inv; eauto. intros [? ?]. subst.
    exploit (Huniq lst2 E0 Hsem lst3); eauto. intros [Hlst _].
    subst. pfold. econs; eauto.
Qed.

Lemma trace_observation_E0 obs : trace_observation E0 obs = obs.
Proof. done. Qed.

Lemma lstutter_star_lbehave cfg pnoops lst1 lst2 obs
  (Hbeh: lbehave cfg pnoops lst1 obs)
  (Hsem: lstutter_star cfg pnoops lst1 lst2) :
  lbehave cfg pnoops lst2 obs.
Proof.
  induction Hsem; auto.
  apply IHHsem.
  eapply stutter_lbehave; eauto.
Qed.

Lemma E0_app_inv tr1 tr2 (H: tr1 ** tr2 = E0) :
  tr1 = E0 /\ tr2 = E0.
Proof. by destruct tr1, tr2. Qed.


(* physical = logical behaviors *)
Lemma destruct_lsop_plus cfg pnoops lst1 lst2 lst3 tr12 tr23
  (Hstut: no_stuttering lst1)
  (H12: lsop_star_rev cfg pnoops lst1 lst2 tr12)
  (H23: lsInsn cfg pnoops lst2 lst3 tr23) :
  exists mst1, no_stuttering mst1 /\
    exists tr1, lsop_star_rev cfg pnoops lst1 mst1 tr1 /\ 
      exists mst2, lstutter_star cfg pnoops mst2 lst3 /\
        exists tr2, lsInsn cfg pnoops mst1 mst2 tr2 /\ tr12 ** tr23 = tr1 ** tr2.
Proof.
  generalize dependent tr23.
  generalize dependent lst3.
  induction H12; intros lst0 tr23 H23.
  - eexists. split; [eauto|].
    exists E0. split; [by econs|].
    eexists. split; [by econs|].
    eexists. split; eauto. 
  - destruct (no_stuttering_dec lst3).
    + exists lst3. split; [auto|].
      eexists. split; [by econs; eauto|].
      exists lst0. split; [by econs|].
      eexists. split; eauto.
    + exploit stuttering_lsInsn; eauto. intros [Hst [Hns ?]]. subst.
      exploit IHlsop_star_rev; eauto.
      intros [mst1 [Hstut' [tr3 [Hrev [mst2 [Hstut'' [tr4 [Hinsn Htr]]]]]]]].
      exists mst1. split; auto.
      eexists; split; [eauto|].
      exists mst2. split.
      * eapply lstutter_star_snoc; eauto.
        by apply stuttering_lsInsn_uniq.
      * eexists. split; [eauto|].
        by rewrite Htr, E0_right.
Qed.

Lemma stuttering_lsInsn' cfg pnoops lst1
  (Hstut: ~ no_stuttering lst1) :
  exists lst2,
    lsInsn cfg pnoops lst1 lst2 E0 /\
    lst1.(state) = lst2.(state) /\ length lst1.(ns) = length lst2.(ns).
Proof.
  destruct lst1 as [st [|n ns]];
    [by exfalso; apply Hstut; econs|]. admit. (*
  destruct st as [|[ec ecs] mem]; [by inversion Hmatch|].
  exploit logical_semantic_step_lsInsn; eauto;
    [|intros [Hmatch' Hstep]; eexists; split; [by eexact Hstep|]]; simpl.
  - remember (stutter_num n) as s. destruct s.
    + exfalso. apply Hstut. eapply no_stuttering_cons; simpl; eauto.
    + econs; simpl in *; eauto.
      * eapply pop_one_cmd; eauto. unfold pop_one_X.
        by erewrite stutter_num_noop_idx_zero_exists; eauto.
      * eapply logical_semantic_step_noop_stk_cmd.
        eapply logical_semantic_step_noop_cmd_noop; eauto.
      * split; eauto.
  - done. *)
Qed.

Theorem lbehave_behave cfg pnoops lst obs
  (Hobsl: lbehave cfg pnoops lst obs) :
  behave cfg lst.(state) obs.
Proof.
  generalize dependent obs.
  generalize dependent lst.
  pcofix CIH. intros lst obs Hobs.
  generalize (stutter_lState cfg pnoops lst). intros [lst' [Hlst' Hstut]].
  exploit lstutter_star_lbehave; eauto. intro Hbeh'.
  erewrite lstutter_star_state; eauto.
  clear Hlst' Hobs lst. rename lst' into lst.
  punfold Hbeh'. inv Hbeh'. pfold.
  inv MAT.
  - econs; [|by exploit lsop_star_sop_star; eauto].
    apply beh_err; auto.
    intros [st' [tr Hstep]]. apply STUCK.
    destruct (no_stuttering_dec ls').
    + exploit sInsn_no_stuttering; eauto.
      intros [lst' [Hlstep ?]]. subst.
      eexists. eexists. eauto.
    + exploit stuttering_lsInsn'; eauto.
      intros [lst' [Hlstep [? ?]]].
      eexists. eexists. eauto.
  - econs; [|by exploit lsop_star_sop_star; eauto].
    apply beh_done; auto.
    intros [st' [tr Hstep]]. apply STUCK.
    destruct (no_stuttering_dec ls').
    + exploit sInsn_no_stuttering; eauto.
      intros [lst' [Hlstep ?]]. subst.
      eexists. eexists. eauto.
    + exploit stuttering_lsInsn'; eauto.
      intros [lst' [Hlstep [? ?]]].
      eexists. eexists. eauto.
  - pclearbot.
    exploit lsop_star_lsop_star_rev; eauto. intro TAUr.
    exploit destruct_lsop_plus; eauto.
    intros [mst1 [Hmst1 [tr1 [Hinsn1 [mst2 [Hstut2 [tr2 [Hinsn2 Htr]]]]]]]].
    rewrite E0_left in Htr. exploit E0_app_inv; eauto. intros [? ?]. subst.
    econs. instantiate (1 := state mst1).
    + eapply beh_inftau; eauto.
      erewrite <- (lstutter_star_state cfg pnoops mst2 ls'0); eauto.
      eapply no_stuttering_lsInsn; eauto.
    + eapply lsop_star_sop_star. apply lsop_star_rev_lsop_star. eauto.
  - pclearbot.
    exploit lsInsn_sInsn; eauto. intros [Hinsn|[Hst [Hns Htr]]]; [|done].
    econs.
    + eapply beh_evt; eauto.
    + eapply lsop_star_sop_star. eauto.
Qed.    

Theorem behave_lbehave cfg pnoops lst obs
  (Hobs: behave cfg lst.(state) obs) :
  lbehave cfg pnoops lst obs.
Proof.
  destruct lst.
  generalize dependent Hobs.
  generalize dependent obs.
  generalize dependent ns.
  generalize dependent state.
  pcofix CIH. intros state noop Hmatch obs Hobs. punfold Hobs. inv Hobs. pfold.
  simpl in *.
  exploit (sop_star_lsop_star cfg pnoops {| state := state; ns := noop; Hmatch := Hmatch |}); eauto.
  intros [mst1 [Hmst1 [? Hstut1]]]. subst.
  inv MAT.
  - econs; [|by apply Hmst1].
    apply lbeh_err; auto.
    intros [st' [tr Hstep]]. apply STUCK.
    apply no_stuttering_lsInsn in Hstep; auto.
    eexists. eexists. eauto.
  - econs; [|by apply Hmst1].
    apply lbeh_done; auto.
    intros [st' [tr Hstep]]. apply STUCK.
    apply no_stuttering_lsInsn in Hstep; auto.
    eexists. eexists. eauto.
  - pclearbot.
    exploit sInsn_no_stuttering; eauto.
    intros [mst2 [Hmst2 ?]]. subst.
    econs; eauto.
    eapply lbeh_inftau; eauto.
    right. rewrite (destruct_lState mst2).
    by apply CIH.
  - pclearbot.
    exploit sInsn_no_stuttering; eauto.
    intros [mst2 [Hmst2 ?]]. subst.
    econs; eauto.
    eapply lbeh_evt; eauto.
    right. rewrite (destruct_lState mst2).
    by apply CIH.
Qed.

Theorem lbehave_prog_behave_prog m pnoops main args obs
  (H: lbehave_prog m pnoops main args obs) :
  behave_prog m main args obs.
Proof.
  inv H.
  exploit ls_genInitState_s_genInitState; eauto. intro Hinit'.
  econs; eauto.
  eapply lbehave_behave; eauto.
Qed.

Theorem behave_prog_lbehave_prog m pnoops main args obs
  (H: behave_prog m main args obs) :
  lbehave_prog m pnoops main args obs.
Proof.
  inv H.
  exploit s_genInitState_ls_genInitState; eauto. intros [ist' [Hinit' ?]]. subst.
  econs; eauto.
  eapply behave_lbehave; eauto.
Qed.
