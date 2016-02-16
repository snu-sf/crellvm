Require Import sflib.
Require Import vellvm.

Require Import decs.
Require Import validator_aux.
Require Import validator_props.
Require Import set_facts2.
Require Import state_props.
Require Import hint_sem.
Require Import hint_sem_aux.
Require Import logical_step.
Require Import infrules.

Import Opsem.
Require Import syntax_ext.
Require Import hints.

Require Import hint_sem_props_resolve_defs.
(* Require Import hint_sem_props_resolve_cond. *)

Ltac arith_microtac :=
  match goal with
    | [H: eq_reg_sem _ _ _ _ _ _ _ |- _] =>
      let gvs := fresh "gvs" in
      let gvs' := fresh "gvs'" in
      let r := fresh "r" in
      let Hlookup := fresh "Hlookup" in
      let Hrhs := fresh "Hrhs" in
      let Hgvs := fresh "Hgvs" in
      let HH := fresh "HH" in
      inversion H as [gvs gvs' r Hlookup Hrhs Hgvs|?];
      [apply eq_gvs_implies_setoid_eq in Hgvs|];
      subst;
      clear H
    | [H: context[gundef ?td _] |- _] =>
      rewrite gundef_is in H
    | [|- context[gundef ?td _]] =>
      rewrite gundef_is
    | [H: context[DepElim.solution_left _ _ _ _ _ _] |- _] =>
      unfold DepElim.solution_left in H
    | [H: context[eq_rect_r _ _ _ _ _] |- _] =>
      unfold eq_rect_r in H
    | [H: context[eq_rect _ _ _ _ _ _ _] |- _] =>
      rewrite <- Eqdep_dec.eq_rect_eq_dec in H; [|by apply eq_nat_dec]
    | [|- context[DepElim.solution_left _ _ _ _ _ _]] =>
      unfold DepElim.solution_left
    | [|- context[eq_rect_r _ _ _ _ _]] =>
      unfold eq_rect_r
    | [|- context[eq_rect _ _ _ _ _ _ _]] =>
      rewrite <- Eqdep_dec.eq_rect_eq_dec; [|by apply eq_nat_dec]
    | [H: ret _ = ret _ |- _] => inv H
    | [|- ret _ = ret _] => f_equal
    | [|- Vint _ _ = Vint _ _] => f_equal
    | [|- val2GV _ _ _ = val2GV _ _ _] => f_equal
    | [H: existT (?s:nat -> Type) ?a ?x = existT ?s ?a ?y |- _] =>
      apply EqDec.inj_right_pair in H; subst
        
    | [H: merror = GV2val _ ?g |- _] =>
      let gg := fresh "gg" in
      let gh := fresh "gh" in
      let gt := fresh "gt" in
      let H' := fresh "H'" in
      remember g as gg;
      destruct gg as [|gh gt];
      inversion H as [H'];
      destruct gt, gh;
      inv H'

    | [|- ret _ = ret _ -> _] =>
      let H := fresh "H" in
      intro H; inv H

    | [|- context[GV2val _ (cgv2gvs DGVs (val2GV _ _ _) _)]] =>
      rewrite GV2val_val2GV; [|done]
    | [H: context[GV2val _ (cgv2gvs DGVs (val2GV _ _ _) _)] |- _] =>
      rewrite GV2val_val2GV in H; [|done]
    | [|- context[GV2val _ (val2GV _ _ _)]] =>
      rewrite GV2val_val2GV'; [|done]
    | [H: context[GV2val _ (val2GV _ _ _)] |- _] =>
      rewrite GV2val_val2GV' in H; [|done]
    | [|- context[cgv2gvs DGVs (val2GV _ _ _) _]] =>
      rewrite cgv2gvs_val2GV; [|done]
    | [H: context[cgv2gvs DGVs (val2GV _ _ _) _] |- _] =>
      rewrite cgv2gvs_val2GV in H; [|done]

    | [H: context[Int.eq ?s ?a ?b] |- _] =>
      rewrite Int_eq_eq_dec in H
    | [|- context[Int.eq ?s ?a ?b]] =>
      rewrite Int_eq_eq_dec
    | [H: context[Int.eq_dec ?s ?a ?b] |- _] =>
      destruct (Int.eq_dec s a b); [subst|]
    | [|- context[Int.eq_dec ?s ?a ?b]] =>
      destruct (Int.eq_dec s a b); [subst|]
    | [|- context[eq_nat_dec ?a ?b]] =>
      destruct (eq_nat_dec a b); [subst|]
    | [H: context[eq_nat_dec ?a ?b] |- _] =>
      destruct (eq_nat_dec a b); [subst|]

    | [|- context[GV2val ?td ?g]] =>
      let gg := fresh "gg" in
      remember (GV2val td g) as gg; destruct gg as [[]|]
  end.

Ltac arith_tac :=
  repeat
    (unfold mbop in *;
     repeat (arith_microtac; auto);
     unfold Val.add_obligation_3 in *;
     unfold Val.add_obligation_2 in *;
     unfold Val.add_obligation_1 in *;
     unfold Val.sub_obligation_3 in *;
     unfold Val.sub_obligation_2 in *;
     unfold Val.sub_obligation_1 in *;
     unfold Val.mul_obligation_3 in *;
     unfold Val.mul_obligation_2 in *;
     unfold Val.mul_obligation_1 in *;
     unfold Val.shl_obligation_3 in *;
     unfold Val.shl_obligation_2 in *;
     unfold Val.shl_obligation_1 in *;
     unfold Val.divs_obligation_3 in *;
     unfold Val.divs_obligation_2 in *;
     unfold Val.divs_obligation_1 in *;
     unfold Val.divu_obligation_3 in *;
     unfold Val.divu_obligation_2 in *;
     unfold Val.divu_obligation_1 in *;
     unfold Val.mods_obligation_3 in *;
     unfold Val.mods_obligation_2 in *;
     unfold Val.mods_obligation_1 in *;
     unfold Val.modu_obligation_3 in *;
     unfold Val.modu_obligation_2 in *;
     unfold Val.modu_obligation_1 in *;
     unfold Val.shl_obligation_3 in *;
     unfold Val.shl_obligation_2 in *;
     unfold Val.shl_obligation_1 in *;
     unfold Val.xor_obligation_1 in *;
     unfold Val.and_obligation_1 in *;
     unfold Val.or_obligation_1 in *;
     simpl; (try subst); auto; (try done)).

Lemma infrule_correct_neq_generate_gm:
  forall m1 m2 x y, infrule_prop m1 m2 (rule_neq_generate_gm x y).
Proof.
  repeat intro; infrule_tac.
  infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  { inv Hrhs. }
  unfold neq_reg_sem. rewrite Hlookup.
  unfold cond_is_global in H0.
  apply existsb_exists in H0.
  destruct H0 as [y [Hin Hdec]].
  destruct (id_dec y x); [subst|done].
  generalize dependent Hin.
  inv Hmatch. generalize dependent Hgid1.
  unfold is_global_ids.
  generalize (collect_global_ids (get_products_from_module m1)).
  intros gls Hgls Hin.
  eapply Forall_forall in Hgls; eauto.
  remember (lookupAL GenericValue (Globals cfg1) x) as gx; destruct gx as [gx|]; [|done].
  exploit (genericvalues_inject.wf_globals__wf_global _ _ gx x Hgl1); eauto.
  intro Hg.
  destruct gvs; try done. destruct p.
  destruct gvs; simpl in Hptr; [|by destruct v].
  destruct v; try done. inv Hptr.
  split.
  - intro Heq. apply eq_gvs_implies_setoid_eq in Heq. subst.
    destruct Hg. omega.
  - repeat split; auto.
    + generalize dependent Hg. clear Heqgx. clear Hgls.
      induction gx; [done|].
      simpl. destruct a.
      destruct v; try by apply IHgx.
      intros [Hb Hinj]. split; [|by apply IHgx].
      split; [|done].
      intro Heq. subst. omega.
    + by eapply Hgdef1; eauto.
Qed.
Hint Resolve infrule_correct_neq_generate_gm: InfRuleDb.
