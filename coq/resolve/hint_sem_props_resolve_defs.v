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
Import syntax_ext.
Import hints.

Inductive matched_module_cfg (m1 m2:module) (cfg1 cfg2:OpsemAux.Config) : Prop :=
| matched_module_cfg_intro :
  forall
    (Htd: CurTargetData cfg1 = CurTargetData cfg2)
    (Hgl: Globals cfg1 = Globals cfg2)
    (Hgdef1: forall x v (Hv: ret v = lookupAL _ (Globals cfg1) x), not_undef v)
    (Hgdef2: forall x v (Hv: ret v = lookupAL _ (Globals cfg2) x), not_undef v)
    (Hgna1: globals_no_alias (Globals cfg1))
    (Hgna2: globals_no_alias (Globals cfg2))
    (Hgid1: is_global_ids (collect_global_ids (get_products_from_module m1)) (Globals cfg1))
    (Hgid2: is_global_ids (collect_global_ids (get_products_from_module m2)) (Globals cfg2)),
    matched_module_cfg m1 m2 cfg1 cfg2.

Definition infrule_prop (m1 m2:module) (i: infrule_t) : Prop :=
  forall
    (cfg1 cfg2: OpsemAux.Config) (Hmatch: matched_module_cfg m1 m2 cfg1 cfg2)
    (lc1 lc2: GVsMap)
    (maxb:Z) (alpha: meminj) (mem1 mem2: mem)
    (Hwf: genericvalues_inject.wf_sb_mi maxb alpha mem1 mem2)
    (Hgl1: genericvalues_inject.wf_globals maxb (Globals cfg1))
    (Hgl2: genericvalues_inject.wf_globals maxb (Globals cfg2))
    (li1 li2: list mblock)
    (h: insn_hint_t)
    (Hhint: hint_sem cfg1 cfg2 lc1 lc2 mem1 mem2 alpha maxb li1 li2 h),
    $$ cfg1; cfg2; lc1; lc2; mem1; mem2; alpha; maxb; li1; li2; infrule_sem m1 m2 i h $$.

Create HintDb InfRuleDb.

Lemma cgv2gvs_cgv2gv val typ :
  cgv2gvs DGVs val typ = cgv2gv val typ.
Proof.
  by infrule_tac.
Qed.    

Lemma GV2val_val2GV TD val chunk typ
  (Hval: val <> Vundef) :
  GV2val TD (cgv2gvs DGVs (val2GV TD val chunk) typ) = ret val.
Proof.
  unfold GV2val, val2GV.
  rewrite cgv2gvs_cgv2gv.
  by destruct val.
Qed.

Lemma GV2val_val2GV' TD val chunk
  (Hval: val <> Vundef) :
  GV2val TD (val2GV TD val chunk) = ret val.
Proof.
  unfold GV2val, val2GV.
  by destruct val.
Qed.

Lemma cgv2gvs_val2GV TD val chunk typ
  (Hval: val <> Vundef) :
  cgv2gvs DGVs (val2GV TD val chunk) typ = [(val, chunk)].
Proof.
  unfold val2GV.
  rewrite cgv2gvs_cgv2gv.
  by destruct val.
Qed.

Lemma gundef_is TD s :
  gundef TD (typ_int s) = ret [(Vundef, AST.Mint (Size.to_nat s - 1))].
Proof. by destruct TD. Qed.

Lemma Int_eq_eq_dec s a b :
  Int.eq s a b =
  if Int.eq_dec s a b
    then true
    else false.
Proof.
  destruct (Int.eq_dec s a b).
  - by subst; apply Int.eq_true.
  - by apply Int.eq_false.
Qed.

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
      apply eq_gvs_implies_setoid_eq in Hgvs;
      subst;
      clear H
    | [H: context[gundef ?td _] |- _] =>
      rewrite gundef_is in H
    | [|- context[gundef ?td _]] =>
      rewrite gundef_is

    | [H: context[DepElim.solution_left _ _ _ _ _ _ _] |- _] =>
      unfold DepElim.solution_left in H
    | [H: context[eq_rect_r _ _ _ _ _ _] |- _] =>
      unfold eq_rect_r in H
    | [H: context[eq_rect _ _ _ _ _ _ _ _] |- _] =>
      rewrite <- Eqdep_dec.eq_rect_eq_dec in H; [|by apply eq_nat_dec]
    | [|- context[DepElim.solution_left _ _ _ _ _ _ _]] =>
      unfold DepElim.solution_left
    | [|- context[eq_rect_r _ _ _ _ _ _]] =>
      unfold eq_rect_r
    | [|- context[eq_rect _ _ _ _ _ _ _ _]] =>
      rewrite <- Eqdep_dec.eq_rect_eq_dec; [|by apply eq_nat_dec]

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
