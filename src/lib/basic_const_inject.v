Require Import vgtac.
Require Import syntax.
Require Import infrastructure.
Require Import Memory.
Require Import targetdata.
Require Import genericvalues.
Require Import alist.
Require Import Integers.
Require Import Values.
Require Import Coqlib.
Require Import monad.
Require Import Metatheory.
Require Import Znumtheory.
Require Import typings.
Require Import infrastructure_props.
Require Import targetdata_props.
Require Import typings_props.
Require Import genericvalues_props.
Require Import memory_sim.

Import LLVMinfra.
Import LLVMgv.
Import LLVMtd.
Import LLVMtypings.

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import ott_list_core.

Require Import genericvalues_inject.

Require Import Metatheory.
Require Import syntax.
Require Import infrastructure.
Require Import ListSet.
Require Import List.
Require Import dom_list.
Require Import analysis.
Require Import targetdata.
Require Import alist.

Module LLVMtyping_rules.
Import LLVMsyntax.
Import LLVMinfra.

Lemma typ_ind_gen: forall P : typ -> Prop,
       (forall sz5 : sz, P (typ_int sz5)) ->
       (forall floating_point5 : floating_point,
        P (typ_floatpoint floating_point5)) ->
       P typ_void ->
       P typ_label ->
       P typ_metadata ->
       (forall (sz5 : sz) (typ5 : typ), P typ5 -> P (typ_array sz5 typ5)) ->
       (forall typ_5 : typ,
        P typ_5 ->
        forall (l : list typ) (varg5 : varg) (IH: Forall P l), P (typ_function typ_5 l varg5)) ->
       (forall (l : list typ) (IH: Forall P l), P (typ_struct l)) ->
       (forall typ5 : typ, P typ5 -> P (typ_pointer typ5)) ->
       (forall id5 : id, P (typ_namedt id5)) -> forall t : typ, P t.
Proof.
  intros; revert t; fix IH 1.
  intros; destruct t; try (by clear IH; eauto).
  - apply H4; eauto. 
  - apply H5; eauto. 
    induction l0; [by clear IH|].
    by econs; [apply IH| apply IHl0].
  - apply H6; eauto. 
    induction l0; [by clear IH|].
    by econs; [apply IH| apply IHl0].
  - apply H7; eauto. 
Qed.

Lemma const_ind_gen:
  forall P : const -> Prop,
       (forall typ5 : typ, P (const_zeroinitializer typ5)) ->
       (forall (sz5 : sz) (Int5 : Int), P (const_int sz5 Int5)) ->
       (forall (floating_point5 : floating_point) (Float5 : Float),
        P (const_floatpoint floating_point5 Float5)) ->
       (forall typ5 : typ, P (const_undef typ5)) ->
       (forall typ5 : typ, P (const_null typ5)) ->
       (forall (typ5 : typ) (l : list const) (IH: Forall P l), P (const_arr typ5 l)) ->
       (forall (typ5 : typ) (l : list const) (IH: Forall P l), P (const_struct typ5 l)) ->
       (forall (typ5 : typ) (id5 : id), P (const_gid typ5 id5)) ->
       (forall (truncop5 : truncop) (const5 : const),
        P const5 -> forall typ5 : typ, P (const_truncop truncop5 const5 typ5)) ->
       (forall (extop5 : extop) (const5 : const),
        P const5 -> forall typ5 : typ, P (const_extop extop5 const5 typ5)) ->
       (forall (castop5 : castop) (const5 : const),
        P const5 -> forall typ5 : typ, P (const_castop castop5 const5 typ5)) ->
       (forall (inbounds5 : inbounds) (const_5 : const),
        P const_5 -> forall (l : list const) (IH: Forall P l), P (const_gep inbounds5 const_5 l)) ->
       (forall const0 : const,
        P const0 ->
        forall const1 : const,
        P const1 ->
        forall const2 : const,
        P const2 -> P (const_select const0 const1 const2)) ->
       (forall (cond5 : cond) (const1 : const),
        P const1 ->
        forall const2 : const, P const2 -> P (const_icmp cond5 const1 const2)) ->
       (forall (fcond5 : fcond) (const1 : const),
        P const1 ->
        forall const2 : const,
        P const2 -> P (const_fcmp fcond5 const1 const2)) ->
       (forall const_5 : const,
        P const_5 -> forall (l : list const) (IH: Forall P l), P (const_extractvalue const_5 l)) ->
       (forall const_5 : const,
        P const_5 ->
        forall const' : const,
        P const' ->
        forall (l : list const) (IH: Forall P l), P (const_insertvalue const_5 const' l)) ->
       (forall (bop5 : bop) (const1 : const),
        P const1 ->
        forall const2 : const, P const2 -> P (const_bop bop5 const1 const2)) ->
       (forall (fbop5 : fbop) (const1 : const),
        P const1 ->
        forall const2 : const, P const2 -> P (const_fbop fbop5 const1 const2)) ->
       forall c : const, P c.
Proof.
  intros; revert c; fix IH 1.
  intros; destruct c; try (by clear IH; eauto).
  - apply H4. 
    induction l0; [by clear IH|].
    by econs; [apply IH| apply IHl0].
  - apply H5. 
    induction l0; [by clear IH|].
    by econs; [apply IH| apply IHl0].
  - apply H7; eauto. 
  - apply H8; eauto. 
  - apply H9; eauto.
  - apply H10; eauto. 
    induction l0; [by clear IH|].
    by econs; [apply IH| apply IHl0].
  - apply H11; eauto.
  - apply H12; eauto.
  - apply H13; eauto.
  - apply H14; eauto.
    induction l0; [by clear IH|].
    by econs; [apply IH| apply IHl0].
  - apply H15; eauto.
    induction l0; [by clear IH|].
    by econs; [apply IH| apply IHl0].
  - apply H16; eauto.
  - apply H17; eauto.
Qed.

Lemma gv_inject_app: forall mi gv1 gv2 gv1' gv2'
    (IN1: gv_inject mi gv1 gv1')
    (IN2: gv_inject mi gv2 gv2'),
  gv_inject mi (gv1 ++ gv2) (gv1' ++ gv2').
Proof.
  induction gv1.
  - i; destruct gv1'; [|inv IN1]; eauto.
  - i. destruct gv1'; inv IN1.
    econs; eauto.
Qed.

Lemma uninits_refl: forall n
    maxb mi Mem1 Mem2 (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2),
    gv_inject mi (uninits n) (uninits n).
Proof.
  i; induction n; econs; eauto. 
Qed.

Lemma repeatGV_refl: forall mi n g g'
    (INJ: gv_inject mi g g'),
  gv_inject mi (repeatGV g n) (repeatGV g' n).
Proof.
  induction n; s; eauto using gv_inject_app.
Qed.

Lemma zeroconst2GV_aux_refl: forall TD
    maxb mi Mem1 Mem2 (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2)
    acc (Hnc: forall id5 gv5, 
              lookupAL _ acc id5 = Some (Some gv5) ->
              gv_inject mi gv5 gv5)
    t gv (Hz: zeroconst2GV_aux TD acc t = Some gv),
  gv_inject mi gv gv.
Proof.
  intros until t.
  induction t using typ_ind_gen; i; ss; try by inv Hz; econs; eauto.
Case "floating point".
  destruct floating_point5; inv Hz; econs; eauto.
Case "array".
  destruct sz5 as [|s]; try solve [uniq_result; auto using gv_inject_uninits].
  inv_mbind; exploit IHt; eauto.
  eauto 10 using gv_inject_app, uninits_refl, repeatGV_refl. 
Case "struct".
  inv_mbind.  
  destruct g; inv H0; [by econs; eauto|].
  revert HeqR; generalize (p::g); clear p g; intro gv; i.
  revert_until l0; induction l0; s; i; [by inv HeqR; eauto|].
  inv IH; inv_mbind; eapply gv_inject_app.
    by symmetry_ctx; eauto.
  eapply gv_inject_app; eauto using uninits_refl.
Case "null".
  inv Hz; unfold null; inv Hwfsim; eauto.
Case "namedt".
  inv_mbind; symmetry_ctx; eauto.
Qed.

Lemma zeroconsts2GV_aux_refl: forall TD
    maxb mi Mem1 Mem2 (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2)
    acc (Hnc: forall id5 gv5, 
              lookupAL _ acc id5 = Some (Some gv5) ->
              gv_inject mi gv5 gv5)
    lt gv (Hz: zeroconsts2GV_aux TD acc lt = Some gv),
  gv_inject mi gv gv.
Proof.
  intros until lt; induction lt; s; i; [by inv Hz; econs; eauto|].
  inv_mbind; symmetry_ctx; exploit IHlt; eauto; intro IJT.
  eapply zeroconst2GV_aux_refl in HeqR0; eauto.
  eauto using gv_inject_app, uninits_refl.
Qed.

Lemma zeroconst2GV_for_namedts_refl: forall TD l
    maxb mi Mem1 Mem2 (Hwfsim: wf_sb_mi maxb mi Mem1 Mem2)
    n id gv (LU: lookupAL (monad GenericValue) (zeroconst2GV_for_namedts TD l n) id = ret (ret gv)),
  gv_inject mi gv gv.
Proof.
  intros until n; induction n; ss.
  i; destruct a; ss; destruct eq_dec; subst; eauto.
  inv LU; inv_mbind; symmetry_ctx.
  destruct g; inv H1; [by econs; eauto|].
  eapply zeroconsts2GV_aux_refl; eauto.
Qed.

Lemma zeroconst2GV_refl : forall maxb mi Mem1 Mem2 gv td t,
  wf_sb_mi maxb mi Mem1 Mem2 ->
  zeroconst2GV td t = Some gv ->
  gv_inject mi gv gv.
Proof. 
  i; destruct td. 
  eauto using zeroconst2GV_aux_refl, zeroconst2GV_for_namedts_refl.
Qed.

Lemma cgv2gv_refl: forall maxb mi Mem1 Mem2 g t,
    wf_sb_mi maxb mi Mem1 Mem2 ->
    gv_inject mi g g ->
  gv_inject mi (cgv2gv g t) (cgv2gv g t).
Proof.
  i; destruct g; eauto.
  destruct p; s; destruct v; eauto.
  destruct g; eauto. 
  destruct t; s; try by econs; eauto.
  - destruct floating_point5; econs; eauto.
  - unfold null; inv H; eauto.
Qed.

Lemma cgv2gv_refl_rev: forall maxb mi Mem1 Mem2 g t,
    wf_sb_mi maxb mi Mem1 Mem2 ->
    gv_inject mi (cgv2gv g t) (cgv2gv g t) ->
  gv_inject mi g g.
Proof.
  i; destruct g; eauto.
  destruct p; s; destruct v; eauto.
  destruct g; eauto. 
Qed.

Lemma const2GV_list_refl: forall maxb mi Mem1 Mem2 TD gl t ll gv
    (Hwf: wf_sb_mi maxb mi Mem1 Mem2)
    (IH: Forall
         (fun c : const =>
          forall gv : GenericValue,
          const2GV TD gl c = ret gv -> gv_inject mi gv gv) ll)
    (Hgv: _list_const_struct2GV_ _const2GV TD gl ll = ret (gv, t)),
  gv_inject mi gv gv.
Proof.
  i; revert ll t gv IH Hgv; induction ll.
  - i; inv Hgv; eauto using uninits_refl.
  - i; inv IH; unfold const2GV in Hgv; s in Hgv; inv_mbind.
    eapply gv_inject_app.
    + eapply cgv2gv_refl_rev; eauto.
      eapply H1; unfold const2GV; rewrite <- HeqR0; eauto.
    + eapply gv_inject_app; eauto using uninits_refl.
Qed.

Lemma const2GV_refl: forall maxb mi Mem Mem' TD gl c gv
    (Hwf: wf_sb_mi maxb mi Mem Mem')
    (Hgl: wf_globals maxb gl)
    (Hgv: const2GV TD gl c = Some gv),
  gv_inject mi gv gv.
Proof.
  i; revert gv Hgv; induction c using const_ind_gen
  ; [M|M|M|M|M| |M|M|M|M|M|M|M|M|M|M|M|M|M]; Mdo unfold const2GV; s; i; inv_mbind.
Case "zero".
  inv H0; apply symmetry in HeqR0.
  eauto using zeroconst2GV_refl, cgv2gv_refl.
Case "int".
  inv Hgv; econs; eauto.
Case "floatingpoint".
  inv H0; destruct floating_point5; inv HeqR; s; econs; eauto.
Case "undef".
  inv H0; symmetry_ctx; eauto using cgv2gv_refl, gv_inject_gundef.
Case "null".
  inv Hgv; inv Hwf; econs; eauto.
Case "array".
  i; revert l0 IH gv Hgv; induction l0.
  - i; inv Hgv; eauto using uninits_refl.
  - i; inv IH; unfold const2GV in Hgv; s in Hgv; inv_mbind.
    destruct typ_dec; subst; [|done].
    inv_mbind; inv H0.
    eapply cgv2gv_refl; eauto.
    eapply gv_inject_app.
    + eapply cgv2gv_refl_rev; eauto.
      eapply H1; unfold const2GV; rewrite <- HeqR0; eauto.
    + eapply gv_inject_app; eauto using uninits_refl.
      specialize (IHl0 H2).
      unfold const2GV in IHl0; s in IHl0.         
      rewrite <- HeqR in IHl0.
      destruct l0; [by inv HeqR; eauto|].
      s in IHl0; eapply cgv2gv_refl_rev; eauto.
Case "struct".
  inv H0; eapply cgv2gv_refl; eauto.
  destruct typ_eq_list_typ; [|by inv H1].
  destruct g; inv H1; eauto using uninits_refl.
  revert HeqR0; generalize (p::g) as gg; clear p g; i.
  eauto using const2GV_list_refl.
Case "gid".
  inv H0; eapply cgv2gv_refl; eauto.
  symmetry_ctx; eauto using global_gv_inject_refl.
Case "trunc_int".
  inv H0; eapply cgv2gv_refl; eauto.
  symmetry_ctx; eapply simulation__mtrunc_refl, HeqR.
  unfold const2GV in IHc; rewrite HeqR0 in IHc.
  eauto using cgv2gv_refl_rev.
Case "mext".
  inv H0; eapply cgv2gv_refl; eauto.
  symmetry_ctx; eapply simulation__mext_refl, HeqR.
  unfold const2GV in IHc; rewrite HeqR0 in IHc.
  eauto using cgv2gv_refl_rev.
Case "mcast".
  inv H0; eapply cgv2gv_refl; eauto.
  symmetry_ctx; eapply simulation__mcast_refl, HeqR.
  unfold const2GV in IHc; rewrite HeqR0 in IHc.
  eauto using cgv2gv_refl_rev.
Case "gep".
  apply symmetry in H1; inv H0; eapply cgv2gv_refl; eauto.
  destruct t; tinv H1.
  remember (getConstGEPTyp l0 (typ_pointer t)) as R2.
  destruct R2; tinv H1.
  remember (GV2ptr TD (getPointerSize TD) g) as R3.
  destruct R3; tinv H1.
    remember (intConsts2Nats TD l0) as R4.
    destruct R4; tinv H1.
      remember (mgep TD t v l1) as R5.
      destruct R5; inv H1.
        symmetry_ctx; unfold const2GV in IHc; rewrite HeqR0 in IHc.
        eapply simulation__mgep_refl with (mi:=mi) in HeqR5 
        ; eauto using GV2ptr_refl, cgv2gv_refl_rev.
        unfold ptr2GV, val2GV. simpl. auto.

        inv_mbind. symmetry_ctx. 
        eauto using gv_inject_gundef.
      inv_mbind. symmetry_ctx. 
      eauto using gv_inject_gundef.
    inv_mbind. symmetry_ctx.
    eauto using gv_inject_gundef.
Case "select".
  inv H0; unfold const2GV in IHc2, IHc3; destruct p0, p1.
  rewrite <- HeqR in IHc2; rewrite <- HeqR1 in IHc3.
  destruct isGVZero; inv H1; eauto.
Case "icmp".
  inv H0; eapply cgv2gv_refl; eauto.
  unfold const2GV in IHc1, IHc2.
  rewrite <- HeqR0 in IHc1; rewrite <- HeqR in IHc2.
  apply symmetry in HeqR1.
  eapply simulation__micmp_refl, HeqR1; eauto using cgv2gv_refl_rev.
Case "fcmp".
  inv H0; eapply cgv2gv_refl; eauto.
  destruct t; try by inv H1.
  inv_mbind; unfold const2GV in IHc1, IHc2.
  rewrite <- HeqR0 in IHc1; rewrite <- HeqR in IHc2.
  apply symmetry in HeqR1.
  eapply simulation__mfcmp_refl, HeqR1; eauto using cgv2gv_refl_rev.

Case "extractvalue".
  inv H0; eapply cgv2gv_refl; eauto. 
  unfold const2GV in IHc; rewrite <-HeqR0 in IHc.
  specialize (IHc _ eq_refl); eapply cgv2gv_refl_rev in IHc; eauto.
  eapply simulation__extractGenericValue_refl; eauto.  

Case "insertvalue".
  inv H0; eapply cgv2gv_refl; eauto. 
  unfold const2GV in IHc1, IHc2; rewrite <-HeqR0 in IHc1; rewrite <-HeqR in IHc2.
  specialize (IHc1 _ eq_refl); eapply cgv2gv_refl_rev in IHc1; eauto.
  specialize (IHc2 _ eq_refl); eapply cgv2gv_refl_rev in IHc2; eauto.
  symmetry_ctx; eapply simulation__insertGenericValue_refl in HeqR1; eauto.

Case "bop".
  inv H0; eapply cgv2gv_refl; eauto. 
  destruct t; try by inv H1.
  inv_mbind.
  unfold const2GV in IHc1, IHc2; rewrite <-HeqR0 in IHc1; rewrite <-HeqR in IHc2.
  specialize (IHc1 _ eq_refl); eapply cgv2gv_refl_rev in IHc1; eauto.
  specialize (IHc2 _ eq_refl); eapply cgv2gv_refl_rev in IHc2; eauto.
  symmetry_ctx; eapply simulation__mbop_refl in HeqR1; eauto.

Case "fbop".
  inv H0; eapply cgv2gv_refl; eauto. 
  destruct t; try by inv H1.
  inv_mbind.
  unfold const2GV in IHc1, IHc2; rewrite <-HeqR0 in IHc1; rewrite <-HeqR in IHc2.
  specialize (IHc1 _ eq_refl); eapply cgv2gv_refl_rev in IHc1; eauto.
  specialize (IHc2 _ eq_refl); eapply cgv2gv_refl_rev in IHc2; eauto.
  symmetry_ctx; eapply simulation__mfbop_refl in HeqR1; eauto.
Qed.

End LLVMtyping_rules.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
