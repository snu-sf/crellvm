Require Import syntax.
Require Import alist.

Require Import infrastructure.
Require Import vellvm.

Require Import sflib.
Require Export Coqlib.
Export LLVMsyntax.
Export LLVMinfra.

Ltac inv H := inversion H; subst; clear H.

(** * Utilities *)

Definition prod_dec:
  forall A (decA: forall x y: A, {x = y} + {~ x = y})
    B (decB: forall x y: B, {x = y} + {~ x = y})
    (x y: A * B),
    {x = y} + {~ x = y}.
Proof.
  intros.
  destruct x, y.
  destruct (decA a a0), (decB b b0).
  left; subst; auto.
  right; intro; apply n; inv H; auto.
  right; intro; apply n; inv H; auto.
  right; intro; apply n; inv H; auto.
Defined.

(** * Hint Database: EqDecDb *)

Create HintDb EqDecDb.

Ltac eqdec_tac := decide equality; auto with EqDecDb.

Hint Resolve INTEGER.dec: EqDecDb.
Hint Resolve id_dec: EqDecDb.
Hint Resolve typ_dec: EqDecDb.
Hint Resolve value_dec: EqDecDb.
Hint Resolve bop_dec: EqDecDb.
Hint Resolve fbop_dec: EqDecDb.
Hint Resolve list_const_dec: EqDecDb.
Hint Resolve floating_point_dec: EqDecDb.
Hint Resolve cmd_dec: EqDecDb.
Hint Resolve inbounds_dec: EqDecDb.
Hint Resolve truncop_dec: EqDecDb.
Hint Resolve extop_dec: EqDecDb.
Hint Resolve castop_dec: EqDecDb.
Hint Resolve cond_dec: EqDecDb.
Hint Resolve fcond_dec: EqDecDb.
Hint Resolve varg_dec: EqDecDb.

Lemma clattrs_dec : forall (c c0:clattrs), {c=c0}+{~c=c0}.
Proof.
  destruct c as [tailc5 callconv5 attributes1 attributes2];
  destruct c0 as [tailc0 callconv0 attributes0 attributes3];
  destruct_wrt_type3 tailc5 tailc0; subst; try solve [done_right];
  destruct_wrt_type3 callconv5 callconv0; subst; try solve [done_right];
  destruct_wrt_type3 attributes1 attributes0; subst; try solve [done_right];
  destruct_wrt_type3 attributes2 attributes3;
    subst; try solve [auto|done_right].
Defined.
Hint Resolve clattrs_dec: EqDecDb.

Definition align_dec : forall x y:align, {x = y} + {~ x = y} := Align.dec.
Hint Resolve align_dec: EqDecDb.

Definition sz_dec : forall x y:sz, {x = y} + {~ x = y} := Size.dec.
Hint Resolve sz_dec: EqDecDb.

(** * constant_dec *)

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

Fixpoint const_eqb (c1 c2:const) : bool :=
  match c1,c2 with
    | const_zeroinitializer t1, 
      const_zeroinitializer t2 => typ_dec t1 t2
    | const_int s1 i1,
      const_int s2 i2 => sz_dec s1 s2 && INTEGER.dec i1 i2
    | const_floatpoint fp1 f1,
      const_floatpoint fp2 f2 => floating_point_dec fp1 fp2 && FLOAT.dec f1 f2
    | const_undef t1, 
      const_undef t2
    | const_null t1,
      const_null t2 => typ_dec t1 t2
    | const_arr t1 lc1,
      const_arr t2 lc2
    | const_struct t1 lc1,
      const_struct t2 lc2 => typ_dec t1 t2 && 
      (fix f (lc1 lc2: list const) :=
        match lc1, lc2 with
          | cons hd1 tl1, cons hd2 tl2 => const_eqb hd1 hd2 && f tl1 tl2
          | nil, nil => true
          | _, _ => false
        end) lc1 lc2
    | const_gid t1 x1,
      const_gid t2 x2 => typ_dec t1 t2 && id_dec x1 x2
    | const_truncop top1 cc1 t1,
      const_truncop top2 cc2 t2 => truncop_dec top1 top2 && const_eqb cc1 cc2 && typ_dec t1 t2
    | const_extop eop1 cc1 t1,
      const_extop eop2 cc2 t2 => extop_dec eop1 eop2 && const_eqb cc1 cc2 && typ_dec t1 t2
    | const_castop cop1 cc1 t1,
      const_castop cop2 cc2 t2 => castop_dec cop1 cop2 && const_eqb cc1 cc2 && typ_dec t1 t2
    | const_gep ib1 cc1 lc1, 
      const_gep ib2 cc2 lc2 => inbounds_dec ib1 ib2 && const_eqb cc1 cc2 &&      
      (fix f (lc1 lc2: list const) :=
        match lc1, lc2 with
          | cons hd1 tl1, cons hd2 tl2 => const_eqb hd1 hd2 && f tl1 tl2
          | nil, nil => true
          | _, _ => false
        end) lc1 lc2
    | const_select cc1 cd1 ce1,
      const_select cc2 cd2 ce2 => const_eqb cc1 cc2 && const_eqb cd1 cd2 && const_eqb ce1 ce2
    | const_icmp cd1 ce1 cf1,
      const_icmp cd2 ce2 cf2 => cond_dec cd1 cd2 && const_eqb ce1 ce2 && const_eqb cf1 cf2
    | const_fcmp cd1 ce1 cf1,
      const_fcmp cd2 ce2 cf2 => fcond_dec cd1 cd2 && const_eqb ce1 ce2 && const_eqb cf1 cf2
    | const_extractvalue cc1 lc1,
      const_extractvalue cc2 lc2 => const_eqb cc1 cc2 && 
      (fix f (lc1 lc2: list const) :=
        match lc1, lc2 with
          | cons hd1 tl1, cons hd2 tl2 => const_eqb hd1 hd2 && f tl1 tl2
          | nil, nil => true
          | _, _ => false
        end) lc1 lc2
    | const_insertvalue cc1 cd1 lc1,
      const_insertvalue cc2 cd2 lc2 => const_eqb cc1 cc2 && const_eqb cd1 cd2 && 
      (fix f (lc1 lc2: list const) :=
        match lc1, lc2 with
          | cons hd1 tl1, cons hd2 tl2 => const_eqb hd1 hd2 && f tl1 tl2
          | nil, nil => true
          | _, _ => false
        end) lc1 lc2
    | const_bop b1 cc1 cd1,
      const_bop b2 cc2 cd2 => bop_dec b1 b2 && const_eqb cc1 cc2 && const_eqb cd1 cd2
    | const_fbop b1 cc1 cd1,
      const_fbop b2 cc2 cd2 => fbop_dec b1 b2 && const_eqb cc1 cc2 && const_eqb cd1 cd2
    | _,_ => false
  end.

Ltac eqbtac :=
  repeat
    (try match goal with
         | [H: andb ?a ?b = true |- _] => apply andb_true_iff in H; destruct H
         | [H: proj_sumbool (typ_dec ?a ?b) = true |- _] => destruct (typ_dec a b)
         | [H: proj_sumbool (sz_dec ?a ?b) = true |- _] => destruct (sz_dec a b)
         | [H: proj_sumbool (INTEGER.dec ?a ?b) = true |- _] => destruct (INTEGER.dec a b)
         | [H: proj_sumbool (floating_point_dec ?a ?b) = true |- _] => destruct (floating_point_dec a b)
         | [H: proj_sumbool (FLOAT.dec ?a ?b) = true |- _] => destruct (FLOAT.dec a b)
         | [H: proj_sumbool (id_dec ?a ?b) = true |- _] => destruct (id_dec a b)
         | [H: proj_sumbool (truncop_dec ?a ?b) = true |- _] => destruct (truncop_dec a b)
         | [H: proj_sumbool (inbounds_dec ?a ?b) = true |- _] => destruct (inbounds_dec a b)
         | [H: proj_sumbool (extop_dec ?a ?b) = true |- _] => destruct (extop_dec a b)
         | [H: proj_sumbool (castop_dec ?a ?b) = true |- _] => destruct (castop_dec a b)
         | [H: proj_sumbool (cond_dec ?a ?b) = true |- _] => destruct (cond_dec a b)
         | [H: proj_sumbool (fcond_dec ?a ?b) = true |- _] => destruct (fcond_dec a b)
         | [H: proj_sumbool (bop_dec ?a ?b) = true |- _] => destruct (bop_dec a b)
         | [H: proj_sumbool (fbop_dec ?a ?b) = true |- _] => destruct (fbop_dec a b)
         | [H: proj_sumbool (linkage_dec ?a ?b) = true |- _] => destruct (linkage_dec a b)
         | [H: proj_sumbool (gvar_spec_dec ?a ?b) = true |- _] => destruct (gvar_spec_dec a b)
         | [H: proj_sumbool (align_dec ?a ?b) = true |- _] => destruct (align_dec a b)
         | [H: proj_sumbool (fdec_dec ?a ?b) = true |- _] => destruct (fdec_dec a b)
         end;
     subst; ss;
     unfold sflib.is_true in *;
     unfold LLVMinfra.is_true in *).

Lemma const_eqb_spec c1 c2
      (EQB: const_eqb c1 c2):
  c1 = c2.
Proof.
  revert c2 EQB.
  induction c1 using const_ind_gen; destruct c2; ss;
    unfold const_eqb; fold const_eqb; i;
      repeat (eqbtac; try reflexivity);
      f_equal; eauto.
  - f_equal. revert l1 IH H0. induction l0; destruct l1; ss. i.
    inv IH. eqbtac. f_equal; eauto.
  - f_equal. revert l1 IH H0. induction l0; destruct l1; ss. i.
    inv IH. eqbtac. f_equal; eauto.
  - f_equal. revert l1 IH H0. induction l0; destruct l1; ss. i.
    inv IH. eqbtac. f_equal; eauto.
  - f_equal. revert l1 IH H0. induction l0; destruct l1; ss. i.
    inv IH. eqbtac. f_equal; eauto.
  - f_equal. revert l1 IH H0. induction l0; destruct l1; ss. i.
    inv IH. eqbtac. f_equal; eauto.
Qed.

Definition gvar_eqb (g1 g2:gvar) : bool :=
  match g1,g2 with
    | gvar_intro x1 lk1 gs1 t1 c1 a1,
      gvar_intro x2 lk2 gs2 t2 c2 a2 => id_dec x1 x2 && linkage_dec lk1 lk2 && gvar_spec_dec gs1 gs2 && typ_dec t1 t2 && const_eqb c1 c2 && align_dec a1 a2
    | gvar_external x1 gs1 t1,
      gvar_external x2 gs2 t2 => id_dec x1 x2 && gvar_spec_dec gs1 gs2 && typ_dec t1 t2 
    | _,_ => false
  end.

Lemma gvar_eqb_spec gvar1 gvar2
      (EQB: gvar_eqb gvar1 gvar2):
  gvar1 = gvar2.
Proof.
  destruct gvar1, gvar2; ss; eqbtac.
  apply const_eqb_spec in H1. subst. ss.
Qed.
