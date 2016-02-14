Require Import vellvm.
Require Import decs.
Require Import basic_const_inject.
Require Import sflib.

Fixpoint my_const_dec (c1 c2:const) : bool :=
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
          | cons hd1 tl1, cons hd2 tl2 => my_const_dec hd1 hd2 && f tl1 tl2
          | nil, nil => true
          | _, _ => false
        end) lc1 lc2
    | const_gid t1 x1,
      const_gid t2 x2 => typ_dec t1 t2 && id_dec x1 x2
    | const_truncop top1 cc1 t1,
      const_truncop top2 cc2 t2 => truncop_dec top1 top2 && my_const_dec cc1 cc2 && typ_dec t1 t2
    | const_extop eop1 cc1 t1,
      const_extop eop2 cc2 t2 => extop_dec eop1 eop2 && my_const_dec cc1 cc2 && typ_dec t1 t2
    | const_castop cop1 cc1 t1,
      const_castop cop2 cc2 t2 => castop_dec cop1 cop2 && my_const_dec cc1 cc2 && typ_dec t1 t2
    | const_gep ib1 cc1 lc1, 
      const_gep ib2 cc2 lc2 => inbounds_dec ib1 ib2 && my_const_dec cc1 cc2 &&      
      (fix f (lc1 lc2: list const) :=
        match lc1, lc2 with
          | cons hd1 tl1, cons hd2 tl2 => my_const_dec hd1 hd2 && f tl1 tl2
          | nil, nil => true
          | _, _ => false
        end) lc1 lc2
    | const_select cc1 cd1 ce1,
      const_select cc2 cd2 ce2 => my_const_dec cc1 cc2 && my_const_dec cd1 cd2 && my_const_dec ce1 ce2
    | const_icmp cd1 ce1 cf1,
      const_icmp cd2 ce2 cf2 => cond_dec cd1 cd2 && my_const_dec ce1 ce2 && my_const_dec cf1 cf2
    | const_fcmp cd1 ce1 cf1,
      const_fcmp cd2 ce2 cf2 => fcond_dec cd1 cd2 && my_const_dec ce1 ce2 && my_const_dec cf1 cf2
    | const_extractvalue cc1 lc1,
      const_extractvalue cc2 lc2 => my_const_dec cc1 cc2 && 
      (fix f (lc1 lc2: list const) :=
        match lc1, lc2 with
          | cons hd1 tl1, cons hd2 tl2 => my_const_dec hd1 hd2 && f tl1 tl2
          | nil, nil => true
          | _, _ => false
        end) lc1 lc2
    | const_insertvalue cc1 cd1 lc1,
      const_insertvalue cc2 cd2 lc2 => my_const_dec cc1 cc2 && my_const_dec cd1 cd2 && 
      (fix f (lc1 lc2: list const) :=
        match lc1, lc2 with
          | cons hd1 tl1, cons hd2 tl2 => my_const_dec hd1 hd2 && f tl1 tl2
          | nil, nil => true
          | _, _ => false
        end) lc1 lc2
    | const_bop b1 cc1 cd1,
      const_bop b2 cc2 cd2 => bop_dec b1 b2 && my_const_dec cc1 cc2 && my_const_dec cd1 cd2
    | const_fbop b1 cc1 cd1,
      const_fbop b2 cc2 cd2 => fbop_dec b1 b2 && my_const_dec cc1 cc2 && my_const_dec cd1 cd2
    | _,_ => false
  end.

Definition my_gvar_dec (g1 g2:gvar) : bool :=
  match g1,g2 with
    | gvar_intro x1 lk1 gs1 t1 c1 a1,
      gvar_intro x2 lk2 gs2 t2 c2 a2 => id_dec x1 x2 && linkage_dec lk1 lk2 && gvar_spec_dec gs1 gs2 && typ_dec t1 t2 && my_const_dec c1 c2 && align_dec a1 a2
    | gvar_external x1 gs1 t1,
      gvar_external x2 gs2 t2 => id_dec x1 x2 && gvar_spec_dec gs1 gs2 && typ_dec t1 t2 
    | _,_ => false
  end.

Ltac dest_hy :=
match goal with
| H : proj_sumbool ?x = true |- _ => destruct x; [subst|done]
| H : proj_sumbool ?x && _ = true |- _ => destruct x; [subst; simpl in H|done]
| H : proj_sumbool ?x && _ && _ = true |- _ => destruct x; [subst; simpl in H|done]
| H : proj_sumbool ?x && _ && _ && _ = true |- _ => destruct x; [subst; simpl in H|done]
| H : proj_sumbool ?x && _ && _ && _ && _ = true |- _ => destruct x; [subst; simpl in H|done]
| H : proj_sumbool ?x && _ && _ && _ && _ && _ = true |- _ => destruct x; [subst; simpl in H|done]
end.

Lemma my_const_dec_spec : forall (c1 c2:const), my_const_dec c1 c2 = true -> c1 = c2.
Proof.
induction c1 using LLVMtyping_rules.const_ind_gen; destruct c2; try done;
  unfold my_const_dec; fold my_const_dec; intros.

- repeat (dest_hy; try reflexivity).
- repeat (dest_hy; try reflexivity).
- repeat (dest_hy; try reflexivity).
- repeat (dest_hy; try reflexivity).
- repeat (dest_hy; try reflexivity).
- repeat (dest_hy; try reflexivity).
  generalize dependent H.
  generalize dependent l1.
  generalize dependent IH.
  induction l0; intros IHH [|l00 l01]; try done.
  intro HH. apply andb_true_iff in HH. destruct HH.
  inv IHH. exploit H3; eauto. intro HH. subst.
  exploit IHl0; eauto. intro HH. inversion HH; done.
- repeat (dest_hy; try reflexivity).
  generalize dependent H.
  generalize dependent l1.
  generalize dependent IH.
  induction l0; intros IHH [|l00 l01]; try done.
  intro HH. apply andb_true_iff in HH. destruct HH.
  inv IHH. exploit H3; eauto. intro HH. subst.
  exploit IHl0; eauto. intro HH. inversion HH; done.
- repeat (dest_hy; try reflexivity).
- repeat (dest_hy; try reflexivity).
  apply andb_true_iff in H; destruct H as [H1 H2]; apply IHc1 in H1; subst.
  repeat (dest_hy; try reflexivity).
- repeat (dest_hy; try reflexivity).
  apply andb_true_iff in H; destruct H as [H1 H2]; apply IHc1 in H1; subst.
  repeat (dest_hy; try reflexivity).
- repeat (dest_hy; try reflexivity).
  apply andb_true_iff in H; destruct H as [H1 H2]; apply IHc1 in H1; subst.
  repeat (dest_hy; try reflexivity).
- dest_hy;
  apply andb_true_iff in H; destruct H as [H1 H2]; apply IHc1 in H1; subst.
  generalize dependent H2.
  generalize dependent l1.
  generalize dependent IH.
  induction l0; intros IHH [|l00 l01]; try done.
  intro HH. apply andb_true_iff in HH. destruct HH.
  inv IHH. exploit H3; eauto. intro HH. subst.
  exploit IHl0; eauto. intro HH. inversion HH; done.
- apply andb_true_iff in H; destruct H as [H1 H2];
  apply andb_true_iff in H1; destruct H1 as [H11 H12]. 
  apply IHc1_1 in H11; apply IHc1_2 in H12; apply IHc1_3 in H2; subst; done.
- repeat (dest_hy; try reflexivity).
  apply andb_true_iff in H; destruct H as [H1 H2].
  apply IHc1_1 in H1; apply IHc1_2 in H2; subst; done.
- repeat (dest_hy; try reflexivity).
  apply andb_true_iff in H; destruct H as [H1 H2].
  apply IHc1_1 in H1; apply IHc1_2 in H2; subst; done.
- apply andb_true_iff in H; destruct H as [H1 H2]; apply IHc1 in H1; subst.
  generalize dependent H2.
  generalize dependent l1.
  generalize dependent IH.
  induction l0; intros IHH [|l00 l01]; try done.
  intro HH. apply andb_true_iff in HH. destruct HH.
  inv IHH. exploit H3; eauto. intro HH. subst.
  exploit IHl0; eauto. intro HH. inversion HH; done.
- apply andb_true_iff in H; destruct H as [H1 H2]. 
  apply andb_true_iff in H1; destruct H1 as [H11 H12]. 
  apply IHc1_1 in H11; apply IHc1_2 in H12; subst.
  generalize dependent H2.
  generalize dependent l1.
  generalize dependent IH.
  induction l0; intros IHH [|l00 l01]; try done.
  intro HH. apply andb_true_iff in HH. destruct HH.
  inv IHH. exploit H3; eauto. intro HH. subst.
  exploit IHl0; eauto. intro HH. inversion HH; done.
- repeat (dest_hy; try reflexivity).
  apply andb_true_iff in H; destruct H as [H1 H2]. 
  apply IHc1_1 in H1; apply IHc1_2 in H2; subst; done.
- repeat (dest_hy; try reflexivity).
  apply andb_true_iff in H; destruct H as [H1 H2]. 
  apply IHc1_1 in H1; apply IHc1_2 in H2; subst; done.
Qed.

Lemma my_gvar_dec_spec : forall (g1 g2:gvar), my_gvar_dec g1 g2 = true -> g1 = g2.
Proof.
destruct g1; destruct g2; try done.
  
Case "gvar_intro".
intros; unfold my_gvar_dec in H. repeat dest_hy.
apply andb_true_iff in H; destruct H as [H1 H2].
apply my_const_dec_spec in H1; subst.
dest_hy; reflexivity.

Case "gvar_external".
intros; unfold my_gvar_dec in H. 
repeat (dest_hy; try reflexivity).
Qed.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
