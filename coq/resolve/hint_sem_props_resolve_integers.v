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

Axiom Int_sub_add_not:
  forall s x y, Int.sub s x y = Int.add s (Int.add s x (Int.not s y)) (Int.one s).

Axiom Int_not_neg:
  forall s x, Int.not s x = Int.add s (Int.neg s x) (Int.mone s).

Axiom Int_ltu_1:
  forall s, Int.ltu s (Int.repr s 1) (Int.iwordsize s).

Axiom Int_shl_add:
  forall s i, Int.shl s i (Int.repr s 1) = Int.add s i i.

Axiom Int_xor_add:
  forall s i,
    Int.xor s i (Int.repr s (INTEGER.to_Z (Zneg (basic_aux.power_sz s)))) = 
    Int.add s i (Int.repr s (INTEGER.to_Z (Zneg (basic_aux.power_sz s)))).

Axiom Int_neg_divs:
  forall s i, Int.neg s i = Int.divs s i (Int.mone s).

Axiom Int_mul_shl:
  forall s i1 i2, Int.shl s i1 i2 = Int.mul s (Int.shl s (Int.repr s 1) i2) i1.

Axiom Int_mods_neg:
  forall s i1 i2, Int.mods s i1 (Int.neg s i2) = Int.mods s i1 i2.

Axiom Int_divs_neg:
  forall s i1 i2, Int.divs s i1 (Int.neg s i2) = Int.neg s (Int.divs s i1 i2).

Axiom Int_shl_neg:
  forall s i1 i2, Int.shl s i1 i2 = Int.neg s (Int.shl s (Int.neg s i1) i2).

Axiom Int_divu_modu:
  forall s i1 i2, Int.divu s i1 i2 = Int.divu s (Int.sub s i1 (Int.modu s i1 i2)) i2.

Axiom Int_divs_mods:
  forall s i1 i2, Int.divs s i1 i2 = Int.divs s (Int.sub s i1 (Int.mods s i1 i2)) i2.

Lemma Int_zero s:
  (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z (INTEGER.of_Z (Size.to_Z s) 0 true))) = Int.zero (Size.to_nat s - 1).
Proof. done. Qed.

Lemma Int_one s :
  (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z (INTEGER.of_Z (Size.to_Z s) 1 true))) = Int.one (Size.to_nat s - 1).
Proof. done. Qed.

Lemma Int_mone s :
  (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z (INTEGER.of_Z (Size.to_Z s) (-1) true))) = Int.mone (Size.to_nat s - 1).
Proof. done. Qed.

Lemma Int_neg_eq s a b :
  a = Int.neg s b ->
  Int.neg s a = b.
Proof.
  intros.
  transitivity (Int.neg _ (Int.neg _ b)).
  - by rewrite H.
  - by rewrite Int.neg_involutive.
Qed.

Lemma Int_neg_one s :
  Int.neg (Size.to_nat s - 1) (Int.one (Size.to_nat s - 1)) = Int.mone (Size.to_nat s - 1).
Proof.
  unfold Int.neg, Int.one, Int.mone.
  f_equal; simpl.
  rewrite Zmod_small; [done|].
  unfold Int.modulus, Int.wordsize, Size.to_nat.
  induction (s - 1)%nat; [done|].
  inv IHn; constructor; [done|].
  by rewrite two_power_nat_S.
Qed.

Lemma Int_add_zero_r (wordsize_one : nat) (x : Int.int wordsize_one) :
  Int.add wordsize_one (Int.zero wordsize_one) x = x.
Proof.
  rewrite Int.add_commut.
  by apply Int.add_zero.
Qed.

Lemma Int_0_and_mul i0 i1:
  Int.and 0 i0 i1 = Int.mul 0 i0 i1.
Proof.
  destruct i0, i1.
  unfold Int.modulus, two_power_nat, shift_nat in intrange, intrange0; simpl in *.
  assert (intval = 0 \/ intval = 1); [omega|].
  assert (intval0 = 0 \/ intval0 = 1); [omega|].
  unfold Int.xor, Int.sub.
  unfold Int.bitwise_binop, xorb; simpl.
  destruct H; destruct H0; subst; simpl in *; try done.
Qed.

Lemma Int_0_xor_sub i0 i1:
  Int.xor 0 i0 i1 = Int.sub 0 i0 i1.
Proof.
  destruct i0, i1.
  unfold Int.modulus, two_power_nat, shift_nat in intrange, intrange0; simpl in *.
  assert (intval = 0 \/ intval = 1); [omega|].
  assert (intval0 = 0 \/ intval0 = 1); [omega|].
  unfold Int.xor, Int.sub.
  unfold Int.bitwise_binop, xorb; simpl.
  destruct H; destruct H0; subst; simpl in *; try done.
  apply Int.eqm_samerepr.
  unfold Int.eqm, Int.eqmod.
  by exists 1.
Qed.

Lemma Int_0_xor_add i0 i1:
  Int.xor 0 i0 i1 = Int.add 0 i0 i1.
Proof.
  destruct i0, i1.
  unfold Int.modulus, two_power_nat, shift_nat in intrange, intrange0; simpl in *.
  assert (intval = 0 \/ intval = 1); [omega|].
  assert (intval0 = 0 \/ intval0 = 1); [omega|].
  unfold Int.xor, Int.add.
  unfold Int.bitwise_binop, xorb; simpl.
  destruct H; destruct H0; subst; simpl in *; try done.
  apply Int.eqm_samerepr.
  unfold Int.eqm, Int.eqmod.
  by exists (-1).
Qed.  
