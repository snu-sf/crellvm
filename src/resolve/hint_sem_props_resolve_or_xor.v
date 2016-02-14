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
Require Import hint_sem_props_resolve_cond.

Lemma bitwise_binop_kk:
  forall n f g,
    (forall a b, f a b = f a (g a b)) ->
    forall x y,
      Int.bitwise_binop n f x y =
      Int.bitwise_binop n f x (Int.bitwise_binop n g x y).
Proof.
  unfold Int.bitwise_binop; intros. repeat rewrite Int.unsigned_repr.
  decEq; apply Int.Z_of_bits_exten; intros.
  repeat rewrite Zplus_0_r. repeat rewrite Int.bits_of_Z_of_bits; auto.
  by apply Int.Z_of_bits_range_2.
Qed.  

Lemma infrule_correct_or_xor:
  forall m1 m2 z y s a b, infrule_prop m1 m2 (rule_or_xor z y s a b).
Proof.
  repeat intro; infrule_tac.
  exists olc1; exists olc2; infrule_tac.
  intros lhs rhs Hmem; infrule_tac.
  destruct Hmem as [Heq|?]; [|by auto]; infrule_tac; arith_tac.
  econstructor; eauto; [|by apply eq_gvs_refl].
  inv Hrhs; inv Hrhs0; constructor.
  generalize dependent H5.
  generalize dependent H4.
  clear -Hlookup0.
  
  unfold BOPEXT; simpl.
  rewrite Hlookup0.
  destruct (getOperandValueExt (CurTargetData cfg1) a olc1 lc1 (Globals cfg1));
    destruct (getOperandValueExt (CurTargetData cfg1) b olc1 lc1 (Globals cfg1));
    infrule_tac; arith_tac.
  apply bitwise_binop_kk.
  by destruct a0, b0.
Qed.
Hint Resolve infrule_correct_or_xor: InfRuleDb.

(* 
*** Local Variables: ***
*** coq-prog-args: ("-emacs" "-impredicative-set") ***
*** End: ***
*)
