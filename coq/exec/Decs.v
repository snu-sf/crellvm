Require Import syntax.
Require Import alist.

Require Import infrastructure.

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
