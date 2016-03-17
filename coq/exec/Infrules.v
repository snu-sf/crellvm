Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.

Require Import Integers.

Require Import Exprs.
Require Import Hints.
Require Import TODO.

Set Implicit Arguments.

Definition cond_plus (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec _)
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c3))
    (Int.add (Size.to_nat s - 1)
             (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c1))
             (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c2))).

Notation "$$ inv |- y >=src rhs $$" := (ExprPairSet.mem (y, rhs) inv.(Invariant.src).(Invariant.lessdef)) (at level 41).
Notation "$$ inv |- y >=tgt rhs $$" := (ExprPairSet.mem (y, rhs) inv.(Invariant.tgt).(Invariant.lessdef)) (at level 41).
Notation "{{ inv +++ y >=src rhs }}" := (Invariant.update_src (Invariant.update_lessdef (ExprPairSet.add (y, rhs))) inv) (at level 41).
Notation "{{ inv +++ y >=tgt rhs }}" := (Invariant.update_tgt (Invariant.update_lessdef (ExprPairSet.add (y, rhs))) inv) (at level 41).

(* TODO *)
Definition apply_infrule
           (infrule:Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  match infrule with
  | Infrule.add_associative x y z c1 c2 c3 s =>
    if $$ inv0 |- (Expr.value (ValueT.id y)) >=src (Expr.bop bop_add s (ValueT.id x) (ValueT.const (const_int s c1))) $$ &&
       $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s (ValueT.id y) (ValueT.const (const_int s c2))) $$ &&
       cond_plus s c1 c2 c3
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s (ValueT.id x) (ValueT.const (const_int s c3)))}}
    else inv0
  | Infrule.add_sub z minusy x y s =>
    if $$ inv0 |- (Expr.value (ValueT.id minusy)) >=src (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) y) $$ &&
       $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s x minusy) $$
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_sub s x y)}}
    else inv0
  | Infrule.add_commutative z x y s =>
    if $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s x y) $$
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s y x)}}
    else inv0
  | _ => inv0 (* TODO *)
  end.

(* TODO *)
Definition apply_infrules
           (infrules:list Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  fold_left (fun i r => apply_infrule r i) infrules inv0.
