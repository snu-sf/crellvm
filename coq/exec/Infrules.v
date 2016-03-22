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

Require Import Decs.
Set Implicit Arguments.

(* Copied from validator/basic_aux.v because ocaml-extracted version of this code cannot find validator/basic_aux.v *)
Fixpoint power_sz (s:sz) : positive :=
  match s with
    | O => xH
    | S n => xO (power_sz n)
  end.

(* Copied from validator/basic_aux.v because ocaml-extracted version of this code cannot find validator/basic_aux.v *)
Definition signbit_of (s:sz) : option Int :=
  match s with 
    | O => None
    | S n => Some (Zneg (power_sz n))
  end.


Definition cond_plus (s:sz) (c1 c2 c3: INTEGER.t) : bool :=
  (Int.eq_dec _)
    (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c3))
    (Int.add (Size.to_nat s - 1)
             (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c1))
             (Int.repr (Size.to_nat s - 1) (INTEGER.to_Z c2))).

Definition cond_signbit (s:sz) (v:ValueT.t) : bool :=
  match signbit_of s, v with
  | None, _ => false
  | Some n, ValueT.const (const_int s' n') =>
    sz_dec s s' && INTEGER.dec n n'
  | _, _ => false
  end.

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
  | Infrule.add_shift y v s =>
    if $$ inv0 |- (Expr.value (ValueT.id y)) >=src (Expr.bop bop_add s v v) $$
    then {{inv0 +++ (Expr.value (ValueT.id y)) >=src (Expr.bop bop_shl s v (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 1%Z true))))}}
    else inv0
  | Infrule.add_signbit x e1 e2 s =>
    if $$ inv0 |- (Expr.value (ValueT.id x)) >=src (Expr.bop bop_add s e1 e2) $$ &&
       cond_signbit s e2
    then {{inv0 +++ (Expr.value (ValueT.id x)) >=src (Expr.bop bop_xor s e1 e2)}}
    else inv0
  | Infrule.sub_add z my x y s =>
    if $$ inv0 |- (Expr.value (ValueT.id my)) >=src (Expr.bop bop_sub s (ValueT.const (const_int s (INTEGER.of_Z (Size.to_Z s) 0%Z true))) (ValueT.id y)) $$ &&
       $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_sub s (ValueT.id x) (ValueT.id my)) $$
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_add s (ValueT.id x) (ValueT.id y))}}
    else inv0
  | Infrule.mul_bool z x y =>
    if $$ inv0 |- (Expr.value (ValueT.id z)) >=src (Expr.bop bop_mul Size.One (ValueT.id x) (ValueT.id y)) $$
    then {{inv0 +++ (Expr.value (ValueT.id z)) >=src (Expr.bop bop_and Size.One (ValueT.id x) (ValueT.id y)) }}
    else inv0
  | _ => inv0 (* TODO *)
  end.

(* TODO *)
Definition apply_infrules
           (infrules:list Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  fold_left (fun i r => apply_infrule r i) infrules inv0.
