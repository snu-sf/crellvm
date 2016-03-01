Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.

Require Import Exprs.
Require Import Hints.
Require Import TODO.

Set Implicit Arguments.

(* TODO *)
Definition apply_infrule
           (infrule:Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  inv0.

(* TODO *)
Definition apply_infrules
           (infrules:list Infrule.t)
           (inv0:Invariant.t): Invariant.t :=
  fold_left (fun i r => apply_infrule r i) infrules inv0.

(* TODO *)
Definition infrule_sem (m1 m2:module) (inf: infrule_t) (h: insn_hint_t) : insn_hint_t :=
  match inf with

    | rule_add_associative x y z s c1 c2 c3 s =>
      if $$ h |- y =r1 (rhs_ext_bop bop_add s (value_ext_id x) (value_ext_const (const_int s c1))) $$ &&
         $$ h |- z =r1 (rhs_ext_bop bop_add s (value_ext_id y) (value_ext_const (const_int s c2))) $$ &&
         cond_plus s c1 c2 c3
      then {{h +++ z =r1 (rhs_ext_bop bop_add s (value_ext_id x) (value_ext_const (const_int s c3)))}}
      else h


