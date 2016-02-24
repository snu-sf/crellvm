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
