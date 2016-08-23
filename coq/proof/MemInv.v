Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Import Opsem.

Require Import Exprs.
Require Import Hints.
Require Import GenericValues.

Set Implicit Arguments.

(* TODO: global, le_public *)

Module Unary.
  Structure t := mk {
    global: mblock;
    private: list mblock;
    private_parent: list mblock;
  }.

  Inductive sem (conf:Config) (shared:mblock -> Prop) (inv:t): Prop :=
  | sem_intro
      (GLOBAL: True)
      (PRIVATE: forall b (IN: In b inv.(private)), ~ shared b)
      (PRIVATE_PARENT: forall b (IN: In b inv.(private_parent)), ~ shared b)
  .

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (GLOBAL: lhs.(global) = rhs.(global))
      (PARENT: lhs.(private_parent) = rhs.(private_parent))
  .
End Unary.

Module Relational.
  Structure t := mk {
    src: Unary.t;
    tgt: Unary.t;
    inject: meminj;
  }.

  Definition shared_src (inv:t) (b:mblock): Prop :=
    inv.(inject) b <> None.

  Definition shared_tgt (inv:t) (b:mblock): Prop :=
    exists b_src offset, inv.(inject) b_src = Some (b, offset).

  Inductive sem (conf_src conf_tgt:Config) (mem_src mem_tgt:mem) (inv:t): Prop :=
  | sem_intro
      (SRC: Unary.sem conf_src (shared_src inv) inv.(src))
      (TGT: Unary.sem conf_tgt (shared_tgt inv) inv.(tgt))
      (INJECT: Mem.inject inv.(inject) mem_src mem_tgt)
  .

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (SRC: Unary.le lhs.(src) rhs.(src))
      (TGT: Unary.le lhs.(tgt) rhs.(tgt))
      (INJECT: inject_incr lhs.(inject) rhs.(inject))
  .
End Relational.
