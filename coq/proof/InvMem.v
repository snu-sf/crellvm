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

Definition GLOBAL_MAX_TODO: Prop. Admitted.

(* For TODOs, see `coq/hint/hint_sem.v` *)
Module Unary.
  Structure t := mk {
    private: list mblock;
    private_parent: list mblock;
    mem_parent: mem;
  }.

  (* TODO: not sure if MEM_PARENT is correct *)
  Inductive sem (conf:Config) (shared:mblock -> Prop) (m:mem) (inv:t): Prop :=
  | sem_intro
      (PRIVATE: forall b (IN: In b inv.(private)), ~ shared b)
      (PRIVATE_PARENT: forall b (IN: In b inv.(private_parent)), ~ shared b)
      (MEM_PARENT: forall b (IN: In b inv.(private_parent)),
          forall chunk i,
            Mem.load chunk inv.(mem_parent) b i = Mem.load chunk m b i)
  .

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (PRIVATE_PARENT: lhs.(private_parent) = rhs.(private_parent))
      (MEM_PARENT: lhs.(mem_parent) = rhs.(mem_parent))
  .
End Unary.

Module Rel.
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
      (SRC: Unary.sem conf_src (shared_src inv) mem_src inv.(src))
      (TGT: Unary.sem conf_tgt (shared_tgt inv) mem_tgt inv.(tgt))
      (INJECT: Mem.inject inv.(inject) mem_src mem_tgt)
  .

  (* TODO: not sure if inject_incr is enough.
   * cf. https://github.com/snu-sf/llvmberry/blob/before_refact/coq/hint/hint_sem.v#L284
   *)
  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (SRC: Unary.le lhs.(src) rhs.(src))
      (TGT: Unary.le lhs.(tgt) rhs.(tgt))
      (INJECT: inject_incr lhs.(inject) rhs.(inject))
  .

  (* TODO: le_public? *)
End Rel.
