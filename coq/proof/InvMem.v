Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import sflib.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import vellvm.
Require Import memory_sim.
Require Import genericvalues_inject.
Import Opsem.

Require Import Exprs.
Require Import Hints.
Require Import GenericValues.

Set Implicit Arguments.


Module Unary.
  Structure t := mk {
    private: list mblock;
    private_parent: list mblock;
    mem_parent: mem;
  }.

  (* TODO: not sure if MEM_PARENT is correct *)
  Inductive sem (conf:Config) (gmax:positive) (public:mblock -> Prop) (m:mem) (inv:t): Prop :=
  | sem_intro
      (GLOBALS: wf_globals gmax conf.(Globals))
      (PRIVATE: forall b (IN: In b inv.(private)), ~ public b /\ (b < m.(Mem.nextblock))%positive)
      (PRIVATE_PARENT: forall b (IN: In b inv.(private_parent)), ~ public b /\ (b < m.(Mem.nextblock))%positive)
      (DISJOINT: list_disjoint inv.(private) inv.(private_parent))
      (MEM_PARENT:
         forall b (IN: In b inv.(private_parent))
           mc o,
           mload_aux inv.(mem_parent) mc b o =
           mload_aux m mc b o)
  .

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (PRIVATE_PARENT: lhs.(private_parent) = rhs.(private_parent))
      (MEM_PARENT:
         forall b (IN: In b lhs.(private_parent))
           mc o,
           mload_aux lhs.(mem_parent) mc b o =
           mload_aux rhs.(mem_parent) mc b o)
  .

  Global Program Instance PreOrder_le: PreOrder le.
  Next Obligation. econs; ss. Qed.
  Next Obligation.
    ii. inv H. inv H0. econs.
    - etransitivity; eauto.
    - i. etransitivity.
      + eapply MEM_PARENT. eauto.
      + eapply MEM_PARENT0. rewrite <- PRIVATE_PARENT. ss.
  Qed.

  Definition lift (m:mem) (inv:t): t :=
    mk nil (inv.(private) ++ inv.(private_parent)) m.
End Unary.

Module Rel.
  Structure t := mk {
    src: Unary.t;
    tgt: Unary.t;
    gmax: positive;
    inject: MoreMem.meminj;
  }.

  Definition public_src (inv:t) (b:mblock): Prop :=
    inv.(inject) b <> None.

  Definition public_tgt (inv:t) (b:mblock): Prop :=
    exists b_src offset, inv.(inject) b_src = Some (b, offset).

  Inductive sem (conf_src conf_tgt:Config) (mem_src mem_tgt:mem) (inv:t): Prop :=
  | sem_intro
      (SRC: Unary.sem conf_src inv.(gmax) (public_src inv) mem_src inv.(src))
      (TGT: Unary.sem conf_tgt inv.(gmax) (public_tgt inv) mem_tgt inv.(tgt))
      (INJECT: MoreMem.mem_inj inv.(inject) mem_src mem_tgt)
      (WF: genericvalues_inject.wf_sb_mi inv.(gmax) inv.(inject) mem_src mem_tgt)
  .

  (* TODO: not sure if inject_incr is enough.
   * cf. https://github.com/snu-sf/llvmberry/blob/before_refact/coq/hint/hint_sem.v#L284
   *)
  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (SRC: Unary.le lhs.(src) rhs.(src))
      (TGT: Unary.le lhs.(tgt) rhs.(tgt))
      (GMAX: lhs.(gmax) = rhs.(gmax))
      (INJECT: inject_incr lhs.(inject) rhs.(inject))
  .

  Global Program Instance PreOrder_le: PreOrder le.
  Next Obligation. econs; ss. Qed.
  Next Obligation.
    ii. inv H. inv H0. econs.
    - etransitivity; eauto.
    - etransitivity; eauto.
    - etransitivity; eauto.
    - eapply inject_incr_trans; eauto.
  Qed.

  Definition lift (m_src m_tgt:mem) (inv:t): t :=
    mk (Unary.lift m_src inv.(src))
       (Unary.lift m_tgt inv.(tgt))
       inv.(gmax)
       inv.(inject).

  (* TODO: le_public? *)
End Rel.
