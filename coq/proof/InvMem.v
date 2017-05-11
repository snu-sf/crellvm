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
Require Import memory_props.
Import Opsem.

Require Import Exprs.
Require Import Hints.
Require Import GenericValues.

Set Implicit Arguments.

Definition gv_diffblock_with_blocks (conf: Config) gv blocks : Prop :=
  forall b
         (ING: In b (GV2blocks gv))
         (INB: In b blocks),
    False.
  (* ~exists b, In b (GV2blocks gv) /\ In b blocks. *)

Definition private_block m public b : Prop :=
  ~ public b /\ (b < m.(Mem.nextblock))%positive.

Module Unary.
  Structure t := mk {
    private_parent: list mblock;
    mem_parent: mem;

    unique_parent: list mblock;

    nextblock: Values.block
  }.

  (* TODO: not sure if MEM_PARENT is correct *)
  Inductive sem (conf:Config) (gmax:positive) (public:mblock -> Prop) (m:mem) (inv:t): Prop :=
  | sem_intro
      (GLOBALS: wf_globals gmax conf.(Globals))
      (WF: MemProps.wf_Mem gmax conf.(CurTargetData) m)
      (PRIVATE_PARENT:
         forall b (IN: In b inv.(private_parent)),
           private_block m public b)
      (MEM_PARENT:
         forall b (IN: In b inv.(private_parent))
           mc o,
           mload_aux inv.(mem_parent) mc b o =
           mload_aux m mc b o)

      (UNIQUE_PARENT_MEM:
         forall mptr typ align val'
           (LOAD: mload conf.(CurTargetData) m mptr typ align = Some val'),
           gv_diffblock_with_blocks conf val' inv.(unique_parent))
      (UNIQUE_PARENT_GLOBALS:
         forall b
           (IN_UNIQUE_PARENT: In b inv.(unique_parent)),
           (gmax < b)%positive)

      (UNIQUE_PRIVATE_PARENT: sublist inv.(unique_parent) inv.(private_parent))
      (NEXTBLOCK: m.(Mem.nextblock) = inv.(nextblock))
      (NEXTBLOCK_PARENT: (inv.(mem_parent).(Mem.nextblock) <= m.(Mem.nextblock))%positive)
      (* above is added for lift_unlift_le *)
  .

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (MEM_PARENT_EQ: lhs.(mem_parent) = rhs.(mem_parent))
      (PRIVATE_PARENT_EQ: lhs.(private_parent) = rhs.(private_parent))
      (UNIQUE_PARENT_EQ: lhs.(unique_parent) = rhs.(unique_parent))
      (MEM_PARENT:
         forall b (IN: In b lhs.(private_parent))
           mc o,
           mload_aux lhs.(mem_parent) mc b o =
           mload_aux rhs.(mem_parent) mc b o)
      (NEXTBLOCK_LE: (lhs.(nextblock) <= rhs.(nextblock))%positive)
  .

  Global Program Instance PreOrder_le: PreOrder le.
  Next Obligation. econs; ss. reflexivity. Qed.
  Next Obligation.
    ii. inv H. inv H0. econs.
    - etransitivity; eauto.
    - etransitivity; eauto.
    - etransitivity; eauto.
    - i. etransitivity.
      + eapply MEM_PARENT. eauto.
      + eapply MEM_PARENT0. rewrite <- PRIVATE_PARENT_EQ. ss.
    - etransitivity; eauto.
  Qed.

  Definition lift (m:mem) (uniqs:list mblock) (privs:list mblock) (inv:t): t :=
    mk (privs ++ inv.(private_parent)) m
       (filter (fun x => existsb (Values.eq_block x) uniqs) privs ++ inv.(unique_parent)) inv.(nextblock).

  Definition unlift (inv0 inv1:t): t :=
    mk inv0.(private_parent)
       inv0.(mem_parent)
       inv0.(unique_parent)
       inv1.(nextblock).
End Unary.

Module Rel.
  Structure t := mk {
    src: Unary.t;
    tgt: Unary.t;
    gmax: positive;
    inject: MoreMem.meminj;
  }.

  Definition public_src (inject:meminj) (b:mblock): Prop :=
    inject b <> None.

  Definition public_tgt (inject:meminj) (b:mblock): Prop :=
    exists b_src offset, inject b_src = Some (b, offset).

  Inductive sem (conf_src conf_tgt:Config) (mem_src mem_tgt:mem) (inv:t): Prop :=
  | sem_intro
      (SRC: Unary.sem conf_src inv.(gmax) (public_src inv.(inject)) mem_src inv.(src))
      (TGT: Unary.sem conf_tgt inv.(gmax) (public_tgt inv.(inject)) mem_tgt inv.(tgt))
      (INJECT: MoreMem.mem_inj inv.(inject) mem_src mem_tgt)
      (WF: genericvalues_inject.wf_sb_mi inv.(gmax) inv.(inject) mem_src mem_tgt)
      (FUNTABLE: ftable_simulation inv.(inject) conf_src.(FunTable) conf_tgt.(FunTable))
  .

  (* Inspired from Compcert's inject_separated *)
  (* maybe just get block number? not entire memory? *)
  Inductive frozen (f_old f_new: MoreMem.meminj) (m_src m_tgt: mem): Prop :=
    | frozen_intro
        (NEW_IMPLIES_OUTSIDE:
           forall b_src b_tgt delta
           (NEW: f_old b_src = None /\ f_new b_src = Some(b_tgt, delta)),
             <<OUTSIDE_SRC: ~Mem.valid_block m_src b_src>> /\ <<OUTSIDE_TGT: ~Mem.valid_block m_tgt b_tgt>>)
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
      (FROZEN: frozen lhs.(inject) rhs.(inject) lhs.(src).(Unary.mem_parent) lhs.(tgt).(Unary.mem_parent))
  .

  Global Program Instance PreOrder_le: PreOrder le.
  Next Obligation.
    econs; ss; try reflexivity.
    econs; eauto. ii. des. clarify.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs.
    - etransitivity; eauto.
    - etransitivity; eauto.
    - etransitivity; eauto.
    - eapply inject_incr_trans; eauto.
    -
      econs; eauto.
      ii. des.
      destruct (inject y b_src) eqn:T.
      + destruct p.
        inv FROZEN.
        hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
        split; ss.
        exploit INJECT0; eauto; []; i; des. clarify.
      + inv FROZEN0.
        hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
        inv SRC. inv TGT. rewrite MEM_PARENT_EQ. rewrite MEM_PARENT_EQ0.
        split; ss.
  Qed.

  Lemma frozen_preserves_src
        inv0 inv1
        (INJECT: inject_incr inv0.(inject) inv1.(inject))
        (FROZEN: frozen inv0.(inject) inv1.(inject) inv0.(src).(Unary.mem_parent) inv0.(tgt).(Unary.mem_parent))
        (* Above two can be driven from both "le inv0 inv1" && "le inv0 (unlift inv0 inv1)" *)
        (* in actual proof, the latter one is given as premise *)
        (* IDK if this is also true for former one *)
        (* Anyhow, I intentionally choose smaller premise that can serve for both cases *)
        b_src
        (INSIDE: Mem.valid_block inv0.(src).(Unary.mem_parent) b_src)
    :
      <<PRESERVED: inv0.(inject) b_src = inv1.(inject) b_src>>
  .
  Proof.
    inv FROZEN.
    destruct (inject inv0 b_src) eqn:T0; ss;
      destruct (inject inv1 b_src) eqn:T1; ss.
    - destruct p, p0; ss.
      exploit INJECT; eauto; []; i; des.
      clarify.
    - destruct p; ss.
      exploit INJECT; eauto; []; i; des.
      clarify.
    - destruct p; ss.
      exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
      exfalso.
      apply OUTSIDE_SRC. eauto.
  Qed.

  Lemma frozen_preserves_tgt
        inv0 inv1
        (INJECT: inject_incr inv0.(inject) inv1.(inject))
        (FROZEN: frozen inv0.(inject) inv1.(inject) inv0.(src).(Unary.mem_parent) inv0.(tgt).(Unary.mem_parent))
        b_tgt
        (INSIDE: Mem.valid_block inv0.(tgt).(Unary.mem_parent) b_tgt)
    :
      <<PRESERVED: forall b_src delta (NOW: inv1.(inject) b_src = Some (b_tgt, delta)),
        <<OLD: inv0.(inject) b_src = Some (b_tgt, delta)>> >>
  .
  Proof.
    inv FROZEN.
    ii.
    destruct (inject inv0 b_src) eqn:T; ss.
    - destruct p; ss.
      exploit INJECT; eauto; []; i; des.
      clarify.
    - exfalso.
      exploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des.
      apply OUTSIDE_TGT. eauto.
  Qed.

  Lemma frozen_shortened
        f_old f_new
        m_src0 m_tgt0
        (FROZEN: frozen f_old f_new m_src0 m_tgt0)
        m_src1 m_tgt1
        (SHORT_SRC: (m_src1.(Mem.nextblock) <= m_src0.(Mem.nextblock))%positive)
        (SHORT_TGT: (m_tgt1.(Mem.nextblock) <= m_tgt0.(Mem.nextblock))%positive)
    :
      <<FROZEN: frozen f_old f_new m_src1 m_tgt1>>
  .
  Proof.
    inv FROZEN.
    econs; eauto.
    ii. des.
    hexploit NEW_IMPLIES_OUTSIDE; eauto; []; i; des. clear NEW_IMPLIES_OUTSIDE.
    split; ss.
    - ii. apply OUTSIDE_SRC.
      eapply Pos.lt_le_trans; eauto.
    - ii. apply OUTSIDE_TGT.
      eapply Pos.lt_le_trans; eauto.
  Qed.

  Definition lift
             (m_src m_tgt:mem)
             (uniqs_src uniqs_tgt:list mblock)
             (privs_src privs_tgt:list mblock)
             (inv:t): t :=
    mk (Unary.lift m_src uniqs_src privs_src inv.(src))
       (Unary.lift m_tgt uniqs_tgt privs_tgt inv.(tgt))
       inv.(gmax)
       inv.(inject).

  (* TODO: le_public? *)
    Definition unlift (inv0 inv1:t): t :=
      mk
        (Unary.unlift inv0.(src) inv1.(src))
        (Unary.unlift inv0.(tgt) inv1.(tgt))
        inv0.(gmax) inv1.(inject).

End Rel.
