Require Import vellvm.
Require Import sflib.
Require Import memory_props.
Require Import TODO.
Import Opsem.

Set Implicit Arguments.

(* Motivation: I want to distinguish excused ad-mits from normal ad-mits, *)
(* and further, I do not want to "grep" excused ones, so I give them different name. *)
(* @jeehoonkang adviced me to use semantic ad-mit instead of just comment. *)
Tactic Notation "EXCUSED_ADMIT" string(excuse) := idtac excuse; admit.

(* Clarify purpose of this file more clearly? *)
(* Should prevent circular dependency *)

Lemma mstore_aux_implies_vm_matches
      Mem chunks gvs blck ofs Mem'
      (MSTORE: mstore_aux Mem chunks gvs blck ofs = Some Mem')
  :
      <<VM_MATCHES: Forall2 vm_matches_typ gvs chunks>>
.
Proof.
  red.
  generalize dependent gvs.
  revert_until chunks.
  revert Mem.
  induction chunks; ii; ss; des_ifs.
  econs; [|eapply IHchunks; eauto].
  unfold vm_matches_typ. ss.
  des_bool; des.
  apply memory_chunk_eq_prop in Heq. subst.
  split; [ss|apply has_chunk_eq_prop; apply Heq1].
Qed.

Lemma mstore_implies_gv_chunks_match
      TD Mem mpt t gvs algn Mem'
      (MSTORE: mstore TD Mem mpt t gvs algn = Some Mem')
  :
    <<CHUNKS_MATCH: gv_chunks_match_typ TD gvs t>>
.
Proof.
  red.
  unfold mstore in *.
  des_ifs.
  unfold gv_chunks_match_typ.
  rewrite Heq0.
  eapply mstore_aux_implies_vm_matches; eauto.
Qed.

Lemma mstore_mload_same
      td Mem mp2 typ1 gv1 align1 Mem'
      (MSTORE: mstore td Mem mp2 typ1 gv1 align1 = ret Mem')
  :
    <<MLOAD: mload td Mem' mp2 typ1 align1 = ret gv1>>
.
Proof.
  (* eapply MemProps.mstore_mload_same; eauto. *) (* From Vellvm, should uncomment *)
  (* eapply mstore_implies_gv_chunks_match; eauto. *)
Admitted.

Lemma filter_map_spec
      X Y
      a b (f:X -> option Y) l
      (IN: In a l)
      (APP: f a = Some b)
  : In b (filter_map f l).
Proof.
  induction l; ss.
  des.
  - subst. rewrite APP.
    econs. eauto.
  - des_ifs; eauto.
    constructor 2. eauto.
Qed.

Lemma filter_map_inv
      X Y
      b (f:X -> option Y) l
      (IN: In b (filter_map f l))
  : exists a, In a l /\ f a = Some b.
Proof.
  revert IN.
  induction l; ss.
  des_ifs; i.
  - ss. des.
    + subst. esplits; eauto.
    + apply IHl in IN. des.
      esplits; eauto.
  - apply IHl in IN. des.
    esplits; eauto.
Qed.

Lemma list_prj2_inv
      X Y (l:list (X * Y)) y
      (IN: In y (list_prj2 X Y l))
  : exists x, In (x, y) l.
Proof.
  induction l; ss; i.
  destruct a. ss. des.
  - subst. esplits; eauto.
  - apply IHl in IN. des.
    esplits; eauto.
Qed.

Lemma wf_globals_eq maxb gl
  :
    <<EQ: genericvalues_inject.wf_globals maxb gl <-> memory_props.MemProps.wf_globals maxb gl>>
.
Proof.
  split.
  - econs; eauto. apply Pos.le_1_l.
  - eapply memory_props.MemProps.redundant__wf_globals.
Qed.

Lemma int_add_0
      (ofs : int32)
  :
    <<INT_ARITH: Int.signed 31 ofs =
                 Int.signed 31 (Int.add 31 ofs (Int.repr 31 0))>>
.
Proof.
  unfold Int.add. ss.
  replace (Int.repr 31 (Int.unsigned 31 ofs + 0)) with ofs; ss.
  destruct ofs. unfold Int.repr. ss.
  rewrite Z.add_comm. ss.
  admit. (* Int.signed arithmetic *)
Admitted.
