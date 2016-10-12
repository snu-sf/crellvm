Require Import vellvm.
Require Import sflib.
Require Import memory_props.
Require Import TODO.
Import Opsem.

Set Implicit Arguments.

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
  eapply MemProps.mstore_mload_same; eauto.
  eapply mstore_implies_gv_chunks_match; eauto.
Qed.
