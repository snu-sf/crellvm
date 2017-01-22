Require Import vellvm.
Require Import sflib.
Require Import memory_props.
Require Import TODO.
Import Opsem.

Set Implicit Arguments.

(* Motivation: I want to distinguish excused ad-mits from normal ad-mits, *)
(* and further, I do not want to "grep" excused ones, so I give them different name. *)
(* @jeehoonkang adviced me to use semantic ad-mit instead of just comment. *)
(* Tactic Notation "EXCUSED_ADMIT" string(excuse) := idtac excuse; ad-mit. *)
(* above definition requires "Adm-itted" at the end of the proof, and I consider that not good *)
Definition EXCUSED_ADMIT (excuse: String.string) {T: Type} : T.  Admitted.

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
  exact (EXCUSED_ADMIT "
Language/Memory model should provide this.
This lemma was originally in Vellvm (Compcert memory model).
However, when we upgraded Vellvm's Compcert memory model to version 2, this lemma was commented.
See common/Memdata.v, ""encode_decode_encode_val__eq__encode_val"" is commented
and all tainted Theorems are commented.
It seems those Theorems are commented at that moment because they are not used in Vellvm.
One may able to track this issue with git lg/blame, also with actual compcert code before/after upgrade.
I consider this ad-mit can be solved, but it does not worth to.
").
  (* eapply MemProps.mstore_mload_same; eauto. *) (* From Vellvm, should uncomment *)
  (* eapply mstore_implies_gv_chunks_match; eauto. *)
Qed.

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
  remember (Int.unsigned 31 ofs) as Z_ofs eqn:DEF_Z_ofs.
  destruct ofs.
  rewrite Z.add_0_r.
  symmetry.
  rewrite -> DEF_Z_ofs.
  apply Int.repr_unsigned.
Qed.

Lemma wf_globals_const2GV
      gmax gl TD cnst gv
      (GLOBALS: genericvalues_inject.wf_globals gmax gl)
      (C2G: const2GV TD gl cnst = Some gv)
  :
    <<VALID_PTR: MemProps.valid_ptrs (gmax + 1)%positive gv>>
.
Proof.
  (* globals: <= gmax *)
  (* valid_ptr: < gmax+1 *)
  exact (EXCUSED_ADMIT "
Language should provide this. This should be provable.
- Inside _const2GV, it seems the only source of pointer is ""gid"", which looks up globals table.
- Note that int2ptr/ptr2int is currently defind as undef in mcast.
- null has pointer type but its value is int.
Therefore, any pointer returned by const2GV may originate from globals table, so this theorem should hold.

Also, even in case this does not hold, look: https://github.com/snu-sf/llvmberry/blob/c6acd1462bdb06c563185e23756897914f80e53a/coq/proof/SoundForgetMemory.v#L1504
This is provable with wf_const, by the lemma ""MemProps.const2GV_valid_ptrs"".
Claiming all const satisfies wf_const is too strong and it will introduce inconsistency.
We might need to add some constraints in our validator,
such as, the const of interest (all that appears in hint/invariant) actually exists in the original code,
which passed type checking, so wf_const holds.
").
Qed.

Lemma mstore_aux_never_produce_new_ptr
      TD mem0 mem1
      nptr ch val b o
      (MEM_NOALIAS: forall ptr ty a gv,
          mload TD mem0 ptr ty a = Some gv ->
          MemProps.no_alias nptr gv)
      (STORE_AUX: mstore_aux mem0 ch val b o = Some mem1)
      (NOALIAS: MemProps.no_alias nptr val)
  : forall ptr ty a gv,
    mload TD mem1 ptr ty a = Some gv ->
    MemProps.no_alias nptr gv
.
Proof.
  exact (EXCUSED_ADMIT "
Memory model should provide this.
- [nptr] is a pointer.
- [mem0] contains no pointers aliased with [nptr].
- [val] is also not aliased with [nptr].
- Then, only storing [val] into somewhere in [mem0] shouldn't produce an
  alias to [nptr]
- Therefore, the result memory [mem1] contains no aliases to [nptr]
").
Qed.
