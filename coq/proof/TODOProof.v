Require Import vellvm.
Require Import sflib.
Require Import memory_props.
Require Import TODO.
Require Import Decs.
Import Opsem.

Set Implicit Arguments.

Ltac rewrite_everywhere H := rewrite H in *.
Ltac all_with_term TAC TERM :=
  repeat multimatch goal with
         | H: context[TERM] |- _ => TAC H
         end
.

Ltac clear_unused :=
  repeat multimatch goal with
         | [H: ?T |- _] =>
           match (type of T) with
           | Prop => idtac
           | _ => try clear H
           end
         end
.
Ltac clear_tautology :=
  repeat match goal with
         | [H: ?A = ?B, H2: ?B = ?A |- _] => clear H2
         | [H: True |- _] => clear H
         | [H: ?X, H2: ?X |- _] => clear H2
         | [H: ?A = ?A |- _] => clear H
         end
.
Ltac clear_tac := repeat (clear_unused; clear_tautology).

Ltac des_outest_ifs H :=
  match goal with
  | H': context[ match ?x with _ => _ end ] |- _ =>
    check_equal H' H;
    match (type of x) with
    | { _ } + { _ } => destruct x; clarify
    | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
    end
  end.

Ltac des_ifs_safe_aux TAC :=
  TAC;
  repeat
    multimatch goal with
    | |- context[match ?x with _ => _ end] =>
      match (type of x) with
      | { _ } + { _ } => destruct x; TAC; []
      | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; TAC; []
      end
    | H: context[ match ?x with _ => _ end ] |- _ =>
      match (type of x) with
      | { _ } + { _ } => destruct x; TAC; []
      | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; TAC; []
      end
    end.
Tactic Notation "des_ifs_safe" := des_ifs_safe_aux clarify.
Tactic Notation "des_ifs_safe" tactic(TAC) := des_ifs_safe_aux TAC.

Ltac abstr_aux x var_name :=
  let hyp_name := fresh "abstr_hyp_name" in
  remember x as var_name eqn:hyp_name; clear hyp_name
.

Tactic Notation "abstr" constr(H) := let var_name := fresh "abstr_var_name" in abstr_aux H var_name.
Tactic Notation "abstr" constr(H) ident(var_name) := abstr_aux H var_name.

Example abstr_demo: (1 + 2 = 3) -> False.
  i.
  abstr_aux (1 + 2) my_name. Undo 1.
  abstr (1 + 2).
Abort.

Ltac des_ifsH H :=
  clarify;
  repeat
    match goal with
    | H': context[ match ?x with _ => _ end ] |- _ =>
      check_equal H' H;
      match (type of x) with
      | { _ } + { _ } => destruct x; clarify
      | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
      end
    end.

Ltac des_ifsG :=
  clarify;
  repeat
    match goal with
    | |- context[match ?x with _ => _ end] =>
      match (type of x) with
      | { _ } + { _ } => destruct x; clarify
      | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
      end
    end.

Ltac expl_aux H TAC :=
  let n := fresh H in
  (* one goal or zero goal *)
  first[exploit H; TAC; []; repeat intro n; des|
        exploit H; TAC; fail]
.

Tactic Notation "expl" constr(H) := expl_aux H eauto.

Tactic Notation "expl" constr(H) tactic(TAC) := expl_aux H TAC.

(* multimatch is needed for "solve [all inv]" *)
Ltac all TAC :=
  repeat multimatch goal with
         | H: _ |- _ => TAC H
         end
.

Ltac apply_all x := all (ltac:(apply_in) x).

(* Motivation: I want to distinguish excused ad-mits from normal ad-mits, *)
(* and further, I do not want to "grep" excused ones, so I give them different name. *)
(* @jeehoonkang adviced me to use semantic ad-mit instead of just comment. *)
(* Tactic Notation "SF_AD-MIT" string(excuse) := idtac excuse; ad-mit. *)
(* above definition requires "Adm-itted" at the end of the proof, and I consider that not good *)
Definition SF_ADMIT (excuse: String.string) {T: Type} : T.  Admitted.

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
  exact (SF_ADMIT "
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

Fixpoint can_have_ptr c :=
  match c with
  | const_gep _ _ _ => true
  | const_zeroinitializer _ => true
  | const_arr _ cs => List.existsb can_have_ptr cs
  | const_struct _ cs => List.existsb can_have_ptr cs
  | const_gid _ _ => true
  | const_castop _ c _ => can_have_ptr c
  | const_select _ c2 c3 => can_have_ptr c2 || can_have_ptr c3
  | const_extractvalue c cs =>
    true (* can_have_ptr c || List.existsb can_have_ptr cs *)
  | const_insertvalue c1 c2 cs =>
    true (* can_have_ptr c || List.existsb can_have_ptr cs *)
  | _ => false
  end
.

Lemma gundef_not_ptr
      TD ty
      b ofs mc
      (GUNDEF: gundef TD ty = Some [(Values.Vptr b ofs, mc)])
  :
    False
.
Proof.
  unfold gundef in *. des_ifs.
  induction l0; ss.
Qed.

Lemma const_ptr
      TD gl c b ofs mc
      (PTR: const2GV TD gl c = Some [(Values.Vptr b ofs, mc)])
  :
    can_have_ptr c
.
Proof.
  move c at top.
  revert_until c.
  induction c using Decs.const_ind_gen; ii; ss;
    unfold const2GV in *; ss; des_ifs_safe; unfold cgv2gv in *; clarify.
  - des_ifs.
  - expl gundef_not_ptr. ss.
  -
    {
      move l0 at top.
      clear Heq1.
      revert_until l0.
      induction l0; ii; ss.
      des_ifs.
      assert(UN: uninits (s - sizeGenericValue g0) = []).
      { clear - H0.
        unfold uninits in *.
        destruct (s - sizeGenericValue g0)%nat; ss.
        exfalso.
        exploit f_equal; eauto.
        instantiate (1:= @length (Values.val * AST.memory_chunk)). ss.
        i.
        repeat rewrite app_length in *.
        destruct g0; ss; clarify.
        omega.
      }
      rewrite UN in *. clear UN. ss.
      destruct g0; ss.
      - clarify.
        exploit IHl0; eauto.
        { inv IH. ss. }
        i. rewrite x. apply orb_true_r.
      - destruct p; ss. clarify.
        destruct g0; ss. clarify.
        inv IH.
        exploit H1.
        { rewrite Heq1. ss. }
        i. rewrite x. apply orb_true_l.
    }
  -
    {
      move l0 at top.
      clear Heq1.
      revert_until l0.
      induction l0; ii; ss.
      des_ifs.
      assert(UN: uninits (s - sizeGenericValue g0) = []).
      { clear - H1.
        unfold uninits in *.
        destruct (s - sizeGenericValue g0)%nat; ss.
        exfalso.
        exploit f_equal; eauto.
        instantiate (1:= @length (Values.val * AST.memory_chunk)). ss.
        i.
        repeat rewrite app_length in *.
        destruct g0; ss; clarify.
        omega.
      }
      rewrite UN in *. clear UN. ss.
      destruct g0; ss.
      - clarify.
        exploit IHl0; eauto.
        { inv IH. ss. }
        i. rewrite x. apply orb_true_r.
      - destruct p; ss. clarify.
        destruct g0; ss. clarify.
        inv IH.
        exploit H1.
        { rewrite Heq1. ss. }
        i. rewrite x. apply orb_true_l.
    }
  - unfold mtrunc in *.
    unfold val2GV in *.
    des_ifs; try (expl gundef_not_ptr); ss.
  - unfold mext in *.
    unfold val2GV in *.
    des_ifs; try (expl gundef_not_ptr); ss.
  - unfold mcast in *.
    unfold mbitcast in *.
    des_ifs; try (expl gundef_not_ptr); ss;
      try (expl IHc; rewrite Heq0; ss).
  -
    des_ifs.
    + clear Heq1. clear Heq0.
      clear_tac.
      exploit IHc3; eauto.
      rewrite Heq2. ss.
      i.
      rewrite x.
      apply orb_true_r.
    + clear Heq2. clear Heq0.
      clear_tac.
      exploit IHc2; eauto.
      rewrite Heq1. ss.
      i.
      rewrite x.
      apply orb_true_l.
  - unfold micmp in *.
    unfold micmp_int in *.
    unfold Values.Val.cmp in *.
    unfold Values.Val.cmpu_int in *.
    unfold Values.Val.of_optbool in *.
    des_ifs; try (expl gundef_not_ptr); ss.
  - unfold mfcmp in *.
    unfold Values.Val.cmpf in *.
    des_ifs; try (expl gundef_not_ptr); ss.
  (* - *)
  (*   { *)
  (*     move l0 at top. *)
  (*     clear Heq1. clear_tac. *)
  (*     revert_until l0. *)
  (*     induction l0; ii; ss. *)
  (*     { inv IH. *)
  (*       cbn in Heq2. *)
  (*       des_ifs; try (expl gundef_not_ptr); ss. *)
  (*       exploit IHc. *)
  (*       rewrite Heq0. *)
  (*       { *)
  (*         clear IHc Heq0. clear_tac. *)
  (*         unfold mget in *. *)
  (*         unfold monad.mbind in *. des_ifs. *)
  (*         assert(g = [] /\ g1 = g0). *)
  (*         { clear - Heq1. clear_tac. *)
  (*           revert_until g0. *)
  (*           induction g0; ii; ss ;clarify. } *)
  (*         des; clarify. *)
  (*         hexploit splitGenericValue_spec; eauto; []; i; des. *)
  (*         admit. *)
  (*       } *)
  (*       i. rewrite x. apply orb_true_l. *)
  (*     } *)
  (*     { *)
  (*       admit. *)
  (*     } *)
  (*   } *)
  (* - unfold genericvalues.LLVMgv.insertGenericValue in *. *)
  (*   des_ifs; try (expl gundef_not_ptr); ss. *)
  (*   unfold mset in *. unfold monad.mbind in *. *)
  (*   des_ifs. *)
  (*   admit. *)
  - unfold mbop in *.
    unfold Values.Val.add in *.
    unfold Values.Val.sub in *.
    repeat (des_ifs; try (expl gundef_not_ptr); ss).
  - unfold mfbop in *.
    repeat (des_ifs; try (expl gundef_not_ptr); ss).
Qed.


Lemma wf_globals_const2GV
      gmax gl TD cnst gv
      (GLOBALS: genericvalues_inject.wf_globals gmax gl)
      (C2G: const2GV TD gl cnst = Some gv)
      (WF_CONST: exists system ty, wf_const system TD cnst ty)
  :
    <<VALID_PTR: MemProps.valid_ptrs (gmax + 1)%positive gv>>
.
Proof.
  des.
  hexploit MemProps.const2GV_valid_ptrs; eauto.
  { apply wf_globals_eq. ss. }
  (* globals: <= gmax *)
  (* valid_ptr: < gmax+1 *)
(*   exact (SF_ADMIT " *)
(* Language should provide this. This should be provable. *)
(* - Inside _const2GV, it seems the only source of pointer is ""gid"", which looks up globals table. *)
(* - Note that int2ptr/ptr2int is currently defind as undef in mcast. *)
(* - null has pointer type but its value is int. *)
(* Therefore, any pointer returned by const2GV may originate from globals table, so this theorem should hold. *)

(* Also, even in case this does not hold, look: https://github.com/snu-sf/llvmberry/blob/c6acd1462bdb06c563185e23756897914f80e53a/coq/proof/SoundForgetMemory.v#L1504 *)
(* This is provable with wf_const, by the lemma ""MemProps.const2GV_valid_ptrs"". *)
(* Claiming all const satisfies wf_const is too strong and it will introduce inconsistency. *)
(* We might need to add some constraints in our validator, *)
(* such as, the const of interest (all that appears in hint/invariant) actually exists in the original code, *)
(* which passed type checking, so wf_const holds. *)
(* "). *)
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
  exact (SF_ADMIT "
Memory model should provide this.
- [nptr] is a pointer.
- [mem0] contains no pointers aliased with [nptr].
- [val] is also not aliased with [nptr].
- Then, only storing [val] into somewhere in [mem0] shouldn't produce an
  alias to [nptr]
- Therefore, the result memory [mem1] contains no aliases to [nptr]
").
Qed.
