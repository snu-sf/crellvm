Require Import vellvm.
Require Import sflib.
Require Import memory_props.
Require Import TODO.
Import Opsem.
Require Import Classical.

Set Implicit Arguments.

(* TODO: Is it replacable by some lemma in stdlib? or tactic? *)
Lemma dependent_split
      (A B: Prop)
      (HYPA: A)
      (HYPB: <<HYPA: A>> -> B)
  :
    <<GOAL: A /\ B>>
.
Proof.
  split; ss.
  apply HYPB; ss.
Qed.

Lemma Pos_lt_le_irrefl
      a b
      (LE: (a <= b)%positive)
      (LT: (b < a)%positive)
  :
    False
.
Proof. eapply Pos.lt_irrefl. eapply Pos.lt_le_trans; eauto. Qed.

Lemma Forall_harder
      A
      (P Q: A -> Prop)
      l
      (FORALL: List.Forall P l)
      (HARDER: forall a, P a -> Q a)
  :
    <<FORALL: List.Forall Q l>>
.
Proof.
  ginduction l; ii; ss.
  inv FORALL. econs; eauto.
  eapply IHl; eauto.
Qed.

Ltac reductio_ad_absurdum :=
  match goal with
  | [ |- ?G ] => destruct (classic G) as [tmp | REDUCTIO_AD_ABSURDUM];
                 [assumption|exfalso]
  end
.

Ltac exists_prop PROP :=
  tryif
    (repeat multimatch goal with
            | [H: PROP |- _ ] => (* idtac "Found!"; idtac H; *) fail 2
            end)
  then fail
  else idtac
.

(* get equality's transitive closure *)
(* TODO: it checks equal to strictly; "(0, 1).fst != 0" here. *)
Ltac eq_closure_tac :=
  repeat
    (repeat multimatch goal with
            | [H1: ?A = ?B, H2: ?B = ?C |- _ ] =>
              (* idtac "------------------------"; *)
              (* idtac H1; idtac H2; *)
              tryif (check_equal A C)
              then (* idtac "FAILREFL1"; *) fail
              else
                tryif (exists_prop (A = C) + exists_prop (C = A))
                then (* idtac "FAILREFL2" *) idtac
                else
                  let name := fresh "EQ_CLOSURE_TAC" in
                  exploit eq_trans; [exact H1|exact H2|]; intro name
            | [H1: ?B = ?A, H2: ?B = ?C |- _ ] =>
              tryif (check_equal A C)
              then (* idtac "FAILREFL1"; *) fail
              else
                tryif (exists_prop (A = C) + exists_prop (C = A))
                then (* idtac "FAILREFL2" *) idtac
                else
                  let name := fresh "EQ_CLOSURE_TAC" in
                  exploit eq_trans; [exact (eq_sym H1)|exact H2|]; intro name
            end)
.

(* COPIED FROM https://www.cis.upenn.edu/~bcpierce/sf/current/LibTactics.html *)
(* TODO: is it OK? *)
(* TODO: move to proper position; I think sflib should be OK *)
(* TODO: also import some other good things, e.g. gens *)
Tactic Notation "clears" ident(X1) :=
  let rec doit _ :=
      match goal with
      | H:context[X1] |- _ => clear H; try (doit tt)
      | _ => clear X1
      end in doit tt.
Tactic Notation "clears" ident(X1) ident(X2) :=
  clears X1; clears X2.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) :=
  clears X1; clears X2; clears X3.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4) :=
  clears X1; clears X2; clears X3; clears X4.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
       ident(X5) :=
  clears X1; clears X2; clears X3; clears X4; clears X5.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
       ident(X5) ident(X6) :=
  clears X1; clears X2; clears X3; clears X4; clears X5; clears X6.
(* TODO: This should fail when ident appears in the goal! *)
(* It currently succeeds, only removing preemises *)

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

Lemma list_disjoint_cons_inv
      X (hd: X) tl xs
      (DISJOINT: list_disjoint (hd :: tl) xs)
  :
    <<DISJOINT: list_disjoint [hd] xs /\ list_disjoint tl xs>>
.
Proof.
  splits.
  - ii. clarify. ss. des; ss. clarify. expl DISJOINT. left. ss.
  - eapply list_disjoint_cons_left; eauto.
Qed.

Lemma f_equal6 (A1 A2 A3 A4 A5 A6 B: Type) (f: A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> B)
      (x1 y1: A1) (EQ1: x1 = y1)
      (x2 y2: A2) (EQ2: x2 = y2)
      (x3 y3: A3) (EQ3: x3 = y3)
      (x4 y4: A4) (EQ4: x4 = y4)
      (x5 y5: A5) (EQ5: x5 = y5)
      (x6 y6: A6) (EQ6: x6 = y6)
  :
    <<EQ: f x1 x2 x3 x4 x5 x6 = f y1 y2 y3 y4 y5 y6>>
.
Proof. subst. reflexivity. Qed.

Lemma f_equal7 (A1 A2 A3 A4 A5 A6 A7 B: Type) (f: A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> B)
      (x1 y1: A1) (EQ1: x1 = y1)
      (x2 y2: A2) (EQ2: x2 = y2)
      (x3 y3: A3) (EQ3: x3 = y3)
      (x4 y4: A4) (EQ4: x4 = y4)
      (x5 y5: A5) (EQ5: x5 = y5)
      (x6 y6: A6) (EQ6: x6 = y6)
      (x7 y7: A7) (EQ7: x7 = y7)
  :
    <<EQ: f x1 x2 x3 x4 x5 x6 x7 = f y1 y2 y3 y4 y5 y6 y7>>
.
Proof. subst. reflexivity. Qed.

Lemma f_equal8 (A1 A2 A3 A4 A5 A6 A7 A8 B: Type) (f: A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> B)
      (x1 y1: A1) (EQ1: x1 = y1)
      (x2 y2: A2) (EQ2: x2 = y2)
      (x3 y3: A3) (EQ3: x3 = y3)
      (x4 y4: A4) (EQ4: x4 = y4)
      (x5 y5: A5) (EQ5: x5 = y5)
      (x6 y6: A6) (EQ6: x6 = y6)
      (x7 y7: A7) (EQ7: x7 = y7)
      (x8 y8: A8) (EQ8: x8 = y8)
  :
    <<EQ: f x1 x2 x3 x4 x5 x6 x7 x8 = f y1 y2 y3 y4 y5 y6 y7 y8>>
.
Proof. subst. reflexivity. Qed.

Ltac rpapply H :=
  first[erewrite f_equal8 | erewrite f_equal7 | erewrite f_equal6 | erewrite f_equal5 |
        erewrite f_equal4 | erewrite f_equal3 | erewrite f_equal2 | erewrite f_equal];
  [exact H|..]; try reflexivity.


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
  exact (SF_ADMIT "
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
