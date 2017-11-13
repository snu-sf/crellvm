Require Import vellvm.
Require Import sflib.
Require Import memory_props.
Require Import TODO.
Import Opsem.
Require Import Classical.

Set Implicit Arguments.


Ltac des_outest_ifsG :=
  match goal with
  | |- context[ match ?x with _ => _ end ] =>
    match (type of x) with
    | { _ } + { _ } => destruct x; clarify
    | _ => let Heq := fresh "Heq" in destruct x as [] eqn: Heq; clarify
    end
  end
.

Ltac hide_goal :=
  match goal with
  | [ |- ?G ] => let name := fresh "HIDDEN_GOAL" in
                 set (name := G); replace G with name by reflexivity; move name at top
  end.

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

Ltac rpapply_raw H :=
  first[erewrite f_equal8 | erewrite f_equal7 | erewrite f_equal6 | erewrite f_equal5 |
        erewrite f_equal4 | erewrite f_equal3 | erewrite f_equal2 | erewrite f_equal];
  [eapply H|..]; try reflexivity.

Ltac is_applied_function TARGET :=
  match TARGET with
  | ?f ?x =>
    idtac
  | _ => fail
  end
.

Ltac has_inside_strict A B :=
  match A with
  | context[B] => tryif (check_equal A B) then fail else idtac
  | _ => fail
  end
.

Ltac is_inside_others_body TARGET :=
  tryif (repeat multimatch goal with
                | [ |- context[?f ?x] ] =>
                  (* idtac f; idtac x; *)
                  tryif (has_inside_strict x TARGET)
                  then fail 2
                  else fail
                end)
  then fail
  else idtac
.

Ltac on_leftest_function TAC :=
  (* repeat *)
  multimatch goal with
  | [ |- context[?f ?x] ] =>
    tryif (is_applied_function f)
    then fail
    else
      tryif (is_inside_others_body f)
      then fail
      else TAC f
  (* else TAC constr:(f) *)
  (* TODO: What is the difference? *)
  end
.
(* TODO: more cannonical way to get leftest function? *)
(* I tried match reverse but it was not good *)
(* TODO: I want to define "get_leftest_function" *)
(* TODO: try tactic notation ? *)

Ltac leftest_rpapply H :=
  on_leftest_function ltac:(fun f =>
     (idtac f; first
                 (* TODO: why rewrite "with" doesn't work? *)
                 [ erewrite (f_equal8 f)
                 | erewrite (f_equal7 f)
                 | erewrite (f_equal6 f)
                 | erewrite (f_equal5 f)
                 | erewrite (f_equal4 f)
                 | erewrite (f_equal3 f)
                 | erewrite (f_equal2 f)
                 | erewrite (f_equal  f) | fail]); [ eapply H | .. ]; try reflexivity)
.





Ltac is_type x :=
     match type of x with
     | Type => idtac
     | Set => idtac
     | Prop => idtac (* TODO: needed? *)
     | _ => fail
     end.

Ltac is_term_applied_function TARGET :=
  match TARGET with
  | ?f ?x =>
    tryif (is_type x) then fail else idtac
  | _ => fail
  end
.

Ltac on_leftest_function_with_type TAC :=
  (* repeat *)
  multimatch goal with
  | [ |- context[?f ?x] ] =>
    tryif (is_term_applied_function f)
    then fail
    else
      tryif (is_inside_others_body f)
      then fail
      else TAC f
  end
.

Ltac rpapply H :=
  on_leftest_function_with_type ltac:(fun f =>
     (idtac f; first
                 (* TODO: why rewrite "with" doesn't work? *)
                 [ erewrite (f_equal8 f)
                 | erewrite (f_equal7 f)
                 | erewrite (f_equal6 f)
                 | erewrite (f_equal5 f)
                 | erewrite (f_equal4 f)
                 | erewrite (f_equal3 f)
                 | erewrite (f_equal2 f)
                 | erewrite (f_equal  f) | fail]); [ eapply H | .. ]; try reflexivity)
.



Goal forall a b,
    let weird_func1 x y z w := (x + y + z + w) in
    let weird_func2 x y := (x * y) > 0 in
    (weird_func2 (weird_func1 1 1 1 1) (b+a)) ->
    (weird_func2 (weird_func1 1 1 1 1) (a+b))
.
Proof.
  i. subst weird_func1. subst weird_func2.
  abstr (fun x y : Z => x * y > 0) weird_func1.
  Fail rpapply_raw H.
  erewrite f_equal4. Undo 1. (* rpapply_raw tries in decreasing order. *)
  (* f_equal4 and then f_equal3 *)
  erewrite f_equal3. Undo 1. (* Anyhow, that doesn't matter now . . . *)
  on_leftest_function ltac:(fun x => idtac x).
  leftest_rpapply H. Undo 1.
  rpapply H. Undo 1.
  Undo 3.
  Fail erewrite (f_equal2 (fun x y : Z => x * y > 0)).
  Fail erewrite f_equal2 with (f:= (fun x y : Z => x * y > 0)).
  (* TODO: without "abstr", below two also fails... *)
  (* It seems some kind of Coqs default reduction mechanism is always on, even in rewriting *)
  (* It may make sense to assume, our proof status has already undergone that reduction. *)
  (* For example, simpl in * will do reduction here, more than needed *)
  simpl in *. Undo 1.
  (* If this becomes problem in actual proof, we may add "remember" & "subst" in rpapply *)
Abort.

Goal (Forall (fun x => x > 0)%nat [1 ; 2]%nat) ->
        (Forall (fun x => x+1 > 1)%nat [1+0 ; 0+2]%nat)
.
Proof.
  i.
  Fail leftest_rpapply.
  on_leftest_function ltac:(fun x => idtac x).
  Fail erewrite (f_equal3 Forall). (* dependent type *)
  rpapply_raw H. Undo 1.
  on_leftest_function_with_type ltac:(fun x => idtac x).
  rpapply H.
Abort.

Goal (Forall2 (fun x y => x+y > 0)%nat [1 ; 2]%nat [3 ; 4]%nat) ->
        (Forall2 (fun x y => x+y+1 > 1)%nat [1+0 ; 0+2]%nat [3 ; 4]%nat)
.
Proof.
  i.
  Fail leftest_rpapply.
  on_leftest_function ltac:(fun x => idtac x).
  Fail erewrite (f_equal3 Forall). (* dependent type *)
  rpapply_raw H. Undo 1.
  on_leftest_function_with_type ltac:(fun x => idtac x).
  (* not "Forall2" or "Forall2 (A:=nat)". it is fed with types at maximum *)
  rpapply H.
Abort.

(* Motivation: I want to distinguish excused ad-mits from normal ad-mits, *)
(* and further, I do not want to "grep" excused ones, so I give them different name. *)
(* Tactic Notation "AD-MIT" string(excuse) := idtac excuse; ad-mit. *)
(* above definition requires "Adm-itted" at the end of the proof, and I consider that not good *)
Definition ADMIT (excuse: String.string) {T: Type} : T.  Admitted.
Tactic Notation "ADMIT" constr(excuse) := idtac excuse; exact (ADMIT excuse).

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

(* TODO: can we do this with setoid? *)
Lemma InA_iff_In
      A
      (myeq: A -> A -> Prop)
      (MYEQ_EQ: forall x y, myeq x y <-> x = y)
  :
    forall x xs, InA myeq x xs <-> In x xs.
Proof.
  i.
  split; i.
  - ginduction xs; ii; ss.
    { inv H. }
    inv H; ss.
    + apply MYEQ_EQ in H1. subst. left; ss.
    + right. eauto.
  - ginduction xs; ii; ss.
    des; ss.
    + subst. econs; eauto.
      eapply MYEQ_EQ; eauto.
    + eapply InA_cons_tl; eauto.
Qed.
