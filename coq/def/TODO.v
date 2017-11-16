Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Require Import sflib.
Require Import String.
Require Import paco.
Import LLVMsyntax.
Import LLVMinfra.

Set Implicit Arguments.


Definition bool_of_option A (x:option A): bool :=
  match x with
  | Some _ => true
  | None => false
  end.
Coercion bool_of_option: option >-> bool.

Definition option_to_list A (oa:option A): list A :=
  match oa with
  | Some a => a::nil
  | None => nil
  end.
Coercion option_to_list: option >-> list.

Definition get_or_else A (x: option A) (default: A) :=
  match x with
    | None => default
    | Some _x => _x
  end.

Fixpoint list_forallb2 A B (P: A -> B -> bool) (la:list A) (lb:list B): bool :=
  match la, lb with
  | a::la, b::lb => P a b && list_forallb2 P la lb
  | nil, nil => true
  | _, _ => false
  end.

Fixpoint list_forallb3 A B C (P: A -> B -> C -> bool) (la:list A) (lb:list B) (lc:list C): bool :=
  match la, lb, lc with
  | a::la, b::lb, c::lc => P a b c && list_forallb3 P la lb lc
  | nil, nil, nil => true
  | _, _, _ => false
  end.

Definition forallb2AL A B (P: atom -> A -> B -> bool) (la:AssocList A) (lb:AssocList B): bool :=
  list_forallb2
    (fun ea eb => id_dec ea.(fst) eb.(fst) && P ea.(fst) ea.(snd) eb.(snd))
    la lb.

Definition is_empty A (l:list A) :=
  match l with nil => true | _ => false end.

Definition lift_option A B (pred:A -> B)
           (oa:option A): option B :=
  match oa with
  | Some a => Some (pred a)
  | None => None
  end.

Definition lift2_option
           A B (pred:A -> B -> Prop)
           (oa:option A) (ob:option B): Prop :=
  match oa, ob with
  | Some a, Some b => pred a b
  | None, None => True
  | _, _ => False
  end.

Fixpoint filter_map A B (pred:A -> option B) (l:list A): list B :=
  match l with
  | nil => nil
  | a::l =>
    match pred a with
    | Some b => b::(filter_map pred l)
    | None => filter_map pred l
    end
  end.

Fixpoint forallb_map A B (pred:A -> option B) (l:list A): option (list B) :=
  match l with
  | nil => Some nil
  | a::l =>
    match pred a, forallb_map pred l with
    | Some b, Some l => Some (b::l)
    | _, _ => None
    end
  end.

Fixpoint unique
         A (eq_dec: forall (a b:A), {a = b} + {a <> b})
         (l:list A): bool :=
  match l with
  | nil => true
  | a::l => negb (in_dec eq_dec a l) && unique eq_dec l
  end.

Definition mapAL := Metatheory.EnvImpl.map.

Definition mapiAL A B (f: atom -> A -> B) (l:AssocList A): AssocList B :=
  List.map
    (fun (p:atom * A) =>
       let (atom, a) := p in (atom, (f atom a)))
    l.

(* Find FIRST occurence of element satisfying f. *)
(* If there is not, return None *)
Fixpoint find_index (A:Type) (l:list A) (f:A -> bool):option nat :=
  match l with
  | nil => None
  | head :: tail =>
    if (f head) then Some 0%nat else option_map S (find_index tail f)
  end.

Lemma find_index_sound
      (A:Type) (l:list A) (f:A -> bool) (idx:nat)
      (FIND:find_index l f = Some idx):
  exists y, nth_error l idx = Some y /\
       f y = true.
Proof.
  revert idx FIND. induction l; intros; simpl in *.
  - inv FIND.
  - destruct (f a) eqn:FA.
    + inv FIND. exists a. split; auto.
    + destruct (find_index l0 f) eqn:FIND'; inv FIND.
      exploit IHl; eauto.
Qed.

Lemma find_index_complete
      (A:Type) (l:list A) (f:A -> bool)
      (idx:nat) (FIND:find_index l f = None):
  negb (existsb f l).
Proof.
  revert FIND. induction l; intros; simpl in *; auto.
  destruct (f a), (find_index l0 f);
    simpl in *; try congruence.
  auto.
Qed.

(* Insert element BEFORE index. If index is out of bound, it SILENTLY inserts at the last. *)
Definition insert_at (A:Type) (idx:nat) (x:A) (l:list A): list A :=
  (firstn idx l) ++ [x] ++ (skipn idx l).

(* Print sflib. There are several same definitions, __mark__, __guard__, etc.
I intentionally define this new definition, not to mess these other things *)
Definition __ao_mark__ A (a : A) : A := a.

Lemma _ao_mark {A} (a: A) : __ao_mark__ A.
Proof. ss. Qed.

Lemma _aa_unmark {A} (a: __ao_mark__ A) : A.
Proof. ss. Qed.

(* Made tactic applying @jeehoonkang's opinion *)
Ltac ao_mark H := apply _ao_mark in H.
Ltac aa_unmark H := apply _aa_unmark in H.

(* Find one without __ao_mark__, and try applying "x".
Regardless of success or fail, __ao_mark__ that.
By the nature of Ltac's match, it searches until it succeeds.
If one success happen, _all_once ends, so "repeat" in all_once is needed.
If all fails, "repeat" in all_once will end, and will unmark all __ao_mark__.
About repeat: https://coq.inria.fr/refman/Reference-Manual011.html#hevea_tactic201
 *)
(*
TODO this tactic can run inf loop, if given tactic generates a premise that
is again the target of the given tactic. This can be systematically prevented
if we snapshot the given moment (by marking detph 1), and then run
all_once (marking depth 2). For now, user may carefully pass tactic that ensures
not to run inf loop, one tip is to use pattern match of type.
See the proof of clear_unary_preserved_expr in SoundReduceMaydiff.v
*)
Tactic Notation "_all_once" tactic(tac) :=
  match goal with
  | [ H: ?y |- _ ] =>
    match y with
    | (__ao_mark__ _) => fail 1
    | _ =>
      try (tac H); ao_mark H
    end
  end.

Ltac aa_unmark_all :=
  repeat match goal with
  | [ H: (__ao_mark__ ?y) |- _ ] =>
    aa_unmark H
  end.

Tactic Notation "all_once" tactic(tac) :=
  repeat (_all_once tac); aa_unmark_all.

Ltac apply_in x H := apply x in H.

Ltac apply_all_once x := all_once (apply_in x).

Goal forall (a b c d e: bool) f,
    (negb true = false) -> (* IT SHOULD NOT RUN INF LOOP *)
    (negb false = true) ->
    (negb a = true) ->
    (negb b = true) ->
    (negb c = true) ->
    (negb d = true) ->
    (negb e = true) ->
    (0 :: 2 :: nil = f) -> (* SHOULD IGNORE THIS *)
    True -> (* SHOULD IGNORE THIS *)
    (negb (true && false) = true) -> False.
Proof.
  i.
  repeat (_all_once (apply_in negb_true_iff)). (* all Prop should be __ao_mark__ed, regardless of success or fail *)
  aa_unmark_all. (* all __ao_mark__ will disappear *)
  Undo. Undo.
  (* apply_in negb_true_iff H2. *)
  Time all_once (apply_in negb_true_iff).
  Undo.
  ao_mark H0. (* This will prevent all_once to happen here *)
  all_once (apply_in negb_true_iff).
  (* User only needs to know "all_once" and "ao_mark". *)
  Undo. Undo.
  apply_all_once negb_true_iff.
Abort.

Ltac solve_compat_bool := repeat red; ii; subst; eauto.

Ltac des_bool :=
  repeat
    match goal with
    | [ H: sflib.is_true _ |- _] => unfold sflib.is_true in H
    | [ H: _ |- sflib.is_true _ ] => unfold sflib.is_true
    | [ H: _ && _ = true |- _ ] => apply andb_true_iff in H
    | [ H: _ && _ = false |- _ ] => apply andb_false_iff in H
    | [ H: _ || _ = true |- _ ] => apply orb_true_iff in H
    | [ H: _ || _ = false |- _ ] => apply orb_false_iff in H
    | [ H: negb _ = true |- _ ] => apply negb_true_iff in H
    | [ H: negb _ = false |- _ ] => apply negb_false_iff in H
    | [ H: context[ _ && false ] |- _ ] => rewrite andb_false_r in H
    | [ H: context[ false && _ ] |- _ ] => rewrite andb_false_l in H
    | [ H: context[ _ || true ] |- _ ] => rewrite orb_true_r in H
    | [ H: context[ true || _ ] |- _ ] => rewrite orb_true_l in H
    | [ H: context[ negb (_ && _) ] |- _ ] => rewrite negb_andb in H
    | [ H: context[ negb (_ || _) ] |- _ ] => rewrite negb_orb in H
    | [ H: context[ negb (negb _) ] |- _ ] => rewrite negb_involutive in H
    | [ |- _ && true = true ] => apply andb_true_iff; splits; [|auto]
    | [ |- true && _ = true ] => apply andb_true_iff; splits; [auto|]
    | [ |- _ || true = true ] => apply orb_true_iff; right; auto
    | [ |- true || _ = true ] => apply orb_true_iff; left; auto
    | [ |- _ && false = true ] => exfalso
    | [ |- false && _ = true ] => exfalso
    | [ |- _ || false = true ] => apply orb_true_iff; left
    | [ |- false || _ = true ] => apply orb_true_iff; right
    end.

(* Constant compcert.lib.Coqlib.proj_sumbool *)
(* proj_sumbool is from compcert *)
(* If we want to insert it inside sflib, we should first define proj_sumbool inside sflib *)
Lemma proj_sumbool_false: forall (P Q : Prop) (a : {P} + {Q}),
    proj_sumbool a = false -> Q.
Proof. ii. destruct a; auto. inv H. Qed.

Ltac des_sumbool :=
  repeat
    match goal with
    | [ H: proj_sumbool ?x = true |- _ ] => apply proj_sumbool_true in H
    | [ H: proj_sumbool ?x = false |- _ ] => apply proj_sumbool_false in H
    end.
(* check InvBooleans tactic in compcert *)

(* It is important that f does not look into A *)
(* This can give you following spec *)
Fixpoint filter_AL_atom {A: Type} (f: atom -> bool) (al: AssocList A) :=
  match al with
  | [] => []
  | (a, h) :: t =>
    if f(a)
    then (a, h) :: (filter_AL_atom f t)
    else (filter_AL_atom f t)
  end.

Lemma lookup_AL_filter_false {A: Type} id al f
      (NOPASS: f id = false):
  <<NORESULT: lookupAL A (filter_AL_atom f al) id = None>>.
Proof.
  red.
  induction al; ss.
  destruct a; ss.
  destruct (f a) eqn:T; ss.
  destruct (id == a) eqn:T2; ss. subst.
  clarify.
Qed.

Lemma lookup_AL_filter_true {A: Type} id al f
      (PASS: f id = true):
  <<RESULT: lookupAL A (filter_AL_atom f al) id =
              lookupAL A al id >>.
Proof.
  red.
  induction al; ss.
  destruct a.
  destruct (id == a) eqn:T; ss.
  - subst. rewrite PASS. ss. rewrite T. ss.
  - destruct (f a) eqn:T2; ss.
    rewrite T. ss.
Qed.

Lemma lookup_AL_filter_some {A: Type} id val al f
  (FILTERED: lookupAL A (filter_AL_atom f al) id = Some val):
  lookupAL A al id = Some val.
Proof.
  destruct (f id) eqn:T.
  - exploit (@lookup_AL_filter_true A); eauto. ii; des.
    rewrite FILTERED in x0. ss.
  - exploit (@lookup_AL_filter_false A); eauto. ii; des.
    rewrite FILTERED in x0. ss.
Qed.

Lemma lookup_AL_filter_spec
      {X: Type} f (al: AssocList X) i:
  lookupAL _ (filter_AL_atom f al) i =
  if f i
  then lookupAL _ al i
  else None.
Proof.
  destruct (f i) eqn:T.
  - apply lookup_AL_filter_true. ss.
  - apply lookup_AL_filter_false. ss.
Qed.

Lemma in_filter_find {A: Type} (x: A) f l
  (IN: In x (filter f l)):
  exists x2, find f l = Some x2 /\ f x2.
Proof.
  induction l; ss.
  destruct (f a) eqn:T.
  - eexists; eauto.
  - clear T. specialize (IHl IN). ss.
Qed.

Lemma In_concat {A B C: Type} f (a: A) (x: B) xs
      (IN1: In a (f x))
      (IN2: In (f x) (List.map f xs)):
  <<IN3: In a (concat (List.map f xs))>>.
Proof.
  red.
  generalize dependent a.
  generalize dependent x.
  induction xs; ii; ss.
  des.
  - rewrite IN2.
    destruct (f x); inv IN1.
    + ss. left. ss.
    + ss. right.
      eapply in_or_app.
      left; ss.
  - exploit IHxs; eauto; []; ii; des.
    destruct (f a) eqn:T; ss.
    right.
    eapply in_or_app. right. ss.
Qed.

Lemma In_map {A B: Type} (f: A -> B) (a: A) al
      (IN: In a al):
        <<IN2: In (f a) (List.map f al)>>.
Proof.
  generalize dependent a.
  induction al; ii; ss.
  des; red; ss. subst.
  - left; ss.
  - right. eapply IHal; ss.
Qed.

Lemma forallb_filter_map {A B: Type} (f: B -> bool) (g: A -> option B) (xs: list A)
      (FORALL: List.forallb f (filter_map g xs)):
  (* List.forallb (fun x => match (g x) with | Some y => f y | None => true end) xs. *)
  <<FORALL: List.forallb (fun x => List.forallb f (g x)) xs>>.
Proof.
  red.
  generalize dependent FORALL.
  induction xs; ii; ss.
  destruct (g a) eqn:T; des_bool; ss.
  - unfold is_true in FORALL. (* des_bool should solve this!!! KILL ALL is_true *)
    repeat (des_bool; des).
    rewrite FORALL.
    rewrite IHxs; eauto.
  - rewrite IHxs; ss.
Qed.

Lemma find_app
      A pred (l1 l2:list A):
  find pred (l1 ++ l2) =
  match find pred l1 with
  | Some v1 => Some v1
  | None => find pred l2
  end.
Proof.
  induction l1; ss. destruct (pred a); ss.
Qed.

Lemma In_eq_find {X} (x: X) xs (x_eq_dec: forall x1 x2, {x1 = x2} + {x1 <> x2})
      (IN: In x xs):
  <<FOUND: (find (fun y => x_eq_dec x y) xs)>>.
Proof.
  red.
  generalize dependent IN.
  induction xs; ii; inv IN; ss.
  - destruct (x_eq_dec x x) eqn:T; ss.
  - specialize (IHxs H).
    destruct (x_eq_dec x a) eqn:T; ss.
Qed.

Lemma list_forallb2_implies A (P1 P2: A -> A -> bool) l1 l2
      (COND: list_forallb2 P1 l1 l2 = true)
      (INC: P1 <2= P2)
  : list_forallb2 P2 l1 l2 = true.
Proof.
  revert l2 COND.
  induction l1; ss.
  i. destruct l2; ss.
  apply andb_true_iff in COND. des.
  apply andb_true_iff.
  split; auto.
  apply INC; auto.
Qed.

Definition AtomSetImpl_from_list
           (ids:list id): AtomSetImpl.t :=
  fold_left (flip AtomSetImpl.add) ids AtomSetImpl.empty.

Lemma AtomSetImpl_from_list_spec ids:
  forall id, AtomSetImpl.mem id (AtomSetImpl_from_list ids) <-> In id ids.
Proof.
  unfold AtomSetImpl_from_list. rewrite <- fold_left_rev_right.
  intros. rewrite in_rev.
  match goal with
  | [|- context[@rev ?T ?ids]] => induction (@rev T ids)
  end; simpl.
  - rewrite AtomSetFacts.empty_b. intuition.
  - unfold flip in *. rewrite AtomSetFacts.add_b.
    unfold AtomSetFacts.eqb. constructor; intros.
    + apply orb_true_iff in H. destruct H.
      * left. destruct (AtomDT.eq_dec a id0); intuition.
      * right. apply IHl0. auto.
    + apply orb_true_intro. destruct H.
      * subst. destruct (AtomDT.eq_dec id0 id0); auto.
      * right. apply IHl0. auto.
Qed.

Lemma existsb_rev A pred (l:list A):
  existsb pred l = existsb pred (rev l).
Proof.
  induction l; ss. rewrite IHl, existsb_app.
  destruct (existsb pred (rev l0)); ss. apply orb_true_r.
Qed.

Lemma list_disjoint_comm A (xs ys: list A)
  (DISJOINT: list_disjoint xs ys)
  :
    <<DISJOINT: list_disjoint ys xs>>
.
Proof.
  generalize dependent ys.
  induction xs; ii; ss.
  des; ss.
  - clarify. unfold list_disjoint in DISJOINT.
    eapply DISJOINT; eauto.
    left; ss.
  - clarify.
    exploit DISJOINT; eauto.
    right; ss.
Qed.

Module FSetAVLExtra (E: OrderedType.OrderedType).

  Include FSetAVL.Make E.
  Definition notin x L := ~ In x L.
  Definition add_list (xs: list E.t) (base: t): t :=
    List.fold_left (fun s i => add i s) xs base
  .

End FSetAVLExtra.

Module FSetFactsExtra (E: OrderedType.OrderedType) (M: FSetInterface.S with Module E := E).

  Include FSetFacts.Facts M.

  Definition map f s := M.fold (compose M.add f) s M.empty.

  Lemma exists_false_iff
        s f
        (COMPAT: compat_bool E.eq f):
    ~ M.Exists (fun x : M.elt => f x = true) s <->
    M.exists_ f s = false.
  Proof.
    econs; ii.
    - destruct (M.exists_ f s) eqn:X; ss.
      contradict H. apply exists_iff; ss.
    - apply exists_iff in H0; ss. clarify.
  Qed.

  Lemma exists_filter
        pred1 pred2 ids
        (PRED1: compat_bool E.eq pred1)
        (PRED2: compat_bool E.eq pred2)
    : M.exists_ pred1 (M.filter pred2 ids) =
      M.exists_ (fun x => andb (pred1 x) (pred2 x)) ids.
  Proof.
    destruct (M.exists_ pred1 (M.filter pred2 ids)) eqn:X1.
    - apply exists_iff in X1; [|solve_compat_bool].
      inv X1. des. apply filter_iff in H; [|solve_compat_bool]. des.
      symmetry. apply exists_iff; ss.
      { ii. f_equal; eauto. }
      econs. esplits; eauto. apply andb_true_iff. ss.
    - symmetry. apply exists_false_iff.
      { ii. f_equal; eauto. }
      apply exists_false_iff in X1; ss. contradict X1.
      inv X1. des. apply andb_true_iff in H0. des.
      econs. splits; eauto. apply filter_iff; ss.
  Qed.

  Lemma map_spec f s ty
        (F: Proper (E.eq ==> E.eq) f):
    M.mem ty (map f s) =
    M.exists_ (eqb ty <*> f) s.
  Proof.
    unfold map. rewrite M.fold_1, <- fold_left_rev_right.
    rewrite exists_b; cycle 1.
    { ii. unfold eqb, compose.
      destruct (eq_dec ty (f x)), (eq_dec ty (f y)); ss.
      - contradict n. etransitivity; eauto.
      - contradict n. etransitivity; eauto.
    }
    rewrite existsb_rev.
    induction (rev (M.elements s)); ss.
    - destruct (M.mem ty M.empty) eqn:X; ss.
      apply M.mem_2 in X. exfalso. eapply M.empty_1. eauto.
    - unfold compose, flip in *. rewrite add_b, IHl0.
      f_equal. unfold eqb. destruct (eq_dec (f a) ty), (eq_dec ty (f a)); ss.
      + contradict n. symmetry. ss.
      + contradict n. symmetry. ss.
  Qed.

  Definition from_list
             (ids:list E.t): M.t :=
    fold_left (flip M.add) ids M.empty.

  Lemma from_list_spec ids:
    forall id, M.mem id (from_list ids) <-> InA E.eq id ids.
  Proof.
    unfold from_list. rewrite <- fold_left_rev_right.
    intros. rewrite <- InA_rev.
    unfold M.elt.
    match goal with
    | [|- context[@rev ?T ?ids]] => induction (@rev T ids)
    end; simpl.
    - rewrite empty_b. intuition. inv H.
    - unfold flip in *. rewrite add_b.
      unfold eqb. constructor; intros.
      + apply orb_true_iff in H. destruct H.
        * left. destruct (eq_dec a id0); intuition.
        * right. apply IHl0. auto.
      + apply orb_true_intro. inv H.
        * destruct (eq_dec a id0); auto.
        * right. apply IHl0. auto.
  Qed.

End FSetFactsExtra.

Definition isMallocInst(c: cmd): bool :=
  match c with
  | LLVMsyntax.insn_malloc _ _ _ _ => true
  | _ => false
  end.

Definition is_none X (x: option X): bool :=
  match x with
  | None => true
  | _ => false
  end
.

Definition is_some X (x: option X): bool :=
  match x with
  | Some _ => true
  | _ => false
  end
.

Definition list_inb X (dec: forall x0 x1: X, {x0 = x1} + {x0 <> x1}) (xs: list X) (x0: X) : bool :=
  is_some (List.find (dec x0) xs)
.
