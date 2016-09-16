Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Classical.
Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.
Require Import opsem.

Require Import sflib.
Require Import paco.
Import Opsem.

Require Import TODO.
Require Import Postcond.
Require Import Validator.
Require Import GenericValues.
Require Import SimulationLocal.
Require InvMem.
Require InvState.
Require Import SoundBase.

Set Implicit Arguments.

Lemma get_lhs_in_spec
      ld (rhs: Exprs.Expr.t) x
  (LHS: Exprs.ExprPairSet.In x (Hints.Invariant.get_lhs ld rhs)):
  (snd x) = rhs /\ Exprs.ExprPairSet.In x ld.
Proof.
  unfold Hints.Invariant.get_lhs, flip in *.
  rewrite Exprs.ExprPairSetFacts.filter_iff in LHS; cycle 1.
  { solve_compat_bool. }
  des. des_sumbool. ss.
Qed.

Lemma get_rhs_in_spec
      ld (lhs: Exprs.Expr.t) x
  (RHS: Exprs.ExprPairSet.In x (Hints.Invariant.get_rhs ld lhs)):
  (fst x) = lhs /\ Exprs.ExprPairSet.In x ld.
Proof.
  unfold Hints.Invariant.get_rhs, flip in *.
  rewrite Exprs.ExprPairSetFacts.filter_iff in RHS; cycle 1.
  { solve_compat_bool. }
  des. des_sumbool. ss.
Qed.

Lemma reduce_maydiff_lessdef_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst invmem inv
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem
                            (reduce_maydiff_lessdef inv)>>.
Proof.
  inversion STATE. econs; eauto. ii.
  specialize (MAYDIFF id0). ss.
  rewrite Exprs.IdTSetFacts.filter_b in NOTIN; cycle 1.
  { repeat red. ii. subst. eauto. }
  des_bool. des; [by eapply MAYDIFF; eauto|].
  des_bool.
  apply Exprs.ExprPairSetFacts.exists_iff in NOTIN; cycle 1.
  { repeat red. ii. subst. eauto. }
  inv NOTIN. des.
  apply Exprs.ExprPairSetFacts.exists_iff in H0; cycle 1.
  { repeat red. ii. subst. eauto. }
  inv H0. des.
  apply get_lhs_in_spec in H1.
  apply get_rhs_in_spec in H.
  destruct x, x0. ss. des. subst.
  rename id0 into __ID__.

  (* src lessdef x, t0 --> t0's result exists *)
  inv SRC. clear NOALIAS UNIQUE PRIVATE.
  unfold Exprs.ExprPairSet.For_all in *.
  specialize (LESSDEF (Exprs.Expr.value (Exprs.ValueT.id __ID__), t0)).
  apply LESSDEF in H3. clear LESSDEF.
  exploit H3; eauto. i. des.

  (* inject_expr t0, t1 --> t1's result exists *)
  exploit InvState.Rel.inject_expr_spec; eauto. i. des.

  (* tgt t1, x --> x's result exists *)
  inv TGT. clear NOALIAS UNIQUE PRIVATE.
  specialize (LESSDEF (t1, Exprs.Expr.value (Exprs.ValueT.id __ID__))).
  apply LESSDEF in H2. clear LESSDEF.
  exploit H2; eauto. i. des.

  (* val_src >= val_a >= val_tgt >= val_b *)
  esplits; eauto.
  clear VAL0 VAL_TGT VAL2 H2 H3 H0 VAL_SRC MAYDIFF.
  rename val0 into val_a.
  rename val2 into val_b.
  exploit GVs.inject_lessdef_compose; eauto. i. des.
  exploit GVs.lessdef_inject_compose; cycle 1; eauto.
Qed.

(* TODO
 * preserved: same
 * otherwise: none
 *)

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
  ss.
  destruct (id == a) eqn:T2; ss.
  subst. rewrite T in NOPASS. ss.
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

Definition clear_locals
           (preserved: id -> bool)
           (locals: GVsMap): GVsMap :=
  filter_AL_atom (preserved) locals.

Definition clear_unary
           (preserved: Exprs.Tag.t * id -> bool)
           (inv: InvState.Unary.t): InvState.Unary.t :=
  InvState.Unary.update_ghost
    (clear_locals (fun id => preserved (Exprs.Tag.ghost, id)))
    (InvState.Unary.update_previous
       (clear_locals (fun id => preserved (Exprs.Tag.previous, id)))
       inv).

Lemma in_filter_find {A: Type} (x: A) f l
  (IN: In x (filter f l)):
  exists x2, find f l = Some x2 /\ f x2.
Proof.
  induction l; ss.
  destruct (f a) eqn:T.
  - eexists; eauto.
  - clear T. specialize (IHl IN). ss.
Qed.

Definition clear_rel
           (preserved: Exprs.Tag.t * id -> bool)
           (inv: InvState.Rel.t): InvState.Rel.t :=
  InvState.Rel.update_both (clear_unary preserved) inv.

Definition equiv_locals (ids:list id) (lhs rhs:GVsMap): Prop :=
  forall id (ID: List.In id ids), lookupAL _ lhs id = lookupAL _ rhs id.

(* TODO move this code into Exprs' tag module *)
Definition is_previous x := match x with Exprs.Tag.previous => true | _ => false end.
Definition is_ghost x := match x with Exprs.Tag.ghost => true | _ => false end.

Inductive equiv_unary (ids:list Exprs.IdT.t) (lhs rhs:InvState.Unary.t): Prop :=
| equiv_unary_intro
    (PREVIOUS: equiv_locals (List.map snd (List.filter (is_previous <*> fst) ids))
                            lhs.(InvState.Unary.previous) rhs.(InvState.Unary.previous))
    (GHOST: equiv_locals (List.map snd (List.filter (is_ghost <*> fst) ids))
                         lhs.(InvState.Unary.ghost) rhs.(InvState.Unary.ghost))
    (* TODO: nil => filter_map from ids *)
.

Lemma clear_unary_subset_idT st_unary f id invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_idT
                   st_unary (clear_unary f invst_unary) id =
                 Some val)):
  <<VAL: (InvState.Unary.sem_idT st_unary invst_unary id =
          Some val)>>.
Proof.
  red.
  unfold InvState.Unary.sem_idT in *.
  unfold clear_unary, clear_locals in *.
  unfold InvState.Unary.update_ghost, InvState.Unary.update_previous in *. ss.
  unfold InvState.Unary.sem_tag in *. ss.
  destruct id. rename i0 into id. ss.
  destruct invst_unary. ss.
  destruct t; ss.
  - exploit (@lookup_AL_filter_some GenericValue); eauto.
  - exploit (@lookup_AL_filter_some GenericValue); eauto.
Qed.

Lemma clear_unary_subset_valueT conf_unary st_unary f vt invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_valueT conf_unary
                   st_unary (clear_unary f invst_unary) vt =
                 Some val)):
  <<VAL: (InvState.Unary.sem_valueT conf_unary st_unary invst_unary vt =
          Some val)>>.
Proof.
  red.
  destruct vt; ss.
  exploit clear_unary_subset_idT; eauto.
Qed.

Lemma clear_unary_subset_list_valueT conf_unary st_unary f vts invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_list_valueT conf_unary
                   st_unary (clear_unary f invst_unary) vts =
                 Some val)):
  <<VAL: (InvState.Unary.sem_list_valueT conf_unary st_unary invst_unary vts =
          Some val)>>.
Proof.
  red.
  generalize dependent val.
  induction vts; i; ss.
  destruct a; ss.
  Ltac exploit_with H x :=
    (exploit H; [exact x|]; eauto; ii; des).
  des_ifs; ss; (all_once exploit_with clear_unary_subset_valueT); (exploit IHvts; eauto; ii; des); clarify.
Qed.

Lemma clear_unary_subset_expr conf_unary st_unary f expr invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_expr conf_unary
                   st_unary (clear_unary f invst_unary) expr =
                 Some val)):
  <<VAL: (InvState.Unary.sem_expr conf_unary st_unary invst_unary expr =
          Some val)>>.
Proof.
  red.
  Ltac exploit_clear_unary_subset_with x :=
    match (type of x) with
    | (InvState.Unary.sem_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_subset_valueT; [exact x|]; eauto; ii; des)
    | (InvState.Unary.sem_list_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_subset_list_valueT; [exact x|]; eauto; ii; des)
    end.
  Time destruct expr; ss;
    des_ifs; ss; (all_once exploit_clear_unary_subset_with); clarify.
  (* exploit_with: Finished transaction in 25.39 secs (25.194u,0.213s) (successful) *)
  (* exploit_with_fast: Finished transaction in 7.575 secs (7.536u,0.044s) (successful) *)
Qed.

Lemma reduce_maydiff_preserved_sem_idT st_src st_tgt
      invst inv id val_src val_tgt
  (VAL_SRC: InvState.Unary.sem_idT st_src
              (clear_unary (reduce_maydiff_preserved inv) (InvState.Rel.src invst)) id =
            Some val_src)
  (VAL_TGT: InvState.Unary.sem_idT st_tgt (InvState.Rel.tgt invst) id = Some val_tgt):
  <<VAL_TGT: InvState.Unary.sem_idT st_tgt
    (clear_unary (reduce_maydiff_preserved inv) (InvState.Rel.tgt invst)) id = Some val_tgt>>.
Proof.
  destruct id.
  rename i0 into id.
  unfold InvState.Unary.sem_idT in *. ss.
  unfold InvState.Unary.sem_tag in *. ss.
  destruct t; ss.
  - rewrite <- VAL_TGT.
    destruct ((fun id0 : LLVMsyntax.id =>
                 reduce_maydiff_preserved inv (Exprs.Tag.previous, id0)) id) eqn:T.
    + exploit (@lookup_AL_filter_true GenericValue id); eauto. ss.
    + exploit (@lookup_AL_filter_false GenericValue id); eauto.
      instantiate (1:= (fun id0 : LLVMsyntax.id =>
                          reduce_maydiff_preserved inv (Exprs.Tag.previous, id0))).
      ss.
      ii; des.
      (* rewrite x0. *)
      (* rewrite VAL_TGT. *)
      (* exfalso. *)
      rewrite x0 in VAL_SRC.
      inv VAL_SRC.
  - rewrite <- VAL_TGT.
    destruct ((fun id0 : LLVMsyntax.id =>
                 reduce_maydiff_preserved inv (Exprs.Tag.ghost, id0)) id) eqn:T.
    + exploit (@lookup_AL_filter_true GenericValue id); eauto. ss.
    + exploit (@lookup_AL_filter_false GenericValue id); eauto.
      instantiate (1:= (fun id0 : LLVMsyntax.id =>
                          reduce_maydiff_preserved inv (Exprs.Tag.ghost, id0))).
      ss.
      ii; des.
      (* rewrite x0. *)
      (* rewrite VAL_TGT. *)
      (* exfalso. *)
      rewrite x0 in VAL_SRC.
      inv VAL_SRC.
Qed.

Lemma incl_lessdef_inv_unary inv_unary:
  <<LESSDEF_INCL:
    List.incl
      (Hints.Invariant.get_idTs_lessdef inv_unary.(Hints.Invariant.lessdef))
      (Hints.Invariant.get_idTs_unary inv_unary)>>.
Proof.
  unfold Hints.Invariant.get_idTs_unary.
  red.
  ss.
  assert(G: incl (Hints.Invariant.get_idTs_lessdef (Hints.Invariant.lessdef inv_unary))
                 (Hints.Invariant.get_idTs_lessdef (Hints.Invariant.lessdef inv_unary))).
  { apply incl_refl. }
  eapply incl_appl in G.
  eapply G.
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
  - specialize (IHxs x IN2 a0 IN1).
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

Lemma In_list {A} (f: Exprs.ExprPair.t -> list A) x xs
      (IN: Exprs.ExprPairSet.In x xs):
  <<IN: List.incl (f x) (List.concat (List.map f (Exprs.ExprPairSet.elements xs)))>>.
Proof.
  red.
  exploit Exprs.ExprPairSetFacts.elements_iff; eauto. ii; des.
  specialize (x1 IN). clear x0.
  exploit InA_iff_In; eauto. ii; des.
  specialize (x2 x1). clear x0. clear x1.
  assert(G: In (f x) (List.map f (Exprs.ExprPairSet.elements xs))).
  { eapply In_map; eauto. }
  exploit (@In_concat A Exprs.ExprPair.t (list A)); eauto.
Qed.

Lemma lessdef_incl
      e1 e2 inv_unary
      (LESSDEF: Exprs.ExprPairSet.In
                  (e1, e2) (Hints.Invariant.lessdef inv_unary)):
  <<INCL: (List.incl (Exprs.Expr.get_idTs e1) (Hints.Invariant.get_idTs_unary inv_unary))
          /\ (List.incl (Exprs.Expr.get_idTs e2) (Hints.Invariant.get_idTs_unary inv_unary))>>.
Proof.
  unfold Exprs.Expr.get_idTs.
  esplits.
  (* - destruct e1; ss. *)
    +
      assert(LESSDEF2 := LESSDEF).
      eapply In_list in LESSDEF; ss.
      red in LESSDEF.
      instantiate (1:= Exprs.ExprPair.get_idTs) in LESSDEF.
      (* exploit (incl_lessdef_inv_unary inv_unary). *)
      (* instantiate (1 := (Hints.Invariant.get_idTs_lessdef *)
      (*                      inv_unary.(Hints.Invariant.lessdef))). *)
      unfold Hints.Invariant.get_idTs_unary.
      unfold Exprs.ExprPair.get_idTs in *. ss.
      unfold Exprs.Expr.get_idTs in *. ss.
      eapply incl_tran.
      {
        instantiate (1:= ((filter_map Exprs.ValueT.get_idTs (Exprs.Expr.get_valueTs e1))
                            ++ (filter_map Exprs.ValueT.get_idTs (Exprs.Expr.get_valueTs e2)))).
        apply incl_appl.
        apply incl_refl.
      }

      eapply incl_tran.
      {
        instantiate
          (1:=
             (concat
                (List.map
                   (fun ep : Exprs.ExprPair.t =>
                      (filter_map Exprs.ValueT.get_idTs (Exprs.Expr.get_valueTs (fst ep)))
                        ++ (filter_map Exprs.ValueT.get_idTs (Exprs.Expr.get_valueTs (snd ep))))
                   (Exprs.ExprPairSet.elements (Hints.Invariant.lessdef inv_unary))))).
        eauto.
      }

      eapply incl_tran.
      {
        instantiate (1:= Hints.Invariant.get_idTs_lessdef (Hints.Invariant.lessdef inv_unary)).
        ss.
      }

      apply incl_appl. apply incl_refl.
    +
      (* COPIED FROM ABOVE *)
      assert(LESSDEF2 := LESSDEF).
      eapply In_list in LESSDEF; ss.
      red in LESSDEF.
      instantiate (1:= Exprs.ExprPair.get_idTs) in LESSDEF.
      (* exploit (incl_lessdef_inv_unary inv_unary). *)
      (* instantiate (1 := (Hints.Invariant.get_idTs_lessdef *)
      (*                      inv_unary.(Hints.Invariant.lessdef))). *)
      unfold Hints.Invariant.get_idTs_unary.
      unfold Exprs.ExprPair.get_idTs in *. ss.
      unfold Exprs.Expr.get_idTs in *. ss.
      eapply incl_tran.
      {
        instantiate (1:= ((filter_map Exprs.ValueT.get_idTs (Exprs.Expr.get_valueTs e1))
                            ++ (filter_map Exprs.ValueT.get_idTs (Exprs.Expr.get_valueTs e2)))).
        apply incl_appr.
        apply incl_refl.
      }

      eapply incl_tran.
      {
        instantiate
          (1:=
             (concat
                (List.map
                   (fun ep : Exprs.ExprPair.t =>
                      (filter_map Exprs.ValueT.get_idTs (Exprs.Expr.get_valueTs (fst ep)))
                        ++ (filter_map Exprs.ValueT.get_idTs (Exprs.Expr.get_valueTs (snd ep))))
                   (Exprs.ExprPairSet.elements (Hints.Invariant.lessdef inv_unary))))).
        eauto.
      }

      eapply incl_tran.
      {
        instantiate (1:= Hints.Invariant.get_idTs_lessdef (Hints.Invariant.lessdef inv_unary)).
        ss.
      }

      apply incl_appl. apply incl_refl.
Qed.

Lemma clear_unary_preserved_valueT
      conf_unary st_unary invst_unary vt val f
      (VAL: InvState.Unary.sem_valueT conf_unary st_unary invst_unary vt = Some val)
      (PRESERVED: (sflib.is_true (List.forallb f (Exprs.ValueT.get_idTs vt)))):
  <<VAL: InvState.Unary.sem_valueT conf_unary st_unary (clear_unary f invst_unary) vt = Some val>>.
Proof.
  red.
  destruct vt; ss.
  des_bool. des. clear PRESERVED0.
  unfold InvState.Unary.sem_idT in *.
  destruct x; ss.
  unfold clear_unary, clear_locals.
  unfold InvState.Unary.update_ghost, InvState.Unary.update_previous in *. ss.
  unfold InvState.Unary.sem_tag in *. ss.
  destruct invst_unary; ss.
  destruct t; ss.
  - exploit (@lookup_AL_filter_true GenericValue).
    {
      (* apply PRESERVED. *) (* WHY IT DOES NOT WORK ???????? *)
      instantiate (1:= i0).
      instantiate  (1:= (fun id0 : id => f (Exprs.Tag.previous, id0))).
      ss.
    } ii; des.
    rewrite x0; ss.
  - (* COPIED FROM ABOVE *)
    exploit (@lookup_AL_filter_true GenericValue).
    {
      (* apply PRESERVED. *) (* WHY IT DOES NOT WORK ???????? *)
      instantiate (1:= i0).
      instantiate  (1:= (fun id0 : id => f (Exprs.Tag.ghost, id0))).
      ss.
    } ii; des.
    rewrite x0; ss.
Qed.

Lemma clear_unary_preserved_list_valueT
      conf_unary st_unary invst_unary vts val f
      (VAL: InvState.Unary.sem_list_valueT conf_unary st_unary invst_unary vts = Some val)
      (PRESERVED: sflib.is_true (List.forallb
                     (fun x => (List.forallb f (Exprs.ValueT.get_idTs x)))
                     (List.map snd vts))):
  <<VAL: InvState.Unary.sem_list_valueT conf_unary st_unary (clear_unary f invst_unary) vts = Some val>>.
Proof.
  generalize dependent PRESERVED.
  generalize dependent val.
  induction vts; ii; ss; red.
  destruct a; ss.
  repeat (des_bool; des).
  des_ifs; ss.
  - (exploit clear_unary_preserved_valueT; [exact Heq1| |]; eauto; ii; des).
    specialize (IHvts l1). exploit IHvts; eauto. ii; des.
    clarify.
  - (exploit clear_unary_preserved_valueT; [exact Heq1| |]; eauto; ii; des).
    clarify.
    specialize (IHvts l0). exploit IHvts; eauto. ii; des.
    ss.
  - (exploit clear_unary_preserved_valueT; [exact Heq0| |]; eauto; ii; des).
    specialize (IHvts l0). exploit IHvts; eauto. ii; des.
    clarify.
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
    des_bool. des.
    rewrite FORALL.
    rewrite IHxs; eauto. ss.
  - rewrite IHxs; ss.
Qed.

Lemma clear_unary_preserved_expr
      conf_unary st_unary invst_unary expr val f
      (VAL: InvState.Unary.sem_expr conf_unary st_unary invst_unary expr = Some val)
      (PRESERVED: List.forallb f (Exprs.Expr.get_idTs expr)):
  <<VAL: InvState.Unary.sem_expr conf_unary st_unary (clear_unary f invst_unary) expr = Some val>>.
Proof.
  red.
  unfold Exprs.Expr.get_idTs in *.
  eapply forallb_filter_map in PRESERVED. des.
  unfold is_true in PRESERVED. (* des_bool should kill it!!!!!!! KILL ALL is_true *)

  Ltac exploit_clear_unary_preserved_with x :=
    match (type of x) with
    | (InvState.Unary.sem_valueT _ _ (clear_unary _ _) _ = _) => fail 1
    | (InvState.Unary.sem_list_valueT _ _ (clear_unary _ _) _ = _) => fail 1
    (* Above is REQUIRED in order to prevent inf loop *)
    | (InvState.Unary.sem_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_preserved_valueT; [exact x| |]; eauto; ii; des)
    | (InvState.Unary.sem_list_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_preserved_list_valueT; [exact x| |]; eauto; ii; des)
    end.

  Time destruct expr; ss;
    repeat (des_bool; des); des_ifs; clarify;
      (all_once exploit_clear_unary_subset_with); clarify;
        (all_once exploit_clear_unary_preserved_with); clarify.
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

Lemma incl_implies_preserved_src
      conf_src st_src invst0 expr val inv
      (VAL: InvState.Unary.sem_expr conf_src st_src (InvState.Rel.src invst0) expr = Some val)
      (INCL: incl (Exprs.Expr.get_idTs expr) (Hints.Invariant.get_idTs_unary (Hints.Invariant.src inv))):
  <<PRESERVED: InvState.Unary.sem_expr conf_src st_src
                                       (clear_unary (reduce_maydiff_preserved inv)
                                                    (InvState.Rel.src invst0)) expr = Some val>>.
Proof.
  red.
  eapply clear_unary_preserved_expr; eauto.
  clear VAL.

  remember (Exprs.Expr.get_idTs expr) as X.
  (* generalize dependent HeqX. *)
  clear HeqX.
  unfold reduce_maydiff_preserved.
  induction X; ii; ss.
  exploit IHX; eauto.
  { eapply elim_incl_cons; eauto. }
  ii; des.
  rewrite x.
  destruct a.
  rename i0 into id.
  destruct t; ss.
  - unfold incl in INCL.
    specialize (INCL (Exprs.Tag.previous, id)).
    exploit INCL. left; eauto. (* although econs; eauto works *)
    ii; des.
    unfold is_true.
    des_bool.
    eapply In_eq_find.
    apply in_app; eauto.
  - unfold incl in INCL.
    specialize (INCL (Exprs.Tag.ghost, id)).
    exploit INCL. left; eauto. (* although econs; eauto works *)
    ii; des.
    unfold is_true.
    des_bool.
    eapply In_eq_find.
    apply in_app; eauto.
Qed.

Lemma incl_implies_preserved_tgt
      conf_tgt st_tgt invst0 expr val inv
      (VAL: InvState.Unary.sem_expr conf_tgt st_tgt (InvState.Rel.tgt invst0) expr = Some val)
      (INCL: incl (Exprs.Expr.get_idTs expr) (Hints.Invariant.get_idTs_unary (Hints.Invariant.tgt inv))):
  <<PRESERVED: InvState.Unary.sem_expr conf_tgt st_tgt
                                       (clear_unary (reduce_maydiff_preserved inv)
                                                    (InvState.Rel.tgt invst0)) expr = Some val>>.
Proof.
  red.
  eapply clear_unary_preserved_expr; eauto.
  clear VAL.

  remember (Exprs.Expr.get_idTs expr) as X.
  (* generalize dependent HeqX. *)
  clear HeqX.
  unfold reduce_maydiff_preserved.
  induction X; ii; ss.
  exploit IHX; eauto.
  { eapply elim_incl_cons; eauto. }
  ii; des.
  rewrite x.
  destruct a.
  rename i0 into id.
  destruct t; ss.
  - unfold incl in INCL.
    specialize (INCL (Exprs.Tag.previous, id)).
    exploit INCL. left; eauto. (* although econs; eauto works *)
    ii; des.
    unfold is_true.
    des_bool.
    eapply In_eq_find.
    apply in_app; eauto.
  - unfold incl in INCL.
    specialize (INCL (Exprs.Tag.ghost, id)).
    exploit INCL. left; eauto. (* although econs; eauto works *)
    ii; des.
    unfold is_true.
    des_bool.
    eapply In_eq_find.
    apply in_app; eauto.
Qed.

Lemma reduce_maydiff_non_physical_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem inv
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem
                              (reduce_maydiff_non_physical inv)>>.
Proof.
  inv STATE.
  unfold reduce_maydiff_non_physical.
  exists (clear_rel (reduce_maydiff_preserved inv) invst0).
  red.
  econs; eauto; ss; cycle 2.
  { ii. (* VAL_SRC (sem_idT) is from ii *) (* sem_inject from MAYDIFF *) ss.
    rewrite Exprs.IdTSetFacts.filter_b in NOTIN; cycle 1.
    { solve_compat_bool. }
    des_bool. des.
    - apply MAYDIFF in NOTIN.
      unfold InvState.Rel.sem_inject in NOTIN.
      exploit (NOTIN val_src); eauto.
      {
        (* ok because it is subset *)
        exploit clear_unary_subset_idT; eauto.
      }
      i. des.
      esplits; eauto.
      {
        exploit reduce_maydiff_preserved_sem_idT; eauto.
      }
    - destruct id0.
      (* TODO do not explicitly write this *)
      unfold Postcond.reduce_maydiff_preserved in NOTIN. ss.
      des_bool. des.
      match goal with
      | [H: bool_of_option ?o = false |- _] => destruct o eqn:T
      end; inv NOTIN0.
      rename t into __t__, i0 into __i__.
      exfalso. clear MAYDIFF TGT SRC MEM CONF invmem.
      unfold InvState.Unary.sem_idT in VAL_SRC. ss.
      unfold InvState.Unary.sem_tag in VAL_SRC. ss.
      destruct invst0. ss.
      destruct src, tgt. ss.
      destruct __t__; inv NOTIN.
      + induction previous; ss; try by inv VAL_SRC.
        apply IHprevious. clear IHprevious.
        destruct a as [aid atag].
        unfold reduce_maydiff_preserved in *. ss.
        destruct (eq_dec __i__ aid); ss.
        * subst.
          unfold Exprs.Tag.t in *.
          unfold clear_locals in *. ss.
          rewrite T in VAL_SRC. ss.
        * unfold clear_locals in *. ss.
          match goal with
          | [H: context[bool_of_option ?o] |- _] => destruct o eqn:T2; ss
          end.
          unfold id in *. destruct (__i__ == aid); ss.
      + (* COPIED FROM ABOVE. EXACTLY SAME PROOF *)
        (* NOTE(jeehoon.kang): if you want to avoid this duplication, you can change some definitions.  *)
        induction ghost; ss; try by inv VAL_SRC.
        apply IHghost. clear IHghost.
        destruct a as [aid atag].
        unfold reduce_maydiff_preserved in *. ss.
        destruct (eq_dec __i__ aid); ss.
        * subst.
          unfold Exprs.Tag.t in *.
          unfold clear_locals in *; ss.
          rewrite T in VAL_SRC. ss.
        * unfold clear_locals in *; ss.
          match goal with
          | [H: context[bool_of_option ?o] |- _] => destruct o eqn:T2; ss
          end.
          unfold id in *. destruct (__i__ == aid); ss.
  }
  - clear TGT.
    econs; inv SRC.
    +
      clear NOALIAS UNIQUE PRIVATE.
      unfold Exprs.ExprPairSet.For_all.
      i.
      destruct x as [e1 e2]; ss.
      specialize (LESSDEF (e1, e2) H).
      unfold InvState.Unary.sem_lessdef in LESSDEF; ss.
      ii. ss.
      specialize (LESSDEF val1).
      assert(G: InvState.Unary.sem_expr
                  conf_src st_src (InvState.Rel.src invst0) e1 = Some val1).
      {
        exploit clear_unary_subset_expr; eauto.
      }
      specialize (LESSDEF G).
      des.
      esplits; eauto.
      assert(K := incl_lessdef_inv_unary (Hints.Invariant.src inv)); des.
      (* exploit incl_lessdef_inv_unary. eauto. *)
      apply incl_implies_preserved_src; eauto.
      eapply In_list with (f:= Exprs.ExprPair.get_idTs) in H. des.
      unfold Exprs.ExprPair.get_idTs in H; ss.
      apply incl_app_inv_r in H.
      eapply incl_tran; eauto.
    +
      clear LESSDEF UNIQUE PRIVATE.
      inv NOALIAS.
      rename NOALIAS0 into NOALIAS.
      econs; ii.
      * clear NOALIAS.
        eapply DIFFBLOCK; eauto.
        eapply clear_unary_subset_valueT; eauto.
        eapply clear_unary_subset_valueT; eauto.
      * clear DIFFBLOCK.
        eapply NOALIAS; eauto.
        eapply clear_unary_subset_valueT; eauto.
        eapply clear_unary_subset_valueT; eauto.
    +
      clear LESSDEF NOALIAS PRIVATE.
      ii.
      specialize (UNIQUE x H).
      inv UNIQUE.
      econs; eauto.
    +
      clear LESSDEF NOALIAS UNIQUE.
      ii.
      specialize (PRIVATE x H).
      unfold InvState.Unary.sem_private in PRIVATE.
      specialize (PRIVATE val).
      apply PRIVATE.
      eapply clear_unary_subset_idT; eauto.
  - clear SRC.
    econs; inv TGT.
    +
      clear NOALIAS UNIQUE PRIVATE.
      unfold Exprs.ExprPairSet.For_all.
      i.
      destruct x as [e1 e2]; ss.
      specialize (LESSDEF (e1, e2) H).
      unfold InvState.Unary.sem_lessdef in LESSDEF; ss.
      ii. ss.
      specialize (LESSDEF val1).
      assert(G: InvState.Unary.sem_expr
                  conf_tgt st_tgt (InvState.Rel.tgt invst0) e1 = Some val1).
      {
        exploit clear_unary_subset_expr; eauto.
      }
      specialize (LESSDEF G).
      des.
      esplits; eauto.
      assert(K := incl_lessdef_inv_unary (Hints.Invariant.tgt inv)); des.
      (* exploit incl_lessdef_inv_unary. eauto. *)
      apply incl_implies_preserved_tgt; eauto.
      eapply In_list with (f:= Exprs.ExprPair.get_idTs) in H. des.
      unfold Exprs.ExprPair.get_idTs in H; ss.
      apply incl_app_inv_r in H.
      eapply incl_tran; eauto.
    +
      clear LESSDEF UNIQUE PRIVATE.
      inv NOALIAS.
      rename NOALIAS0 into NOALIAS.
      econs; ii.
      * clear NOALIAS.
        eapply DIFFBLOCK; eauto.
        eapply clear_unary_subset_valueT; eauto.
        eapply clear_unary_subset_valueT; eauto.
      * clear DIFFBLOCK.
        eapply NOALIAS; eauto.
        eapply clear_unary_subset_valueT; eauto.
        eapply clear_unary_subset_valueT; eauto.
    +
      clear LESSDEF NOALIAS PRIVATE.
      ii.
      specialize (UNIQUE x H).
      inv UNIQUE.
      econs; eauto.
    +
      clear LESSDEF NOALIAS UNIQUE.
      ii.
      specialize (PRIVATE x H).
      unfold InvState.Unary.sem_private in PRIVATE.
      specialize (PRIVATE val).
      apply PRIVATE.
      eapply clear_unary_subset_idT; eauto.
Qed.

Lemma reduce_maydiff_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem inv
      (CONF: InvState.valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem
                              (reduce_maydiff inv)>>.
Proof.
  unfold reduce_maydiff.
  exploit reduce_maydiff_lessdef_sound; eauto. i. des.
  exploit reduce_maydiff_non_physical_sound; eauto.
Qed.
