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

Ltac solve_compat_bool := repeat red; ii; subst; eauto.

(* TODO rename H2 into H(original name)? *)
Ltac des_is_true :=
  repeat
    match goal with
    | [H: sflib.is_true ?x |- _] =>
      let H2 := fresh H in
      destruct x eqn:H2; cycle 1; inversion H; clear H
    (* Intended not to use inv here, because it contains subst, changing other premises  *)
    end.

Ltac des_bool :=
  repeat
    match goal with
    | [ H: ?x && ?y = true |- _ ] => apply andb_true_iff in H
    | [ H: ?x && ?y = false |- _ ] => apply andb_false_iff in H
    | [ H: ?x || ?y = true |- _ ] => apply orb_true_iff in H
    | [ H: ?x || ?y = false |- _ ] => apply orb_false_iff in H
    | [ H: negb ?x = true |- _ ] => apply negb_true_iff in H
    | [ H: negb ?x = false |- _ ] => apply negb_false_iff in H
    | [ H: context[ ?x && false ] |- _ ] => rewrite andb_false_r in H
    | [ H: context[ false && ?x ] |- _ ] => rewrite andb_false_l in H
    | [ H: context[ ?x || true ] |- _ ] => rewrite orb_true_r in H
    | [ H: context[ true || ?x ] |- _ ] => rewrite orb_true_l in H
    | [ H: context[ negb (?x && ?y) ] |- _ ] => rewrite negb_andb in H
    | [ H: context[ negb (?x || ?y) ] |- _ ] => rewrite negb_orb in H
    | [ H: context[ negb (negb ?x) ] |- _ ] => rewrite negb_involutive in H
    end.

Lemma proj_sumbool_false: forall (P Q : Prop) (a : {P} + {Q}),
    proj_sumbool a = false -> Q.
Proof. ii. destruct a; auto. inv H. Qed.

Ltac des_sumbool :=
  repeat
    match goal with
    | [ H: proj_sumbool ?x = true |- _ ] => apply proj_sumbool_true in H
    | [ H: proj_sumbool ?x = false |- _ ] => apply proj_sumbool_false in H
    end.
(* check InvBooleans tactic *)

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
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem inv)
      (MEM: InvMem.Rel.sem conf_src conf_tgt st_src.(Mem) st_tgt.(Mem) invmem):
  <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst invmem
                            (reduce_maydiff_lessdef inv)>>.
Proof.
  inversion STATE. econs; eauto. ii.
  specialize (MAYDIFF id0). ss.
  rewrite Exprs.IdTSetFacts.filter_b in NOTIN; cycle 1.
  { repeat red. ii. subst. eauto. }
  des_is_true. des_bool. des; [by eapply MAYDIFF; eauto|].
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

Lemma clear_unary_subset_list_valueT conf_unary st_unary f vtl invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_list_valueT conf_unary
                   st_unary (clear_unary f invst_unary) vtl =
                 Some val)):
  <<VAL: (InvState.Unary.sem_list_valueT conf_unary st_unary invst_unary vtl =
          Some val)>>.
Proof.
  red.
  generalize dependent val.
  induction vtl; i; ss.
  destruct a; ss.
  Ltac exploit_with x :=
    (exploit clear_unary_subset_valueT; [exact x|]; eauto; ii; des).
  des_ifs; ss; (all_once exploit_with); (exploit IHvtl; eauto; ii; des); clarify.
Qed.

Lemma clear_unary_subset_exprT conf_unary st_unary f expr invst_unary val
      (VAL_SUBSET: (InvState.Unary.sem_expr conf_unary
                   st_unary (clear_unary f invst_unary) expr =
                 Some val)):
  <<VAL: (InvState.Unary.sem_expr conf_unary st_unary invst_unary expr =
          Some val)>>.
Proof.
  red.
  Ltac exploit_with_fast x :=
    match (type of x) with
    | (InvState.Unary.sem_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_subset_valueT; [exact x|]; eauto; ii; des)
    | (InvState.Unary.sem_list_valueT _ _ _ _ = Some _) =>
      (exploit clear_unary_subset_list_valueT; [exact x|]; eauto; ii; des)
    end.
  Time destruct expr; ss;
    des_ifs; ss; (all_once exploit_with_fast); clarify.
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

(* Lemma reduce_maydiff_preserved_sem_idT *)
(*       conf_unary st_unary id invst_unary val invmem_unary inv *)
(*       (* inv is not unary, which is ugly. *)
(* One may re-define reduce_maydiff_preserved to take only unary, but it seems not simple *) *)
(*       (UNARY: *)
(*          (InvState.Unary.sem *)
(*             conf_unary st_unary invst_unary *)
(*             invmem_unary (Hints.Invariant.src inv)) *)
(*          \/ *)
(*          (InvState.Unary.sem *)
(*             conf_unary st_unary invst_unary *)
(*             invmem_unary (Hints.Invariant.tgt inv))) *)
(*       (VAL_UNARY: InvState.Unary.sem_idT st_unary invst_unary id = Some val): *)
(*   InvState.Unary.sem_idT *)
(*     st_unary (clear_unary (reduce_maydiff_preserved inv) invst_unary) id = Some val. *)
(* Proof. *)
(*   unfold InvState.Unary.sem_idT in *. *)
(*   (* assert(SAFE: (reduce_maydiff_preserved inv) id = false). *) *)
(*   destruct id; ss. *)
(*   rename i0 into id. *)
(*   assert(SAFE: (fun id0 : LLVMsyntax.id => *)
(*                   reduce_maydiff_preserved inv (t, id0)) id = true). *)
(*   { *)
(*     unfold reduce_maydiff_preserved. *)
(*     ss. *)
(*     des. *)
(*     - *)
(*       inv UNARY. *)
(*       admit. *)
(*     - admit. *)
(*       (* inv UNARY. *) *)
(*   } *)
(*   clear UNARY. *)
(*   unfold clear_unary, clear_locals in *. *)
(*   unfold InvState.Unary.update_ghost, InvState.Unary.update_previous in *. ss. *)
(*   unfold InvState.Unary.sem_tag in *. ss. *)
(*   destruct invst_unary; ss. *)
(*   destruct t; ss. *)
(*   - exploit (@lookup_AL_filter_true *)
(*                GenericValue id previous *)
(*                (fun id0 : LLVMsyntax.id => *)
(*                   reduce_maydiff_preserved inv (Exprs.Tag.previous, id0))); eauto. *)
(*     ii; des. *)
(*     rewrite <- VAL_UNARY. eauto. *)
(*   - exploit (@lookup_AL_filter_true *)
(*                GenericValue id ghost *)
(*                (fun id0 : LLVMsyntax.id => *)
(*                   reduce_maydiff_preserved inv (Exprs.Tag.ghost, id0))); eauto. *)
(*     ii; des. *)
(*     rewrite <- VAL_UNARY. eauto. *)
(* Abort. *)

Lemma reduce_maydiff_non_physical_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem inv
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
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
    des_is_true. des_bool. des.
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
  - econs.
    inv SRC.
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
        admit.
      }
      specialize (LESSDEF G).
      des.
      esplits; eauto.
      (* exploit clear_unary_subset_exprT. apply VAL2. ii; des. *)

      unfold clear_unary, clear_locals; ss.
      destruct invst0; ss.
      destruct src; ss.
      admit.
    + admit.
    + admit.
    + admit.
  - admit.
  (* - exploit preserved_equiv_unary. apply SRC. eauto. i. des. ss. *)
  (* - exploit reduce_maydiff_preserved_fit_type_spec1; eauto. i. des. ss. *)
Admitted.

Lemma reduce_maydiff_sound
      m_src m_tgt
      conf_src st_src
      conf_tgt st_tgt
      invst0 invmem inv
      (CONF: valid_conf m_src m_tgt conf_src conf_tgt)
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
