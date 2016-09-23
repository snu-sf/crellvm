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
Require Import Validator.
Require Import Postcond.
Require Import Exprs.
Require Import GenericValues.
Require InvMem.
Require InvState.
Require Import SoundBase.
Require Import SoundImplies. (* for preorder GVs.lessdef *)
Require Import Inject. (* for simtac *)

Set Implicit Arguments.


(* TODO: lemma on tag.previous *)

(* TODO: Unify this snapshot_specs *)

(* Definition snapshot_as_previous st invst: Prop := *)
(*   forall x gvx *)
(*          (LOCAL: lookupAL _ st.(EC).(Locals) x = Some gvx), *)
(*     <<PREV: InvState.Unary.sem_idT st invst (Tag.previous, x) = Some gvx>>. *)

(* Definition snapshot_spec2 st invst: Prop := *)
(*   forall x gvx *)
(*          (PREV: InvState.Unary.sem_idT st invst (Tag.previous, x) = Some gvx), *)
(*     <<LOCAL: lookupAL _ st.(EC).(Locals) x = Some gvx>>. *)

Definition snapshot_previous st invst: Prop :=
  forall x,
    <<SNAPSHOT_PREV: InvState.Unary.sem_idT st invst (Tag.previous, x) =
    lookupAL _ st.(EC).(Locals) x>>.

Definition snapshot_ghost invst0 invst1: Prop :=
  <<SNAPSHOT_GHOST: invst0.(InvState.Unary.ghost) = invst1.(InvState.Unary.ghost)>>.

Lemma physical_previous_lessdef_spec
      e1 e2 inv
      (IN: ExprPairSet.In (e1, e2) (Snapshot.physical_previous_lessdef inv))
  :
    exists x,
      <<IN_UNARY: In (Tag.previous, x) (Hints.Invariant.get_idTs_unary inv)>> /\
      (<<EXPR1: e1 = Expr.value (ValueT.id (Tag.previous, x))>> /\
       <<EXPR2: e2 = Expr.value (ValueT.id (Tag.physical, x))>>
                \/
       <<EXPR1: e2 = Expr.value (ValueT.id (Tag.previous, x))>> /\
       <<EXPR2: e1 = Expr.value (ValueT.id (Tag.physical, x))>>).
Proof.
  unfold Snapshot.physical_previous_lessdef in IN.
  rewrite IdTSet.fold_1 in IN.
  rewrite <- fold_left_rev_right in IN.
Admitted.

  (* match goal with *)
  (* | [H: (negb <*> LiftPred.ExprPair _) (_, _) = _ |- _] => *)
  (*   let FILTER1 := fresh "FILTER1" in *)
  (*   let FILTER2 := fresh "FILTER2" in *)
  (*   unfold compose, LiftPred.ExprPair in H; simtac; ss; *)
  (*   apply orb_false_iff in H; destruct H as [FILTER1 FILTER2] *)
  (* | [H: (negb <*> LiftPred.ValueTPair _) (_, _) = _ |- _] => *)
  (*   unfold compose, LiftPred.ValueTPair in H; simtac; solve_des_bool *)
  (* end. *)


(* Lemma expr_no_prev_sem_preserved *)
(*       conf st1 st2 invst e *)
(*       (LOCALS: st1.(EC).(Locals) = st2.(EC).(Locals)) *)
(*       (MEM: st1.(Mem) = st2.(Mem)) *)
(*       (NOPREV: LiftPred.Expr Snapshot.IdT e = false) *)
(*   : <<SEM: InvState.Unary.sem_expr conf st1 invst e = *)
(*            InvState.Unary.sem_expr conf st2 invst e>>. *)
(* Proof. *)
(*   destruct e; *)
(*     try (ss; repeat solve_des_bool; *)
(*          des_ifs; solve_sem_valueT; solve_sem_idT; congruence). *)
(*   - ss. repeat solve_des_bool. *)
(*     des_ifs. *)
(*     + admit. (* sem_list_valueT *) *)
(*     + admit. *)
(*     + (* solve_sem_valueT; try congruence. *) *)
(*       admit. *)
(*     + admit. *)
(*     + solve_sem_valueT; solve_sem_idT; congruence. *)
(*   - ss. repeat solve_des_bool. *)
(*     des_ifs; try (solve_sem_valueT; solve_sem_idT; congruence). *)
(*     + destruct v. *)
(*       { *)
(*         ss. *)
(*         destruct x as [xtag x]. *)
(*         { destruct xtag; ss. *)
(*           { solve_sem_idT. rewrite LOCALS in *. clarify. } *)
(*           { solve_sem_idT. clarify. } *)
(*         } *)
(*       } *)
(*       { ss. clarify. } *)
(*     + admit. *)
(*   - destruct v; ss. *)
(*     destruct x as [xtag x]; destruct xtag; ss. *)
(*     red. solve_sem_idT. congruence. *)
(* Admitted. *)

Lemma valueT_no_prev_sem_preserved
      conf st invst0 invst1 v
      (NOPREV: LiftPred.ValueT Snapshot.IdT v = false)
      (GHOST: invst0.(InvState.Unary.ghost) = invst1.(InvState.Unary.ghost))
  : <<SEM: InvState.Unary.sem_valueT conf st invst0 v = InvState.Unary.sem_valueT conf st invst1 v>>.
Proof.
  destruct v; eauto.
  destruct x as [xtag x]. ss.
  destruct xtag; ss.
  red. solve_sem_idT. congruence.
Qed.

Ltac solve_liftpred_nopred :=
  repeat match goal with
         | [H: Postcond.LiftPred.ValueT Postcond.Snapshot.IdT _ = false |- _ ] =>
           eapply valueT_no_prev_sem_preserved in H; des; eauto
         end.

Lemma expr_no_prev_sem_preserved
      conf st invst0 invst1 e
      (NOPREV: LiftPred.Expr Snapshot.IdT e = false)
      (GHOST: invst0.(InvState.Unary.ghost) = invst1.(InvState.Unary.ghost))
  : <<SEM: InvState.Unary.sem_expr conf st invst0 e = InvState.Unary.sem_expr conf st invst1 e>>.
Proof.
  Time destruct e; unfold LiftPred.Expr in *; try solve_des_bool;
    try (solve_liftpred_nopred;
         solve_sem_valueT; solve_sem_idT; des_ifs; fail).
  (* Finished transaction in 17.507 secs (17.477u,0.042s) (successful) *)
  - solve_liftpred_nopred.
    solve_sem_valueT.
    + solve_sem_idT. des_ifs.
      * admit. (* gep: sem_list_valueT *)
      * admit.
      * admit.
    + solve_sem_idT. des_ifs.
      * admit.
      * admit.
      * admit.
    + solve_sem_idT. des_ifs.
      * admit.
      * admit.
      * admit.
    + solve_sem_idT. des_ifs.
      * admit.
      * admit.
      * admit.
  - (* select *)
    solve_des_bool.
    solve_liftpred_nopred.
    admit.
Admitted.

Lemma existsb_rev A pred (l:list A):
  existsb pred l = existsb pred (rev l).
Proof.
Admitted.

Lemma IdTSet_map_spec
      f s ty
  : IdTSet.mem ty (IdTSet_map f s) =
    IdTSet.exists_ (IdTSetFacts.eqb ty <*> f) s.
Proof.
  unfold IdTSet_map. rewrite IdTSet.fold_1, <- fold_left_rev_right.
  rewrite IdTSetFacts.exists_b; [|solve_compat_bool].
  rewrite existsb_rev.
  unfold IdTSet.elt. induction (rev (IdTSet.elements s)); ss.
  - admit.
  - unfold compose in *. rewrite IdTSetFacts.add_b. rewrite IHl0.
    admit.
Admitted.

Lemma PtrSet_map_spec
      map ps p
  : PtrSet.mem p (PtrSet_map map ps) =
    PtrSet.exists_ (compose (PtrSetFacts.eqb p) map) ps.
Proof.
Admitted.

Lemma PtrPairSet_map_spec
      map pps pp
  : PtrPairSet.mem pp (PtrPairSet_map map pps) =
    PtrPairSet.exists_ (compose (PtrPairSetFacts.eqb pp) map) pps.
Proof.
Admitted.

Lemma ValueTPairSet_map_spec
      map vps vp
  : ValueTPairSet.mem vp (ValueTPairSet_map map vps) =
    ValueTPairSet.exists_ (compose (ValueTPairSetFacts.eqb vp) map) vps.
Proof.
Admitted.

Lemma ExprPairSet_map_spec
      map eps ep
  : ExprPairSet.mem ep (ExprPairSet_map map eps) =
    ExprPairSet.exists_ (compose (ExprPairSetFacts.eqb ep) map) eps.
Proof.
Admitted.

Lemma IdTSet_exists_filter
      pred1 pred2 ids
  : IdTSet.exists_ pred1 (IdTSet.filter pred2 ids) =
    IdTSet.exists_ (fun x => andb (pred1 x) (pred2 x)) ids.
Proof.
Admitted.

Lemma PtrSet_exists_filter
      pred1 pred2 ps
  : PtrSet.exists_ pred1 (PtrSet.filter pred2 ps) =
    PtrSet.exists_ (fun x => andb (pred1 x) (pred2 x)) ps.
Proof.
Admitted.

Lemma PtrPairSet_exists_filter
      pred1 pred2 pps
  : PtrPairSet.exists_ pred1 (PtrPairSet.filter pred2 pps) =
    PtrPairSet.exists_ (fun x => andb (pred1 x) (pred2 x)) pps.
Proof.
Admitted.

Lemma ValueTPairSet_exists_filter
      pred1 pred2 vps
  : ValueTPairSet.exists_ pred1 (ValueTPairSet.filter pred2 vps) =
    ValueTPairSet.exists_ (fun x => andb (pred1 x) (pred2 x)) vps.
Proof.
Admitted.

Lemma ExprPairSet_exists_filter
      pred1 pred2 eps
  : ExprPairSet.exists_ pred1 (ExprPairSet.filter pred2 eps) =
    ExprPairSet.exists_ (fun x => andb (pred1 x) (pred2 x)) eps.
Proof.
Admitted.

Lemma previousified_sem_valueT_in_new_invst
      conf st invst0 v
      (NOPREV : LiftPred.ValueT Snapshot.IdT v = false)
  : <<X: InvState.Unary.sem_valueT conf st invst0 v =
         InvState.Unary.sem_valueT conf st
                                   {| InvState.Unary.previous := Locals (EC st);
                                      InvState.Unary.ghost := InvState.Unary.ghost invst0 |}
                                   (Previousify.ValueT v)>>.
Proof.
  destruct v; ss.
  destruct x as [xtag x]. ss.
  unfold Snapshot.IdT in *.
  destruct xtag; ss.
Qed.

Lemma previousified_sem_expr_in_new_invst
      conf st invst0 e
      (NOPREV : LiftPred.Expr Snapshot.IdT e = false)
  : <<X: InvState.Unary.sem_expr conf st invst0 e =
         InvState.Unary.sem_expr conf st
                                 {| InvState.Unary.previous := Locals (EC st);
                                    InvState.Unary.ghost := InvState.Unary.ghost invst0 |}
                                 (Previousify.Expr e)>>.
Proof.
  (* TODO: use all_once *)
  Ltac solve_double :=
    match goal with
    | [v: ValueT.t, w:ValueT.t |- _] =>
      match goal with
      | [Hv: LiftPred.ValueT Snapshot.IdT v = false,
             Hw: LiftPred.ValueT Snapshot.IdT w = false |- _] =>
        let EQv := fresh "EQv" in
        let EQw := fresh "EQw" in
        exploit previousified_sem_valueT_in_new_invst; try exact Hv; intro EQv; des; rewrite EQv;
        exploit previousified_sem_valueT_in_new_invst; try exact Hw; intro EQw; des; rewrite EQw
      end
    end.
  Ltac solve_single :=
    match goal with
    | [v: ValueT.t |- _] =>
      match goal with
      | [Hv: LiftPred.ValueT Snapshot.IdT v = false |- _] =>
        let EQv := fresh "EQv" in
        exploit previousified_sem_valueT_in_new_invst; try exact Hv; intro EQv; des; rewrite EQv
      end
    end.

  destruct e; unfold LiftPred.Expr in *; try solve_des_bool; ss;
    try (solve_double; congruence; fail);
    try (solve_single;congruence; fail).
  - admit. (* gep *)
  - admit. (* select *)
Admitted.

Lemma snapshot_unary_sound
      conf st invst0 invmem inv0
      (STATE: InvState.Unary.sem conf st invst0 invmem inv0)
  :
    exists invst1,
      <<STATE: InvState.Unary.sem conf st invst1 invmem (Snapshot.unary inv0)>> /\
      <<PREV: snapshot_previous st invst1>> /\
      <<GHOST: snapshot_ghost invst0 invst1>>.
Proof.
  exists (InvState.Unary.mk st.(EC).(Locals) invst0.(InvState.Unary.ghost)).
  splits; ss.
  inv STATE.
  econs; ss.
  - intros ep. ii.
    solve_set_union.
    + destruct ep as [e1 e2].
      apply physical_previous_lessdef_spec in IN. des.
      { subst; ss.
        solve_sem_idT.
        esplits; [eauto|reflexivity].
      }
      { subst; ss.
        solve_sem_idT.
        esplits; [eauto|reflexivity].
      }
    + destruct ep as [e1 e2].
      unfold Snapshot.ExprPairSet in IN. ss.
      solve_set_union.
      { solve_in_filter.
        solve_negb_liftpred.
        exploit LESSDEF; eauto.
        { ss.
          erewrite expr_no_prev_sem_preserved; eauto.
        }
        i. des.
        esplits; eauto.
        erewrite expr_no_prev_sem_preserved; eauto.
      }
      { 
        match goal with
        | [H: ExprPairSet.In _ (ExprPairSet_map _ (ExprPairSet.filter _ _)) |- _] =>
          apply ExprPairSetFacts.mem_iff in H; rewrite ExprPairSet_map_spec in H;
            rewrite ExprPairSet_exists_filter in H; apply ExprPairSetFacts.exists_iff in H; solve_compat_bool;
              destruct H as [[e01 e02]]; des
        end.
        solve_des_bool.
        solve_negb_liftpred.
        unfold compose, ExprPairSetFacts.eqb, Previousify.ExprPair in *.
        des_ifs.
        rewrite <- previousified_sem_expr_in_new_invst in *; eauto.
        exploit LESSDEF; eauto.
      }
  - clear -NOALIAS.
    inv NOALIAS.
    econs.
    + i. ss.
      unfold Snapshot.diffblock in *.
      solve_set_union.
      { rewrite ValueTPairSetFacts.filter_b in MEM; [|solve_compat_bool].
        simtac.
        solve_negb_liftpred.
        exploit DIFFBLOCK; eauto.
        - erewrite valueT_no_prev_sem_preserved in *; eauto.
        - erewrite valueT_no_prev_sem_preserved in *; eauto.
      }
      { match goal with
        | [H: ValueTPairSet.mem _ (ValueTPairSet_map _ (ValueTPairSet.filter _ _)) = _ |- _] =>
          rewrite ValueTPairSet_map_spec in H;
            rewrite ValueTPairSet_exists_filter in H; apply ValueTPairSetFacts.exists_iff in H; [| solve_compat_bool];
              destruct H as [[val01 val02]]; des
        end.
        exploit ValueTPairSet.mem_1; eauto. i.
        simtac.
        solve_negb_liftpred.
        unfold compose, ValueTPairSetFacts.eqb, Previousify.ValueTPair in *.
        des_ifs.
        rewrite <- previousified_sem_valueT_in_new_invst in *; eauto.
      }
    + i. ss.
      unfold Snapshot.noalias in *.
      solve_set_union.
      { rewrite PtrPairSetFacts.filter_b in MEM; [|solve_compat_bool].
        simtac.
        solve_negb_liftpred.
        exploit NOALIAS0; eauto.
        - erewrite valueT_no_prev_sem_preserved in *; eauto.
        - erewrite valueT_no_prev_sem_preserved in *; eauto.
      }
      { match goal with
        | [H: PtrPairSet.mem _ (PtrPairSet_map _ (PtrPairSet.filter _ _)) = _ |- _] =>
          rewrite PtrPairSet_map_spec in H;
            rewrite PtrPairSet_exists_filter in H; apply PtrPairSetFacts.exists_iff in H; [| solve_compat_bool];
              destruct H as [[ptr01 ptr02]]; des
        end.
        exploit PtrPairSet.mem_1; eauto. i.
        simtac.
        solve_negb_liftpred.
        unfold compose, PtrPairSetFacts.eqb, Previousify.PtrPair in *.
        des_ifs. ss.
        rewrite <- previousified_sem_valueT_in_new_invst in *; eauto.
      }
  - ii.
    exploit UNIQUE; eauto. intros UNIQUE_SEM.
    inv UNIQUE_SEM. econs; eauto.
  - ii.
    unfold Snapshot.IdTSet in *.
    match goal with
    | [H: ExprPairSet.In _ (ExprPairSet.union _ _) |- _] =>
      let IN := fresh "IN" in
      apply ExprPairSet.union_1 in H; destruct H as [IN|IN]
    | [H: ?is_true (ValueTPairSet.mem _ (ValueTPairSet.union _ _)) |- _] =>
      unfold is_true in H;
        rewrite ValueTPairSetFacts.union_b in H; solve_des_bool
    | [H: ?is_true (PtrPairSet.mem _ (PtrPairSet.union _ _)) |- _] =>
      unfold is_true in H;
        rewrite PtrPairSetFacts.union_b in H; solve_des_bool
    | [H: IdTSet.In _ (IdTSet.union _ _) |- _] =>
      let IN := fresh "IN" in
      apply IdTSet.union_1 in H; destruct H as [IN|IN]
    end. (*    solve_set_union *)
    { apply IdTSetFacts.filter_iff in IN; [|solve_compat_bool]. des.
      unfold compose, Snapshot.IdT in *.
      simtac.
      destruct x as [xtag x]. ss. clear COND.
      destruct xtag; ss.
      - exploit PRIVATE; eauto.
      - exploit PRIVATE; eauto.
    }
    { match goal with
      | [H: IdTSet.In _ (IdTSet_map _ (IdTSet.filter _ _)) |- _] =>
        apply IdTSetFacts.mem_iff in H; rewrite IdTSet_map_spec in H;
          rewrite IdTSet_exists_filter in H; apply IdTSetFacts.exists_iff in H; [| solve_compat_bool];
            destruct H as [[xtag xid]]; des
      end.
      unfold compose, Snapshot.IdT, Previousify.IdT, IdTSetFacts.eqb in *. ss.
      simtac. clear COND COND0.
      destruct xtag; ss.
      - exploit PRIVATE; eauto.
      - exploit PRIVATE; eauto.
    }
Qed.

Lemma snapshot_maydiff_spec
      id md:
  IdTSet.mem id (Snapshot.IdTSet md) =
  if Tag.eq_dec id.(fst) (Tag.previous:Tag.t)
  then IdTSet.mem ((Tag.physical:Tag.t), id.(snd)) md
  else IdTSet.mem id md.
Proof.
  unfold Snapshot.IdTSet, compose.
  rewrite IdTSetFacts.union_b.
  rewrite IdTSetFacts.filter_b; [|solve_compat_bool].
  rewrite IdTSet_map_spec. unfold compose.
  
  
  rewrite IdTSet_exists_filter.
  destruct id. destruct t; ss.
  - match goal with
    | [_:_ |- _ = ?rhs] =>
      destruct rhs; ss
    end.
    match goal with
    | [_:_ |- ?lhs = _] =>
      destruct lhs eqn:LHS; ss
    end.
    apply IdTSetFacts.exists_iff in LHS; [| solve_compat_bool].
    inv LHS. destruct x as [xtag x]. des.
    unfold IdTSetFacts.eqb in *. simtac.
    destruct xtag; ss.
  - rewrite andb_false_r. ss.
    match goal with
    | [_:_ |- _ = ?rhs] =>
      destruct rhs eqn:RHS; ss
    end.
    + apply IdTSetFacts.exists_iff; [solve_compat_bool|].
      unfold IdTSet.Exists.
      esplits.
      { apply IdTSetFacts.mem_iff; eauto. }
      ss. unfold Previousify.IdT, IdTSetFacts.eqb. ss.
      des_ifs.
    + assert (NONEXIST: ~ IdTSet.Exists (fun x => IdTSetFacts.eqb (Tag.previous, i0) (Previousify.IdT x) && negb (Snapshot.IdT x)) md).
      { ii. unfold IdTSet.Exists in *. des.
        destruct x as [xtag x].
        unfold is_true, IdTSetFacts.eqb, Previousify.IdT in *.
        simtac.
        destruct xtag; ss.
        inversion e. subst.
        apply IdTSetFacts.mem_iff in H. clarify.
      }
      match goal with
      | [_:_ |- ?lhs = _] =>
        destruct lhs eqn:LHS; ss
      end.
      exfalso. apply NONEXIST. apply IdTSetFacts.exists_iff; eauto. solve_compat_bool.
  - rewrite andb_true_r.
    match goal with
    | [_:_ |- _ || ?lhs2 = _] =>
      destruct lhs2 eqn:LHS2; ss
    end.
    + apply IdTSetFacts.exists_iff in LHS2; [| solve_compat_bool].
      inv LHS2. destruct x as [xtag x]. des. simtac.
      unfold Previousify.IdT, IdTSetFacts.eqb, Previousify.Tag, Snapshot.IdT in *. ss.
      des_ifs.
      apply IdTSetFacts.mem_iff in H. rewrite -> H. eauto.
    + rewrite orb_false_r. eauto.
Qed.

Lemma snapshot_sound
      conf_src conf_tgt st_src st_tgt invst0 invmem inv0
      (STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst0 invmem inv0):
  exists invst1,
    <<STATE: InvState.Rel.sem conf_src conf_tgt st_src st_tgt invst1 invmem (Snapshot.t inv0)>> /\
    <<PREV_SRC: snapshot_previous st_src invst1.(InvState.Rel.src)>> /\
    <<PREV_TGT: snapshot_previous st_tgt invst1.(InvState.Rel.tgt)>>.
Proof.
  inv STATE.
  apply snapshot_unary_sound in SRC. des.
  apply snapshot_unary_sound in TGT. des.
  exists (InvState.Rel.mk invst1 invst2).
  esplits.
  - econs; ss.
    i. destruct id0.
    rewrite snapshot_maydiff_spec in NOTIN. destruct t; ss.
    * hexploit MAYDIFF; eauto.
    * hexploit MAYDIFF; eauto. i.
      ii. ss.
      exploit PREV; eauto. i. des.
      exploit H.
      { unfold InvState.Unary.sem_idT. ss.
        rewrite <- x. eauto.
      }
      i. des.
      esplits; eauto.
      exploit PREV0; eauto.
      i. des.
      rewrite x0; eauto.
    * hexploit MAYDIFF; eauto. i.
      unfold snapshot_ghost in *.
      unfold InvState.Rel.sem_inject in *.
      unfold InvState.Unary.sem_idT in *. ss.
      rewrite <- GHOST. rewrite <- GHOST0. eauto.
  - eauto.
  - eauto.
Qed.
