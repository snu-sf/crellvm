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
Require Import TODOProof.
Require Import Decs.
Require Import Exprs.
Require Import Validator.
Require Import GenericValues.
Require Import Inject.
Require InvMem.
Require InvState.
Require Import Hints.
Require Import memory_props.
Import Memory.
Require Import opsem_wf.
Require Import genericvalues_inject.
Require Import memory_sim.
Require Import MemAux.
Require Import SoundBase.

Set Implicit Arguments.


Section NONE.

  Lemma subst_none_value
        conf st invst0 x v
        (NONE: InvState.Unary.sem_idT st invst0 x = None)
        val1
        (SEM: InvState.Unary.sem_valueT conf st invst0 v = Some val1)
        y
  :
    <<NO_X: (ValueT.substitute x y v) = v>>
  .
  Proof.
    red.
    destruct v; ss.
    des_ifs.
  Qed.

  Lemma subst_none_list_value
        conf st invst0 x
        (NONE: InvState.Unary.sem_idT st invst0 x = None)
        l0 lsv
        (SEM: InvState.Unary.sem_list_valueT conf st invst0 lsv = Some l0)
        y
    :
      <<NO_X: List.map (fun x0 : sz * ValueT.t => (fst x0, ValueT.substitute x y (snd x0))) lsv = lsv>>
  .
  Proof.
    red.
    ginduction lsv; ii; ss.
    des_ifs. ss.
    repeat erewrite subst_none_value; eauto.
    f_equal.
    eapply IHlsv; eauto.
  Qed.

  Lemma subst_none_expr
        conf st invst0 x e
        (NONE: InvState.Unary.sem_idT st invst0 x = None)
        val1
        (SEM: InvState.Unary.sem_expr conf st invst0 e = Some val1)
        y
    :
      <<NO_X: (Expr.substitute x y e) = e>>
  .
  Proof.
    red.
    destruct e; ss; des_ifs.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
      f_equal.
      erewrite subst_none_list_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
    - ss. repeat erewrite subst_none_value; eauto.
  Qed.

  Lemma subst_none_value_rev
        conf st invst0 y v
        (NONE: InvState.Unary.sem_valueT conf st invst0 y = None)
        x val1
        (SEM: InvState.Unary.sem_valueT conf st invst0 (ValueT.substitute x y v) = Some val1)
  :
    <<NO_X: (ValueT.substitute x y v) = v>>
  .
  Proof.
    red.
    destruct v; ss.
    des_ifs.
  Qed.

  Lemma subst_none_list_value_rev
        conf st invst0 y
        (NONE: InvState.Unary.sem_valueT conf st invst0 y = None)
        l0 lsv x
        (SEM: InvState.Unary.sem_list_valueT
                conf st invst0
                (List.map (fun x0 : sz * ValueT.t => (fst x0, ValueT.substitute x y (snd x0))) lsv) = 
              Some l0)
    :
      <<NO_X: List.map (fun x0 : sz * ValueT.t => (fst x0, ValueT.substitute x y (snd x0))) lsv = lsv>>
  .
  Proof.
    red.
    ginduction lsv; ii; ss.
    des_ifs. destruct a; ss.
    erewrite subst_none_value_rev; eauto.
    f_equal; ss.
    eapply IHlsv; eauto.
  Qed.

  Lemma subst_none_expr_rev
        conf st invst0 y e
        (NONE: InvState.Unary.sem_valueT conf st invst0 y = None)
        x val1
        (SEM: InvState.Unary.sem_expr conf st invst0 (Expr.substitute x y e) = Some val1)
    :
      <<NO_X: (Expr.substitute x y e) = e>>
  .
  Proof.
    red.
    destruct e; ss; des_ifs;
      f_equal; try erewrite subst_none_value_rev; eauto.
    erewrite subst_none_list_value_rev; eauto.
  Qed.

End NONE.



Section SPEC.

  (* TODO: location *)
  Lemma const_eqb_refl_list
        l0
        (IH: Forall (fun a : const => const_eqb a a) l0)
  :
    (fix f (lc1 lc2 : list const) {struct lc1} : bool :=
       match lc1 with
       | [] => match lc2 with
               | [] => true
               | _ :: _ => false
               end
       | hd1 :: tl1 => match lc2 with
                       | [] => false
                       | hd2 :: tl2 => const_eqb hd1 hd2 && f tl1 tl2
                       end
       end) l0 l0
  .
  Proof.
    ginduction l0; ii; ss.
    inv IH.
    rewrite H1; ss.
    eapply IHl0; eauto.
  Qed.

  (* TODO: location *)
  Lemma const_eqb_refl
        a
  :
    <<REFL: const_eqb a a>>
  .
  Proof.
    red.
    induction a using const_ind_gen; ss; unfold proj_sumbool in *; des_ifs; ss;
      repeat (apply andb_true_iff; split; ss);
      try (by eapply const_eqb_refl_list; eauto); ss.
  Qed.

  (* TODO: location *)
  Lemma forallb_const_eqb_refl
        lc
  :
    <<EQ: list_forallb2 const_eqb lc lc = true>>
  .
  Proof.
    red.
    ginduction lc; ii; ss.
    rewrite IHlc; ss.
    unfold proj_sumbool in *.
    apply andb_true_iff; split; ss.
    apply const_eqb_refl; ss.
  Qed.

  Lemma substitute_same_modulo_spec
        e from to
  :
    <<SUBST: Expr.same_modulo_value e (Expr.substitute from to e) = true>>
  .
  Proof.
    red.
    destruct e; ss; unfold proj_sumbool in *; ss; des_ifs; ss.
    - apply andb_true_iff. split; ss.
      apply forallb_const_eqb_refl; ss.
    - apply forallb_const_eqb_refl; ss.
    - clear_tac.
      exfalso. ginduction lsv; ii; ss.
      apply n. f_equal.
      exploit IHlsv; try eassumption.
      { ii. rewrite <- H in *. ss. }
      i; ss.
  Qed.

  (* TODO: location *)
  Lemma map_valueTs_get_valueTs_spec
        f e
    :
      List.map f (Expr.get_valueTs e) = (Expr.get_valueTs (Expr.map_valueTs e f))
  .
  Proof.
    destruct e; ss.
    f_equal.
    clear_tac.
    ginduction lsv; ii; ss.
    f_equal. eauto.
  Qed.

  Lemma substitute_lessdef_spec
        conf st invst0
        (from: IdT.t) (to: ValueT.t)
        (LDFROMTO : InvState.Unary.sem_lessdef conf st invst0 (Expr.value from, Expr.value to))
        e
    :
      Forall2 (fun v1 v2 : ValueT.t =>
                 InvState.Unary.sem_lessdef conf st invst0 (Expr.value v1, Expr.value v2)) 
              (Expr.get_valueTs e) (Expr.get_valueTs (Expr.substitute from to e))
  .
  Proof.
    unfold Expr.substitute.
    rewrite <- map_valueTs_get_valueTs_spec.
    abstr (Expr.get_valueTs e) tt.
    clear_tac.
    ginduction tt; ii; ss.
    econs; eauto.
    ii; ss.
    destruct a; ss.
    - des_ifs.
      + eapply LDFROMTO; eauto.
      + esplits; eauto.
        eapply GVs.lessdef_refl.
    - esplits; eauto.
      eapply GVs.lessdef_refl.
  Qed.

  Lemma substitute_lessdef_spec_rev
        conf st invst0
        (from: IdT.t) (to: ValueT.t)
        (LDFROMTO : InvState.Unary.sem_lessdef conf st invst0 (Expr.value to, Expr.value from))
        e
    :
      Forall2 (fun v1 v2 : ValueT.t =>
                 InvState.Unary.sem_lessdef conf st invst0 (Expr.value v1, Expr.value v2)) 
              (Expr.get_valueTs (Expr.substitute from to e)) (Expr.get_valueTs e)
  .
  Proof.
    unfold Expr.substitute.
    rewrite <- map_valueTs_get_valueTs_spec.
    abstr (Expr.get_valueTs e) tt.
    clear_tac.
    ginduction tt; ii; ss.
    econs; eauto.
    ii; ss.
    destruct a; ss.
    - des_ifs.
      + eapply LDFROMTO; eauto.
      + esplits; eauto.
        eapply GVs.lessdef_refl.
    - esplits; eauto.
      eapply GVs.lessdef_refl.
  Qed.

  (* TODO: location *)
  Lemma same_modulo_value_comm
        a b
        (SAME: Expr.same_modulo_value a b)
    :
      <<SAME: Expr.same_modulo_value b a>>
  (* <<COMM: Expr.same_modulo_value a b = Expr.same_modulo_value b a>> <--- little harder to prove, skip *)
  .
  Proof.
    red.
    destruct a, b; ss; unfold proj_sumbool in *; des_ifs; unfold is_true in *; ss; des_bool; des; clear_tac.
    - apply InvState.Rel.list_forallb_const_eqb in SAME. des. clarify.
      eapply forallb_const_eqb_refl; eauto.
    - ss.
    - apply InvState.Rel.list_forallb_const_eqb in SAME. des. clarify.
      eapply forallb_const_eqb_refl; eauto.
    - rewrite e1 in *. ss.
  Qed.

End SPEC.



Section SOME.

  Lemma substitute_some_id
        conf st from to idt0 invst0 val0 from_gv to_gv
        (FROM: InvState.Unary.sem_idT st invst0 from = Some from_gv)
        (TO: InvState.Unary.sem_valueT conf st invst0 to = Some to_gv)
        (LD: GVs.lessdef from_gv to_gv)
        (SEM: InvState.Unary.sem_idT st invst0 idt0 = Some val0)
  :
    exists val1 : GenericValue,
      <<SEM: InvState.Unary.sem_valueT conf st invst0
                                       (if IdT.eq_dec from idt0 then to else idt0) = Some val1>>
             /\ <<LD: GVs.lessdef val0 val1 >>
  .
  Proof.
    des_ifs.
    - esplits; eauto.
    - esplits; eauto.
      eapply GVs.lessdef_refl.
  Qed.

  Lemma substitute_some_value
        conf st from to v0 invst0 val0 from_gv to_gv
        (FROM: InvState.Unary.sem_idT st invst0 from = Some from_gv)
        (TO: InvState.Unary.sem_valueT conf st invst0 to = Some to_gv)
        (LD: GVs.lessdef from_gv to_gv)
        (SEM: InvState.Unary.sem_valueT conf st invst0 v0 = Some val0)
  :
    exists val1 : GenericValue,
      <<SEM: InvState.Unary.sem_valueT conf st invst0 (ValueT.substitute from to v0) = Some val1 >> /\
             <<LD: GVs.lessdef val0 val1 >>
  .
  Proof.
    destruct v0; ss.
    - eapply substitute_some_id; eauto.
    - esplits; eauto. eapply GVs.lessdef_refl.
  Qed.

  Lemma substitute_some_expr
        conf st from to e invst0 val0 from_gv to_gv
        (FROM: InvState.Unary.sem_idT st invst0 from = Some from_gv)
        (TO: InvState.Unary.sem_valueT conf st invst0 to = Some to_gv)
        (LD: GVs.lessdef from_gv to_gv)
        (SEM: InvState.Unary.sem_expr conf st invst0 e = Some val0)
  :
    exists val1 : GenericValue,
      <<SEM: InvState.Unary.sem_expr conf st invst0 (Expr.substitute from to e) = Some val1 >> /\
             <<LD: GVs.lessdef val0 val1 >>
  .
  Proof.
    eapply InvState.Rel.lessdef_expr_spec3; eauto.
    { eapply substitute_same_modulo_spec; eauto. }
    { assert(LDFROMTO: InvState.Unary.sem_lessdef conf st invst0 (Expr.value from, Expr.value to)).
      { ii; esplits; eauto. ss. rewrite VAL1 in *. clarify. }
      clear - LDFROMTO.
      eapply substitute_lessdef_spec; eauto.
    }
  Qed.

  Lemma substitute_some_expr_rev
        conf st from to e invst0 val0 from_gv to_gv
        (TO: InvState.Unary.sem_valueT conf st invst0 to = Some to_gv)
        (FROM: InvState.Unary.sem_idT st invst0 from = Some from_gv)
        (LD: GVs.lessdef to_gv from_gv)
        (SEM: InvState.Unary.sem_expr conf st invst0 (Expr.substitute from to e) = Some val0)
    :
      exists val1 : GenericValue,
        <<SEM: InvState.Unary.sem_expr conf st invst0 e = Some val1 >> /\ <<LD: GVs.lessdef val0 val1 >>
  .
  Proof.
    eapply InvState.Rel.lessdef_expr_spec3; eauto.
    { rewrite same_modulo_value_comm; ss.
      eapply substitute_same_modulo_spec; eauto. }
    { assert(LDFROMTO: InvState.Unary.sem_lessdef conf st invst0 (Expr.value to, Expr.value from)).
      { ii; esplits; eauto. ss. rewrite VAL1 in *. clarify. }
      clear - LDFROMTO.
      eapply substitute_lessdef_spec_rev; eauto.
    }
  Qed.

End SOME.

Lemma substitute_spec_unary
      conf st x y e pubs gmax
      invst0 invmem0 inv0
      (SEM: InvState.Unary.sem conf st invst0 invmem0 gmax pubs inv0)
      (LD: InvState.Unary.sem_lessdef conf st invst0 
                                      (Exprs.Expr.value (Exprs.ValueT.id x), Exprs.Expr.value y))
  :
    <<SEM: InvState.Unary.sem
             conf st invst0 invmem0 gmax pubs
             (Hints.Invariant.update_lessdef
                (Exprs.ExprPairSet.add (e, Exprs.Expr.substitute x y e)) inv0)>>
.
Proof.
  econs; eauto; try apply SEM.
  inv SEM. clear - LESSDEF LD.
  ii.
  apply Exprs.ExprPairSetFacts.add_iff in H.
  des; cycle 1.
  { eapply LESSDEF; eauto. }
  clear LESSDEF.
  clarify. ss.
  unfold InvState.Unary.sem_lessdef in *.
  ss.
  destruct (InvState.Unary.sem_idT st invst0 x) eqn:T; cycle 1.
  { clear LD.
    solve_leibniz.
    clear - VAL1 T.
    erewrite subst_none_expr; eauto. esplits; eauto. eapply GVs.lessdef_refl.
  }
  specialize (LD g eq_refl). des.
  clear_tac.
  solve_leibniz.
  eapply substitute_some_expr; eauto.
Qed.

Lemma substitute_spec_unary_rev
      conf st x y e pubs gmax
      invst0 invmem0 inv0
      (SEM: InvState.Unary.sem conf st invst0 invmem0 gmax pubs inv0)
      (LD: InvState.Unary.sem_lessdef conf st invst0 
                                      (Exprs.Expr.value y, Exprs.Expr.value (Exprs.ValueT.id x)))
  :
    <<SEM: InvState.Unary.sem
             conf st invst0 invmem0 gmax pubs
             (Hints.Invariant.update_lessdef
                (Exprs.ExprPairSet.add (Exprs.Expr.substitute x y e, e)) inv0)>>
.
Proof.
  econs; eauto; try apply SEM.
  inv SEM. clear - LESSDEF LD.
  ii.
  apply Exprs.ExprPairSetFacts.add_iff in H.
  des; cycle 1.
  { eapply LESSDEF; eauto. }
  clear LESSDEF.
  clarify. ss.
  unfold InvState.Unary.sem_lessdef in *.
  ss.
  destruct (InvState.Unary.sem_valueT conf st invst0 y) eqn:T; cycle 1.
  { clear LD.
    solve_leibniz.
    clear - VAL1 T.
    erewrite subst_none_expr_rev in VAL1; eauto. esplits; eauto. eapply GVs.lessdef_refl.
  }
  specialize (LD g eq_refl). des.
  clear_tac.
  solve_leibniz.
  eapply substitute_some_expr_rev; eauto.
Qed.

