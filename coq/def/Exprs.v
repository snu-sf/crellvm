Require Import syntax.
Require Import alist.
Require Import Decs.

Require Import Metatheory.
Import LLVMsyntax.

Require Import sflib.

Require Import TODO.

Set Implicit Arguments.


Module MSetAVLExtra (E: Orders.OrderedType).
  (* Require Import MSets.MSetRBT. *)
  (* MSetRBT.Make. *)
  Include MSetAVL.Make E.
  Definition notin x L := ~ In x L.

End MSetAVLExtra.

Module MSetFactsExtra (E: Orders.OrderedType) (M: MSetInterface.S with Module E := E).
(* Module MSetFactsExtra (E: Orders.OrderedType) (M: (MSetInterface.SetsOn E)). *)

  Include MSetFacts.Facts M.

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
    unfold map. rewrite M.fold_spec, <- fold_left_rev_right.
    rewrite exists_b; cycle 1.
    { ii. unfold eqb, compose.
      destruct (eq_dec ty (f x)), (eq_dec ty (f y)); ss.
      - contradict n. etransitivity; eauto.
      - contradict n. etransitivity; eauto. eapply F; eauto. symmetry. ss.
    }
    rewrite existsb_rev.
    induction (rev (M.elements s)); ss.
    - destruct (M.mem ty M.empty) eqn:X; ss.
      apply M.mem_spec in X. exfalso. eapply M.empty_spec. eauto.
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
          contradict n. symmetry. ss.
        * right. apply IHl0. auto.
  Qed.

End MSetFactsExtra.


(* Default OrderedType is Structures.OrderedType *)
(* https://coq.inria.fr/library/ *)
(* ... OrderedType* are there only for compatibility. *)
Module Tag <: Orders.OrderedType.
  Inductive t_: Set :=
  | physical
  | previous
  | ghost
  .
  Definition t := t_.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
    decide equality.
  Defined.
  Global Program Instance eq_equiv : Equivalence eq.

  Definition is_previous x := match x with Tag.previous => true | _ => false end.
  Definition is_ghost x := match x with Tag.ghost => true | _ => false end.

  (* physical < previous < ghost *)
  Definition ltb (x y: t): bool :=
    match x, y with
    | physical, previous => true
    | physical, ghost => true
    | previous, ghost => true
    | _, _ => false
    end.

  Definition lt: t -> t -> Prop := ltb.

  Definition compare (x y: t): comparison :=
    if(eq_dec x y) then Eq else
      (if (ltb x y) then Lt else Gt)
  .
  
  Lemma compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    ii. destruct x, y; ss; by econs.
  Qed.

  Global Program Instance lt_strorder : StrictOrder lt.
  Next Obligation.
    ii. unfold lt in *. unfold ltb in *. des_ifs.
  Qed.

  Global Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. clarify.
  Qed.
  Next Obligation.
    ii. unfold lt in *. unfold ltb in *. des_ifs.
  Qed.

End Tag.
Hint Resolve Tag.eq_dec: EqDecDb.

Module IdT <: Orders.OrderedType.
  Definition t : Set := (Tag.t * id)%type.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply Tag.eq_dec.
  Qed.

  (* Definition ltb (x y: t): bool := *)
  (*   (Tag.ltb x.(fst) y.(fst)) || (Tag.eq_dec x.(fst) y.(fst) && ltb x.(snd) y.(snd)) *)
  (* . *)

  Global Program Instance eq_equiv : Equivalence eq.

  Definition lt (x y: t): Prop :=
    (Tag.lt x.(fst) y.(fst)) \/ (Tag.eq x.(fst) y.(fst) /\ AtomImpl.lt x.(snd) y.(snd))
  .

  Definition compare (x y: t): comparison :=
    match Tag.compare x.(fst) y.(fst) with
    | Eq => compare x.(snd) y.(snd)
    | Lt => Lt
    | Gt => Gt
    end.
  
  Lemma compare_spec : forall x y : t, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y).
  Proof.
    ii.
    destruct x, y; ss.
    unfold eq, lt. ss.
    unfold compare. ss.
    des_ifs; ss.
    - unfold Tag.compare in *. des_ifs.
      destruct (AtomImpl.compare i0 i1) eqn:T;
        (hexploit compare_spec; eauto; []; rewrite T; intro SPEC; des); inv SPEC.
      + econs; ss.
      + econs. right. split; ss.
      + econs. right. split; ss.
    - (hexploit Tag.compare_spec; eauto; []; rewrite Heq; intro SPEC; des); inv SPEC.
      (* TODO: tactic for compare_spec? like transitivity? *)
      econs; eauto.
    - (hexploit Tag.compare_spec; eauto; []; rewrite Heq; intro SPEC; des); inv SPEC.
      econs; eauto.
  Qed.

  Global Program Instance lt_strorder : StrictOrder lt.
  Next Obligation.
    ii.
    unfold lt in *.
    des.
    - generalize Tag.lt_strorder; intro ORDER. inv ORDER.
      eapply StrictOrder_Irreflexive; eauto.
    - generalize AtomImpl.lt_strorder; intro ORDER. inv ORDER.
      eapply StrictOrder_Irreflexive; eauto.
  Qed.

  Global Program Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
  Next Obligation.
    ii. unfold eq in *. clarify.
  Qed.
  Next Obligation.
    ii. unfold lt in *.
    destruct x, y, z; ss.
    destruct H.
    - destruct H0.
      + left. etransitivity; eauto.
      + des. unfold Tag.eq in *. clarify.
        left. ss.
    - unfold Tag.eq in *. des; subst.
      + left. ss.
      +  right. split; ss.
         etransitivity; eauto.
  Qed.

  Definition lift (tag:Tag.t) (i:id): t := (tag, i).
End IdT.

Hint Resolve IdT.eq_dec: EqDecDb.


(* Module IdTSet : FSetExtra.WSfun IdT := FSetExtra.Make IdT. *)
(* Module IdTSetFacts := WFacts_fun2 IdT IdTSet. *)

Print MSetInterface.
Print MSetInterface.S.
Module IdTSet := MSetAVLExtra IdT. (* TODO: I want to specify type here *)
(* "MSetInterface.S with Module E := IdT" dosen't work *)
Module IdTSetFacts := MSetFactsExtra IdT IdTSet.

Lemma IdTSet_from_list_spec ids:
  forall id, IdTSet.mem id (IdTSetFacts.from_list ids) <-> In id ids.
Proof.
  i. rewrite IdTSetFacts.from_list_spec. apply InA_iff_In.
Qed.

Module Value.
  Definition t := value.

  Definition get_ids(v: t): option id :=
    match v with
      | value_id i => Some i
      | value_const _ => None
    end.
End Value.

Module ValueT <: UsualDecidableType.
  Inductive t_: Set :=
  | id (x:IdT.t)
  | const (c:const)
  .
  Definition t:= t_.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply IdT.eq_dec.
    apply const_dec.
  Qed.

  Definition lift (tag:Tag.t) (v:value): t :=
    match v with
    | value_id i => id (IdT.lift tag i)
    | value_const c => const c
    end.

  Definition get_idTs (v: t): option IdT.t :=
    match v with
      | id i => Some i
      | const _ => None
    end.
End ValueT.
Hint Resolve ValueT.eq_dec: EqDecDb.
Coercion ValueT.id: IdT.t >-> ValueT.t_.
Coercion ValueT.const: const >-> ValueT.t_.

Module ValueTSet : FSetExtra.WSfun ValueT := FSetExtra.Make ValueT.
Module ValueTSetFacts := WFacts_fun2 ValueT ValueTSet.

(* TODO: universal construction? *)
Module ValueTPair <: UsualDecidableType.
  Definition t := (ValueT.t * ValueT.t)%type.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    apply prod_dec;
    apply ValueT.eq_dec.
  Defined.

  Definition get_idTs (vp: t): list IdT.t :=
    (option_to_list (ValueT.get_idTs vp.(fst)))
      ++ (option_to_list (ValueT.get_idTs vp.(snd))).
End ValueTPair.
Hint Resolve ValueTPair.eq_dec: EqDecDb.

Module ValueTPairSet : FSetExtra.WSfun ValueTPair := FSetExtra.Make ValueTPair.
Module ValueTPairSetFacts := WFacts_fun2 ValueTPair ValueTPairSet.

Module Expr <: UsualDecidableType.
  Inductive t_: Set :=
  | bop (b:bop) (s:sz) (v:ValueT.t) (w:ValueT.t)
  | fbop (fb:fbop) (fp:floating_point) (v:ValueT.t) (w:ValueT.t)
  | extractvalue (t:typ) (v:ValueT.t) (lc:list const) (u:typ)
  | insertvalue (t:typ) (v:ValueT.t) (u:typ) (w:ValueT.t) (lc:list const)
  | gep (ib:inbounds) (t:typ) (v:ValueT.t) (lsv:list (sz * ValueT.t)) (u:typ)
  | trunc (top:truncop) (t:typ) (v:ValueT.t) (u:typ)
  | ext (eop:extop) (t:typ) (v:ValueT.t) (u:typ)
  | cast (cop:castop) (t:typ) (v:ValueT.t) (u:typ)
  | icmp (c:cond) (t:typ) (v:ValueT.t) (w:ValueT.t)
  | fcmp (fc:fcond) (fp:floating_point) (v:ValueT.t) (w:ValueT.t)
  | select (v:ValueT.t) (t:typ) (w:ValueT.t) (z:ValueT.t)
  | value (v:ValueT.t)
  | load (v:ValueT.t) (t:typ) (a:align)
  .
  Definition t := t_.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    decide equality;
      try (apply list_eq_dec);
      try (apply prod_dec);
      try (apply IdT.eq_dec);
      try (apply ValueT.eq_dec);
      try (apply id_dec);
      try (apply Tag.eq_dec);
      try (apply sz_dec);
      try (apply bop_dec);
      try (apply fbop_dec);
      try (apply floating_point_dec);
      try (apply typ_dec);
      try (apply const_dec);
      try (apply inbounds_dec);
      try (apply truncop_dec);
      try (apply extop_dec);
      try (apply castop_dec);
      try (apply cond_dec);
      try (apply fcond_dec).
  Defined.

  Definition get_valueTs (e: t): list ValueT.t :=
    match e with
      | (Expr.bop _ _ v1 v2) => [v1 ; v2]
      | (Expr.fbop _ _ v1 v2) => [v1 ; v2]
      | (Expr.extractvalue _ v _ _) => [v]
      | (Expr.insertvalue _ v1 _ v2 _) => [v1 ; v2]
      | (Expr.gep _ _ v vl _) => v :: (List.map snd vl)
      | (Expr.trunc _ _ v _) => [v]
      | (Expr.ext _ _ v _) => [v]
      | (Expr.cast _ _ v _) => [v]
      | (Expr.icmp _ _ v1 v2) => [v1 ; v2]
      | (Expr.fcmp _ _ v1 v2) => [v1 ; v2]
      | (Expr.select v1 _ v2 v3) => [v1 ; v2 ; v3]
      | (Expr.value v) => [v]
      | (Expr.load v _ _) => [v]
    end.

  Definition same_modulo_value (e1 e2:Expr.t): bool :=
    match e1, e2 with
    | Expr.bop b1 s1 v1 w1, Expr.bop b2 s2 v2 w2 =>
      (bop_dec b1 b2)
        && (sz_dec s1 s2)
    | Expr.fbop fb1 fp1 v1 w1, Expr.fbop fb2 fp2 v2 w2 =>
      (fbop_dec fb1 fb2)
        && (floating_point_dec fp1 fp2)
    | Expr.extractvalue t1 v1 lc1 u1, Expr.extractvalue t2 v2 lc2 u2 =>
      (typ_dec t1 t2)
        && (list_forallb2 const_eqb lc1 lc2)
        && (typ_dec u1 u2)
    | Expr.insertvalue t1 v1 t'1 v'1 lc1, Expr.insertvalue t2 v2 t'2 v'2 lc2 =>
      (typ_dec t1 t2)
        && (typ_dec t'1 t'2)
        && (list_forallb2 const_eqb lc1 lc2)
    | Expr.gep ib1 t1 v1 lsv1 u1, Expr.gep ib2 t2 v2 lsv2 u2 =>
      (inbounds_dec ib1 ib2)
        && (typ_dec t1 t2)
        && (list_eq_dec sz_dec
                        (List.map fst lsv1)
                        (List.map fst lsv2))
        && (typ_dec u1 u2)
    | Expr.trunc top1 t1 v1 u1, Expr.trunc top2 t2 v2 u2 =>
      (truncop_dec top1 top2)
        && (typ_dec t1 t2)
        && (typ_dec u1 u2)
    | Expr.ext eop1 t1 v1 u1, Expr.ext eop2 t2 v2 u2 =>
      (extop_dec eop1 eop2)
        && (typ_dec t1 t2)
        && (typ_dec u1 u2)
    | Expr.cast cop1 t1 v1 u1, Expr.cast cop2 t2 v2 u2 =>
      (castop_dec cop1 cop2)
        && (typ_dec t1 t2)
        && (typ_dec u1 u2)
    | Expr.icmp c1 t1 v1 w1, Expr.icmp c2 t2 v2 w2  =>
      (cond_dec c1 c2)
        && (typ_dec t1 t2)
    | Expr.fcmp fc1 fp1 v1 w1, Expr.fcmp fc2 fp2 v2 w2  =>
      (fcond_dec fc1 fc2)
        && (floating_point_dec fp1 fp2)
    | Expr.select v1 t1 w1 z1, Expr.select v2 t2 w2 z2 =>
      (typ_dec t1 t2)
    | Expr.value v1, Expr.value v2 =>
      true
    | Expr.load v1 t1 a1, Expr.load v2 t2 a2 =>
      (typ_dec t1 t2)
        && (Decs.align_dec a1 a2)
    | _, _ => false
    end.

  Definition get_idTs (e: t): list IdT.t :=
    TODO.filter_map ValueT.get_idTs (get_valueTs e).

  Definition map_valueTs (e: t) (f: ValueT.t -> ValueT.t): t :=
    match e with
    | (Expr.bop _blah _blah2 v1 v2) =>
      Expr.bop _blah _blah2 (f v1) (f v2)
    | (Expr.fbop _blah _blah2 v1 v2) =>
      Expr.fbop _blah _blah2 (f v1) (f v2)
    | (Expr.extractvalue _blah v _blah2 _blah3) =>
      (Expr.extractvalue _blah (f v) _blah2 _blah3)
    | (Expr.insertvalue _blah v1 _blah2 v2 _blah3) =>
      (Expr.insertvalue _blah (f v1) _blah2 (f v2) _blah3)
    | (Expr.gep _blah _blah2 v vl _blah3) =>
      (Expr.gep _blah _blah2 (f v)
                (List.map (fun x => (fst x, (f (snd x)))) vl) _blah3)
    | (Expr.trunc _blah _blah2 v _blah3) =>
      (Expr.trunc _blah _blah2 (f v) _blah3)
    | (Expr.ext _blah _blah2 v _blah3) =>
      (Expr.ext _blah _blah2 (f v) _blah3)
    | (Expr.cast _blah _blah2 v _blah3) =>
      (Expr.cast _blah _blah2 (f v) _blah3)
    | (Expr.icmp _blah _blah2 v1 v2) =>
      (Expr.icmp _blah _blah2 (f v1) (f v2))
    | (Expr.fcmp _blah _blah2 v1 v2) =>
      (Expr.fcmp _blah _blah2 (f v1) (f v2))
    | (Expr.select v1 _blah v2 v3) =>
      (Expr.select (f v1) _blah (f v2) (f v3))
    | (Expr.value v) =>
      (Expr.value (f v))
    | (Expr.load v _blah _blah2) =>
      (Expr.load (f v) _blah _blah2)
    end.

End Expr.
Hint Resolve Expr.eq_dec: EqDecDb.
Coercion Expr.value: ValueT.t >-> Expr.t_.

(* TODO: universal construction? *)
Module ExprPair <: UsualDecidableType.
  Definition t := (Expr.t * Expr.t)%type.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    apply prod_dec;
      apply Expr.eq_dec.
  Defined.

  Definition get_idTs (ep: t): list IdT.t :=
    (Expr.get_idTs ep.(fst))
      ++ (Expr.get_idTs ep.(snd)).
End ExprPair.
Hint Resolve ExprPair.eq_dec: EqDecDb.

Module ExprPairSet : FSetExtra.WSfun ExprPair := FSetExtra.Make ExprPair.
Module ExprPairSetFacts := WFacts_fun2 ExprPair ExprPairSet.

(* Ptr: alias related values *)
Module Ptr <: UsualDecidableType.
  (* typ has the type of the 'pointer', not the type of the 'object'.
     ex: %x = load i32* %y, align 4 <- (id y, typ_pointer (typ_int 32))
                   ^^^^
  *)
  Definition t := (ValueT.t * typ)%type.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    apply prod_dec.
    apply ValueT.eq_dec.
    apply typ_dec.
  Defined.
  Definition get_idTs (p: t): option IdT.t :=
    match p with
    | (v,_) => ValueT.get_idTs v
    end.
End Ptr.

Module PtrSet : FSetExtra.WSfun Ptr := FSetExtra.Make Ptr.
Module PtrSetFacts := WFacts_fun2 Ptr PtrSet.

Lemma PtrSet_from_list_spec ps:
  forall p, PtrSet.mem p (PtrSetFacts.from_list ps) <-> In p ps.
Proof.
  i. rewrite PtrSetFacts.from_list_spec. apply InA_iff_In.
Qed.

Module PtrPair <: UsualDecidableType.
  Definition t := (Ptr.t * Ptr.t)%type.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    apply prod_dec; apply Ptr.eq_dec.
  Defined.

  Definition get_idTs (pp: t): list IdT.t :=
    (option_to_list (Ptr.get_idTs pp.(fst)))
      ++ (option_to_list (Ptr.get_idTs pp.(snd))).
End PtrPair.
Hint Resolve PtrPair.eq_dec: EqDecDb.

Module PtrPairSet : FSetExtra.WSfun PtrPair := FSetExtra.Make PtrPair.
Module PtrPairSetFacts := WFacts_fun2 PtrPair PtrPairSet.
