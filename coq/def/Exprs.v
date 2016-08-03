Require Import syntax.
Require Import alist.
Require Import Decs.

Require Import Metatheory.
Import LLVMsyntax.

Require Import sflib.

Require Import TODO.

Set Implicit Arguments.

Module Tag <: UsualDecidableType.
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
End Tag.
Hint Resolve Tag.eq_dec: EqDecDb.

Module IdT <: UsualDecidableType.
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

  Definition lift (tag:Tag.t) (i:id): t := (tag, i).
End IdT.
Hint Resolve IdT.eq_dec: EqDecDb.

Module IdTSet : FSetExtra.WSfun IdT := FSetExtra.Make IdT.
Module IdTSetFacts := WFacts_fun IdT IdTSet.

(* TODO: move *)
Definition AtomSetImpl_from_list
           (ids:list id): AtomSetImpl.t :=
  fold_left (flip AtomSetImpl.add) ids AtomSetImpl.empty.

(* TODO: move *)
Definition IdTSet_from_list
           (ids:list IdT.t): IdTSet.t :=
  fold_left (flip IdTSet.add) ids IdTSet.empty.

Lemma IdTSet_from_list_spec ids:
  forall id, IdTSet.mem id (IdTSet_from_list ids) <-> In id ids.
Proof.
  unfold IdTSet_from_list. rewrite <- fold_left_rev_right.
  intros. rewrite in_rev.
  match goal with
  | [|- context[@rev ?T ?ids]] => induction (@rev T ids)
  end; simpl.
  - rewrite IdTSetFacts.empty_b. intuition.
  - unfold flip in *. rewrite IdTSetFacts.add_b.
    unfold IdTSetFacts.eqb. constructor; intros.
    + apply orb_true_iff in H. destruct H.
      * left. destruct (IdT.eq_dec a id0); intuition.
      * right. apply IHl0. auto.
    + apply orb_true_intro. destruct H.
      * subst. destruct (IdT.eq_dec id0 id0); auto.
      * right. apply IHl0. auto.
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
Module ValueTSetFacts := WFacts_fun ValueT ValueTSet.

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
End ValueTPair.
Hint Resolve ValueTPair.eq_dec: EqDecDb.

Module ValueTPairSet : FSetExtra.WSfun ValueTPair := FSetExtra.Make ValueTPair.
Module ValueTPairSetFacts := WFacts_fun ValueTPair ValueTPairSet.

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
End ExprPair.
Hint Resolve ExprPair.eq_dec: EqDecDb.

Module ExprPairSet : FSetExtra.WSfun ExprPair := FSetExtra.Make ExprPair.
Module ExprPairSetFacts := WFacts_fun ExprPair ExprPairSet.

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

Module PtrSet: FSetExtra.WSfun Ptr := FSetExtra.Make Ptr.
Module PtrSetFacts := WFacts_fun Ptr PtrSet.

(* TODO: move *)
Definition PtrSet_from_list
           (ps:list Ptr.t): PtrSet.t :=
  fold_left (flip PtrSet.add) ps PtrSet.empty.

Lemma PtrSet_from_list_spec ps:
  forall p, PtrSet.mem p (PtrSet_from_list ps) <-> In p ps.
Proof.
  unfold PtrSet_from_list. rewrite <- fold_left_rev_right.
  intros. rewrite in_rev.
  match goal with
  | [|- context[@rev ?T ?ps]] => induction (@rev T ps)
  end; simpl.
  - rewrite PtrSetFacts.empty_b. intuition.
  - unfold flip in *. rewrite PtrSetFacts.add_b.
    unfold PtrSetFacts.eqb. constructor; intros.
    + apply orb_true_iff in H. destruct H.
      * left. destruct (Ptr.eq_dec a p); intuition.
      * right. apply IHl0. auto.
    + apply orb_true_intro. destruct H.
      * subst. destruct (Ptr.eq_dec p p); auto.
      * right. apply IHl0. auto.
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
End PtrPair.
Hint Resolve PtrPair.eq_dec: EqDecDb.

Module PtrPairSet: FSetExtra.WSfun PtrPair := FSetExtra.Make PtrPair.
Module PtrPairSetFacts := WFacts_fun PtrPair PtrPairSet.
