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

  Definition get_ids(v: t): list id :=
    match v with
      | value_id i => [i]
      | value_const _ => []
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

  Definition get_ids (v: t): list LLVMsyntax.id :=
    match v with
      | id (_, i) => [i]
      | const _ => []
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

  Definition get_ids (e: t): list LLVMsyntax.id :=
    List.fold_left (fun s i => ValueT.get_ids i ++ s) (get_valueTs e) [].
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
