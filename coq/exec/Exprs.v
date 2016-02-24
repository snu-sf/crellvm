Require Import syntax.
Require Import alist.
Require Import decs.

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

  Definition get_uses (v:t): list id :=
    match v with
    | value_id id => [id]
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
End ValueT.
Hint Resolve ValueT.eq_dec: EqDecDb.
Coercion ValueT.id: IdT.t >-> ValueT.t_.
Coercion ValueT.const: const >-> ValueT.t_.

Module ValueTSet : FSetExtra.WSfun ValueT := FSetExtra.Make ValueT.
Module ValueTSetFacts := WFacts_fun ValueT ValueTSet.

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
      try (apply ott_list_eq_dec.pair_eq_dec);
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
    apply ott_list_eq_dec.pair_eq_dec;
      apply Expr.eq_dec.
  Defined.
End ExprPair.
Hint Resolve ExprPair.eq_dec: EqDecDb.

Module ExprPairSet : FSetExtra.WSfun ExprPair := FSetExtra.Make ExprPair.
Module ExprPairSetFacts := WFacts_fun ExprPair ExprPairSet.
