Require Import syntax.
Require Import alist.
Require Import Decs.

Require Import Metatheory.
Import LLVMsyntax.

Require Import sflib.

Require Import TODO.
Require Import Ords.

Set Implicit Arguments.

Local Open Scope OrdIdx_scope.

(* TODO: Move to Ords.v *)
Module Backport_Alt (E: OrdersAlt.OrderedTypeAlt) <: OrderedType.OrderedType.
  Module OT := (OrdersAlt.OT_from_Alt E).
  Include (OrdersAlt.Backport_OT OT).
End Backport_Alt.

(* TODO: move to Ords.v *)
Module prod (E1 E2: AltUsual) <: AltUsual.

  Definition t : Type := E1.t * E2.t.

  Definition compare (x y: t): comparison :=
    lexico_order [fun _ => E1.compare (fst x) (fst y) ; fun _ => E2.compare (snd x) (snd y)].

  Lemma compare_sym
        x y
    :
      <<SYM: compare y x = CompOpp (compare x y)>>
  .
  Proof.
    destruct x as [x1 x2], y as [y1 y2]. unfold compare. red.
    specialize (E1.compare_sym x1 y1). intro SYM_E1.
    specialize (E2.compare_sym x2 y2). intro SYM_E2.
    ss. des_ifs.
  Qed.

  Lemma leibniz_compare_eq1 x
    : E1.compare x x = Eq.
  Proof.
    specialize (E1.compare_sym x x). i.
    destruct (E1.compare x x) eqn:COMP; ss.
  Qed.

  Lemma leibniz_compare_eq2 x
    : E2.compare x x = Eq.
  Proof.
    specialize (E2.compare_sym x x). i.
    destruct (E2.compare x x) eqn:COMP; ss.
  Qed.

  Lemma compare_trans: forall
      c x y z (* for compatibility with Alt *)
      (XY: compare x y = c)
      (YZ: compare y z = c)
    ,
      <<XZ: compare x z = c>>
  .
  Proof.
    i. destruct x as [x1 x2], y as [y1 y2], z as [z1 z2].
    unfold compare in *. red.
    specialize (@E1.compare_trans c x1 y1 z1). intro TR_E1.
    specialize (@E2.compare_trans c x2 y2 z2). intro TR_E2.
    ss. des_ifs;
          try (by exploit TR_E1; eauto);
          try (by exploit TR_E2; eauto);
      repeat match goal with
             | [H: E1.compare ?a ?b = Eq |- _] =>
               specialize (E1.compare_leibniz H); i; []; subst; clear H
             | [H: E2.compare ?a ?b = Eq |- _] =>
               specialize (E2.compare_leibniz H); i; []; subst; clear H
             | [H: E1.compare ?a ?a = Lt |- _] =>
               rewrite leibniz_compare_eq1 in H
             | [H: E1.compare ?a ?a = Gt |- _] =>
               rewrite leibniz_compare_eq1 in H
             | [H: E2.compare ?a ?a = Lt |- _] =>
               rewrite leibniz_compare_eq2 in H
             | [H: E2.compare ?a ?a = Gt |- _] =>
               rewrite leibniz_compare_eq2 in H
      end; try congruence.
  Qed.

  Lemma compare_leibniz: forall
      x y
      (EQ: compare x y = Eq)
    ,
      x = y
  .
  Proof.
    destruct x, y; ss. unfold compare. i. ss. des_ifs.
    f_equal.
    - apply E1.compare_leibniz; ss.
    - apply E2.compare_leibniz; ss.
  Qed.

End prod.




Module Tag <: AltUsual.
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

  (* Definition lt: t -> t -> Prop := ltb. *)

  Definition compare (x y: t): comparison :=
    if(eq_dec x y) then Eq else
      (if (ltb x y) then Lt else Gt)
  .

  Lemma compare_sym : forall x y : t, << SYM: compare y x = CompOpp (compare x y) >>.
  Proof. destruct x, y; ss. Qed.

  Lemma compare_trans :
     forall (c : comparison) (x y z : t),
       compare x y = c -> compare y z = c -> << TR:compare x z = c >>.
  Proof. i. destruct x, y, z; ss; des_ifs. Qed.

  Lemma compare_leibniz : forall x y : t, compare x y = Eq -> x = y.
  Proof. destruct x, y; ss. Qed.

End Tag.

Hint Resolve Tag.eq_dec: EqDecDb.

Module IdT <: AltUsual.
  Include (prod Tag id).

  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply Tag.eq_dec.
  Qed.

  Definition lift (tag:Tag.t) (i:id): t := (tag, i).

End IdT.
Hint Resolve IdT.eq_dec: EqDecDb.

Module IdT_OT := Backport_Alt IdT.

Module IdTSet.
  Include FSetAVLExtra IdT_OT.

  Definition clear_idt (idt0: IdT.t) (t0: t): t :=
    filter (fun x => negb (IdT.eq_dec idt0 x)) t0
  .

End IdTSet.

Module IdTSetFacts := FSetFactsExtra IdT_OT IdTSet.

Lemma IdTSet_from_list_spec ids:
  forall id, IdTSet.mem id (IdTSetFacts.from_list ids) <-> In id ids.
Proof.
  i. rewrite IdTSetFacts.from_list_spec.
  etransitivity; try apply InA_iff_In.
  split; i.
Admitted.

Module Value.
  Definition t := value.

  Definition get_ids(v: t): option id :=
    match v with
      | value_id i => Some i
      | value_const _ => None
    end.
End Value.

Module ValueT <: AltUsual.
  Inductive t_: Type :=
  | id (x:IdT.t)
  | const (c:const)
  .
  Definition t:= t_.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    decide equality.
    apply IdT.eq_dec.
    apply const_dec.
  Qed.

  Definition case_order v : OrdIdx.t :=
    match v with
    | id _ => 0
    | const _ => 1
    end.

  Definition compare (v1 v2:t) : comparison :=
    match v1, v2 with
    | id x1, id x2 => IdT.compare x1 x2
    | const c1, const c2 => const.compare c1 c2
    | _, _ => OrdIdx.compare (case_order v1) (case_order v2)
    end.

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof.
  Admitted.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof.
  Admitted.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof.
  Admitted.

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

  Definition substitute (from: IdT.t) (to: ValueT.t) (body: ValueT.t): ValueT.t :=
    match body with
    | ValueT.id i => if(IdT.eq_dec from i) then to else body
    | _ => body
    end
  .

End ValueT.

Hint Resolve ValueT.eq_dec: EqDecDb.
Coercion ValueT.id: IdT.t >-> ValueT.t_.
Coercion ValueT.const: const >-> ValueT.t_.

Module ValueT_OT := Backport_Alt ValueT.

Module ValueTSet := FSetAVLExtra ValueT_OT.
Module ValueTSetFacts := FSetFactsExtra ValueT_OT ValueTSet.

Module ValueTPair <: AltUsual.
  Include prod ValueT ValueT.

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

Module ValueTPair_OT := Backport_Alt ValueTPair.
Module ValueTPairSet.
  Include FSetAVLExtra ValueTPair_OT.

  Definition clear_idt (idt: IdT.t) (t0: t): t :=
    filter (fun xy => negb (list_inb IdT.eq_dec (ValueTPair.get_idTs xy) idt)) t0
  .

End ValueTPairSet.

Module ValueTPairSetFacts := FSetFactsExtra ValueTPair_OT ValueTPairSet.

Module sz_ValueT := prod sz ValueT.

Module Expr <: AltUsual.
  Inductive t_: Type :=
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

  Definition case_order e : OrdIdx.t :=
    match e with
    | bop _ _ _ _ => 0
    | fbop _ _ _ _ => 1
    | extractvalue _ _ _ _ => 2
    | insertvalue _ _ _ _ _ => 3
    | gep _ _ _ _ _ => 4
    | trunc _ _ _ _ => 5
    | ext _ _ _ _ => 6
    | cast _ _ _ __ => 7
    | icmp _ _ _ _ => 8
    | fcmp _ _ _ _ => 9
    | select _ _ _ _ => 10
    | value _ => 11
    | load _ _ _ => 12
    end.

  Definition compare' (e1 e2:t): comparison :=
    match e1, e2 with
    | bop b1 s1 v1 w1, bop b2 s2 v2 w2 =>
      lexico_order [fun _ => bop.compare b1 b2 ; fun _ => sz.compare s1 s2 ;
                      fun _ => ValueT.compare v1 v2 ; fun _ => ValueT.compare w1 w2]
    | fbop fb1 fp1 v1 w1, fbop fb2 fp2 v2 w2 =>
      lexico_order [fun _ => fbop.compare fb1 fb2 ; fun _ => floating_point.compare fp1 fp2 ;
                      fun _ => ValueT.compare v1 v2 ; fun _ => ValueT.compare w1 w2]
    | extractvalue t1 v1 lc1 u1, extractvalue t2 v2 lc2 u2 =>
      lexico_order [fun _ => typ.compare t1 t2 ; fun _ => ValueT.compare v1 v2 ;
                      fun _ => compare_list const.compare lc1 lc2 ;
                      fun _ => typ.compare u1 u2]
    | insertvalue t1 v1 u1 w1 lc1, insertvalue t2 v2 u2 w2 lc2 =>
      lexico_order [fun _ => typ.compare t1 t2 ; fun _ => ValueT.compare v1 v2 ;
                      fun _ => typ.compare u1 u2 ; fun _ => ValueT.compare w1 w2 ;
                        fun _ => compare_list const.compare lc1 lc2]
    | gep ib1 t1 v1 lsv1 u1, gep ib2 t2 v2 lsv2 u2 =>
      lexico_order [fun _ => bool.compare ib1 ib2 ; fun _ => typ.compare t1 t2 ;
                      fun _ => ValueT.compare v1 v2 ;
                      fun _ => compare_list sz_ValueT.compare lsv1 lsv2 ;
                      fun _ => typ.compare u1 u2]
    | trunc top1 t1 v1 u1, trunc top2 t2 v2 u2 =>
      lexico_order [fun _ => truncop.compare top1 top2 ; fun _ => typ.compare t1 t2 ;
                      fun _ => ValueT.compare v1 v2 ; fun _ => typ.compare u1 u2]
    | ext eop1 t1 v1 u1, ext eop2 t2 v2 u2 =>
      lexico_order [fun _ => extop.compare eop1 eop2 ; fun _ => typ.compare t1 t2 ;
                      fun _ => ValueT.compare v1 v2 ; fun _ => typ.compare u1 u2]
    | cast cop1 t1 v1 u1, cast cop2 t2 v2 u2 =>
      lexico_order [fun _ => castop.compare cop1 cop2 ; fun _ => typ.compare t1 t2 ;
                      fun _ => ValueT.compare v1 v2 ; fun _ => typ.compare u1 u2]
    | icmp c1 t1 v1 w1, icmp c2 t2 v2 w2 =>
      lexico_order [fun _ => cond.compare c1 c2 ; fun _ => typ.compare t1 t2 ;
                      fun _ => ValueT.compare v1 v2 ; fun _ => ValueT.compare w1 w2]
    | fcmp c1 t1 v1 w1, fcmp c2 t2 v2 w2 =>
      lexico_order [fun _ => fcond.compare c1 c2 ; fun _ => floating_point.compare t1 t2 ;
                      fun _ => ValueT.compare v1 v2 ; fun _ => ValueT.compare w1 w2]
    | select v1 t1 w1 z1, select v2 t2 w2 z2 =>
      lexico_order [fun _ => ValueT.compare v1 v2 ; fun _ => typ.compare t1 t2 ;
                      fun _ => ValueT.compare w1 w2 ; fun _ => ValueT.compare z1 z2]
    | value v1, value v2 => ValueT.compare v1 v2
    | load v1 t1 a1, load v2 t2 a2 =>
      lexico_order [fun _ => ValueT.compare v1 v2 ; fun _ => typ.compare t1 t2 ;
                      fun _ => sz.compare a1 a2]
    | _, _ => OrdIdx.compare (case_order e1) (case_order e2)
    end.

  Definition compare := wrap_compare compare'.

  Lemma compare_sym
        x y
    : <<SYM: compare y x = CompOpp (compare x y)>>.
  Proof.
  Admitted.

  Lemma compare_trans
        c x y z
        (XY: compare x y = c)
        (YZ: compare y z = c)
    : <<XZ: compare x z = c>>.
  Proof.
  Admitted.

  Lemma compare_leibniz
        x y
        (EQ: compare x y = Eq)
    : x = y.
  Proof.
  Admitted.

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

  Definition substitute (from: IdT.t) (to: ValueT.t) (body: t): t :=
    (Expr.map_valueTs body (ValueT.substitute from to))
  .

  Definition is_load (e: t): bool :=
    match e with
    | Expr.load _ _ _ => true
    | _ => false
    end
  .

End Expr.
Hint Resolve Expr.eq_dec: EqDecDb.
Coercion Expr.value: ValueT.t >-> Expr.t_.

Module Expr_OT := Backport_Alt Expr.
Module ExprSet := FSetAVLExtra Expr_OT.

Module ExprPair <: AltUsual.
  Include prod Expr Expr.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    apply prod_dec;
      apply Expr.eq_dec.
  Defined.

  Definition get_idTs (ep: t): list IdT.t :=
    (Expr.get_idTs ep.(fst))
      ++ (Expr.get_idTs ep.(snd)).
End ExprPair.

Module ExprPair_OT := Backport_Alt ExprPair.
Module ExprPairSet.
  Include FSetAVLExtra ExprPair_OT.

  Definition clear_idt (idt: IdT.t) (t0: t): t :=
    filter (fun xy => negb (list_inb IdT.eq_dec (ExprPair.get_idTs xy) idt)) t0
  .
End ExprPairSet.

Module ExprPairSetFacts := FSetFactsExtra ExprPair_OT ExprPairSet.

(* Ptr: alias related values *)
Module Ptr <: AltUsual.
  (* typ has the type of the 'pointer', not the type of the 'object'.
     ex: %x = load i32* %y, align 4 <- (id y, typ_pointer (typ_int 32))
                   ^^^^
  *)
  Include prod ValueT typ.

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

Module Ptr_OT := Backport_Alt Ptr.
Module PtrSet := FSetAVLExtra Ptr_OT.
Module PtrSetFacts := FSetFactsExtra Ptr_OT PtrSet.

Lemma InA_equiv_eqs
      X (eqa eqb : X -> X -> Prop)
      (EQS_EQ: forall x y, eqa x y <-> eqb x y)
  : forall a l, InA eqa a l <-> InA eqb a l.
Proof.
  intros a l.
  induction l; split; intro HIn; inv HIn;
    try (by left; apply EQS_EQ; eauto);
    try (by right; apply IHl; eauto).
Qed.

Lemma PtrSet_from_list_spec ps:
  forall p, PtrSet.mem p (PtrSetFacts.from_list ps) <-> In p ps.
Proof.
  i. rewrite PtrSetFacts.from_list_spec.
  cut (InA (fun x y : Ptr.t => Ptr.compare x y = Eq) p ps
       <-> InA eq p ps).
  { intro EQUIV. rewrite EQUIV. apply InA_iff_In. }
  apply InA_equiv_eqs.
  i. split.
  - apply Ptr.compare_leibniz.
  - i. subst. apply PtrSet.E.eq_refl.
Qed.

Module PtrPair <: AltUsual.
  Include prod Ptr Ptr.
  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof.
    apply prod_dec; apply Ptr.eq_dec.
  Defined.

  Definition get_idTs (pp: t): list IdT.t :=
    (option_to_list (Ptr.get_idTs pp.(fst)))
      ++ (option_to_list (Ptr.get_idTs pp.(snd))).
End PtrPair.
Hint Resolve PtrPair.eq_dec: EqDecDb.

Module PtrPair_OT := Backport_Alt PtrPair.

Module PtrPairSet.
  Include FSetAVLExtra PtrPair_OT.
  Definition clear_idt (idt: IdT.t) (t0: t): t :=
    filter (fun xy => negb (list_inb IdT.eq_dec (PtrPair.get_idTs xy) idt)) t0
  .

End PtrPairSet.

Module PtrPairSetFacts := FSetFactsExtra PtrPair_OT PtrPairSet.



(* TODO: Remove this after migrating yoonseung's Ords.v *)
Ltac solve_leibniz_ cmp CL :=
  repeat match goal with
         | [H:cmp ?a ?b = Eq |- _] => apply CL in H
         end; subst.

Ltac solve_leibniz :=
  solve_leibniz_ ValueT.compare ValueT.compare_leibniz;
  solve_leibniz_ IdT.compare IdT.compare_leibniz;
  solve_leibniz_ ValueTPair.compare ValueTPair.compare_leibniz;
  solve_leibniz_ PtrPair.compare PtrPair.compare_leibniz
  solve_leibniz_ ExprPair.compare ExprPair.compare_leibniz;
.

Ltac solve_compat_bool := repeat red; ii; solve_leibniz; subst; eauto; ss.
