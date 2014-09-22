Require Import vellvm.
Require Import alist.
Require Import decs.

(** * Extended instructions : variable + {old,new} mark

We extend instruction syntax for expressing an old value of a
variable.  The extended instructions are used in hint. *)

(** [ntag] expresses whether a variable is newly define in the basic
block. *)

Inductive ntag :=
| ntag_old
| ntag_new.

Definition id_ext : Type := (id * ntag)%type.

Inductive value_ext : Type :=
| value_ext_id (x:id_ext)
| value_ext_const (c:const)
.

Definition params_ext := list (typ * attributes * value_ext).

(** ** [rhs_ext] is the right hand side of an extended command that
uses [id_ext]. *)

Inductive rhs_ext := 
| rhs_ext_bop (b:bop) (s:sz) (v:value_ext) (w:value_ext)
| rhs_ext_fbop (fb:fbop) (fp:floating_point) (v:value_ext) (w:value_ext)
| rhs_ext_extractvalue (t:typ) (v:value_ext) (lc:list const) (u:typ)
| rhs_ext_insertvalue (t:typ) (v:value_ext) (u:typ) (w:value_ext) (lc:list const)
| rhs_ext_gep (ib:inbounds) (t:typ) (v:value_ext) (lsv:list (sz * value_ext)) (u:typ)
| rhs_ext_trunc (top:truncop) (t:typ) (v:value_ext) (u:typ)
| rhs_ext_ext (eop:extop) (t:typ) (v:value_ext) (u:typ)
| rhs_ext_cast (cop:castop) (t:typ) (v:value_ext) (u:typ)
| rhs_ext_icmp (c:cond) (t:typ) (v:value_ext) (w:value_ext)
| rhs_ext_fcmp (fc:fcond) (fp:floating_point) (v:value_ext) (w:value_ext)
| rhs_ext_select (v:value_ext) (t:typ) (w:value_ext) (z:value_ext)
| rhs_ext_value (v:value_ext)
| rhs_ext_old_alloca
.

(** ** decidability *)

Definition ntag_dec : forall x y:ntag, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.
Definition id_ext_dec : forall x y:id_ext, {x = y} + {x <> y}.
Proof.
  destruct x,y; destruct (id_dec i0 i1).
  decide equality; apply ntag_dec.
  decide equality; apply ntag_dec.
Defined.
Hint Resolve id_ext_dec: EqDecDb.

Lemma id_ext_dec_r x1 x2 (H: id_ext_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Definition value_ext_dec : forall v1 v2 : value_ext, {v1 = v2} + {v1 <> v2}.
Proof.
  destruct v1,v2; try (right; congruence).
  destruct (id_ext_dec x x0); subst. left; auto. right; congruence.
  destruct (const_dec c c0); subst. left; auto. right; congruence.
Defined.
Hint Resolve value_ext_dec: EqDecDb.

Lemma value_ext_dec_r x1 x2 (H: value_ext_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma list_value_ext_dec : forall (lv1 lv2: list (sz * value_ext)), {lv1=lv2}+{~lv1=lv2}.
Proof.
  decide equality.
  decide equality.
  apply value_ext_dec.
  apply Size.dec. 
Defined.
Hint Resolve list_value_ext_dec: EqDecDb.

Lemma params_ext_dec : forall (p1 p2:params_ext), {p1=p2}+{~p1=p2}.
Proof.
  decide equality.
    destruct a as [ [t a] v]. destruct p as [ [t0 a0] v0].
    destruct (@typ_dec t t0); subst; try solve [done_right].
    destruct (@attributes_dec a a0); subst; try solve [done_right].
    destruct (@value_ext_dec v v0); subst; try solve [auto | done_right].
Defined.
Hint Resolve params_ext_dec: EqDecDb.

Definition rhs_ext_dec : forall x y:rhs_ext, {x = y} + {~ x = y}.
Proof.
  intros x y.
  repeat (match goal with
            | [x: rhs_ext |- _] => destruct x
            | [x: (_ * _)%type |- _] => destruct x
          end; try (right; discriminate); dec_auto).
Defined.
Hint Resolve rhs_ext_dec: EqDecDb.


(** * Auxiliary Functions on Extended Syntax *)

(** ** Set of [id_ext] *)

Module IdExtDT <: UsualDecidableType with Definition t := id_ext.
  Definition t := id_ext.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec := id_ext_dec.
End IdExtDT.

Module IdExtSetImpl : FSetExtra.WSfun IdExtDT := FSetExtra.Make IdExtDT.
Module IdExtSetFacts := WFacts_fun IdExtDT IdExtSetImpl.

(** ** Set of [value_ext] *)

Module ValueExtDT <: UsualDecidableType with Definition t := value_ext.
  Definition t := value_ext.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec := value_ext_dec.
End ValueExtDT.

Module ValueExtSetImpl : FSetExtra.WSfun ValueExtDT := FSetExtra.Make ValueExtDT.
Module ValueExtSetFacts := WFacts_fun ValueExtDT ValueExtSetImpl.

(** ** Set of [id_ext] * [rhs_ext]  *)

Module EqRegDT <: UsualDecidableType with Definition t := (id_ext * rhs_ext)%type.
  Definition t := (id_ext * rhs_ext)%type.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec := prod_dec _ id_ext_dec _ rhs_ext_dec.
End EqRegDT.

Module EqRegSetImpl : FSetExtra.WSfun EqRegDT := FSetExtra.Make EqRegDT.
Module EqRegSetFacts := WFacts_fun EqRegDT EqRegSetImpl.

(** ** Set of pointer(=[value_ext]) * [value_ext]  *)

Module EqHeapDT <: UsualDecidableType with Definition t := (value_ext * typ * align * value_ext)%type.
  Definition t := (value_ext * typ * align * value_ext)%type.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec :=
    prod_dec _ (prod_dec _ (prod_dec _ value_ext_dec _ typ_dec) _ (align_dec)) _ value_ext_dec.
End EqHeapDT.

Module EqHeapSetImpl : FSetExtra.WSfun EqHeapDT := FSetExtra.Make EqHeapDT.
Module EqHeapSetFacts := WFacts_fun EqHeapDT EqHeapSetImpl.

(** ** Set of [id_ext] * ([id_ext] + global(=[id])) *)

Definition localglobal_t := (id_ext + id)%type.

Definition localglobal_dec : forall (x y:localglobal_t), {x = y} + {x <> y}.
Proof. decide equality. apply id_ext_dec. Defined.

Module NeqRegDT <: UsualDecidableType with Definition t := (id_ext * localglobal_t)%type.
  Definition t := (id_ext * localglobal_t)%type.
  Definition eq := @eq t.
  Definition eq_refl := @refl_equal t.
  Definition eq_sym := @sym_eq t.
  Definition eq_trans := @trans_eq t.
  Definition eq_dec := prod_dec _ id_ext_dec _ localglobal_dec.
End NeqRegDT.

Module NeqRegSetImpl : FSetExtra.WSfun NeqRegDT := FSetExtra.Make NeqRegDT.
Module NeqRegSetFacts := WFacts_fun NeqRegDT NeqRegSetImpl.

(** * Logical Nop *)

(** We renamed some operators of [nat] for extracting them to
integer-related ones in OCaml.  [nat] was already extracted by the
vellvm compile, so we rename it and give an extraction option only for
my_somethings. *)

Definition my_nat := nat.
Definition my_O : my_nat := O.
Definition my_S : my_nat -> my_nat := S.
Definition my_beq_nat : my_nat -> my_nat -> bool := beq_nat.
Definition my_pred : my_nat -> my_nat := pred.

(** ** type definition *)

Structure one_noop_t : Type := mkOneNoop {
  bb_noop: l;
  idx_noop: my_nat
}.

Definition noop_t : Type := list one_noop_t.

Definition fdef_noop_t : Type := noop_t.
Definition products_noop_t : Type := AssocList (* fid to *) fdef_noop_t.
Definition module_noop_t : Type := products_noop_t.
Definition modules_noop_t : Type := list module_noop_t.
Definition system_noop_t : Type := modules_noop_t.

(** ** auxiliary functions for nop *)

Definition get_noop_by_fname (fname:id) (pnoop:products_noop_t) : noop_t :=
  match lookupAL _ pnoop fname with
    | None => nil
    | Some noop => noop
  end.

Definition get_noop_by_bb (bb:l) (noop:noop_t) : noop_t := 
  List.filter (fun x => l_dec bb (bb_noop x)) noop.

Fixpoint noop_idx_zero_exists (noop:noop_t) : bool :=
  match noop with
    | nil => false
    | hd::tl => 
      (my_beq_nat my_O (idx_noop hd)) || noop_idx_zero_exists tl
  end.

Fixpoint noop_idx_zero_remove (noop:noop_t) : noop_t :=
  match noop with
    | nil => nil
    | hd::tl => 
      if my_beq_nat my_O (idx_noop hd)
        then tl
        else hd::(noop_idx_zero_remove tl)
  end.

Definition noop_idx_decrease (noop:noop_t) : noop_t :=
  List.map (fun one_noop =>
    mkOneNoop (bb_noop one_noop) (my_pred (idx_noop one_noop))
    )
  noop.

(** Return type of pop_one_X is option ret_pop.
   - cmd case: (ret_pop_cmd (Some cmd) left_cmd left_nop)
   - nop case: (ret_pop_cmd None left_cmd left_nop)
   - terminator case: ret_pop_terminator

   If the validation succeeded, the error should not appear. *)

Inductive ret_pop {A:Type} : Type :=
| ret_pop_cmd : option A -> list A -> noop_t -> ret_pop
| ret_pop_terminator : ret_pop.

Definition pop_one_X {A:Type} (xs:list A) (noop:noop_t) : ret_pop :=
  if noop_idx_zero_exists noop
  then (ret_pop_cmd None xs (noop_idx_zero_remove noop))
  else
    match xs with
      | hd::tl => (ret_pop_cmd (Some hd) tl (noop_idx_decrease noop))
      | nil => ret_pop_terminator
    end.

Definition lift_fdef_noop_to_system (fid: atom) (fn: fdef_noop_t) : system_noop_t :=
  ( (fid, fn)::nil )::nil.

Fixpoint collect_global_ids (ps: products) : ids :=
  match ps with
    | nil => nil
    | (product_gvar (gvar_intro i _ _ _ _ _))::tps => (i::(collect_global_ids tps))
    | (product_gvar (gvar_external i _ _))::tps => (i::(collect_global_ids tps))
    | _::tps => collect_global_ids tps
  end.

Definition get_products_from_module (m: module) :=
  match m with
    | module_intro _ _ ps => ps
  end.
