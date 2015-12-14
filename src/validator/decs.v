Require Import syntax.
Require Import alist.

Require Import infrastructure.

Require Export Coqlib.
Export LLVMsyntax.
Export LLVMinfra.

Ltac inv H := inversion H; subst; clear H.

(** * Utilities *)

Definition prod_dec:
  forall A (decA: forall x y: A, {x = y} + {~ x = y})
    B (decB: forall x y: B, {x = y} + {~ x = y})
    (x y: A * B),
    {x = y} + {~ x = y}.
Proof.
  intros.
  destruct x, y.
  destruct (decA a a0), (decB b b0).
  left; subst; auto.
  right; intro; apply n; inv H; auto.
  right; intro; apply n; inv H; auto.
  right; intro; apply n; inv H; auto.
Defined.

Definition option_dec (T:Type) 
  (T_dec:forall x y:T,{x = y} + {~ x = y})
  : forall x y:option T, {x = y} + {~ x = y}.
Proof.
  destruct x,y; try (right; discriminate).
  destruct (T_dec t t0); try (right; congruence).
  left; congruence.
  left; congruence.
Defined.

(** * Hint Database: EqDecDb *)

Create HintDb EqDecDb.

Ltac eqdec_tac := decide equality; auto with EqDecDb.

Hint Resolve INTEGER.dec: EqDecDb.
Hint Resolve id_dec: EqDecDb.
Hint Resolve typ_dec: EqDecDb.
Hint Resolve value_dec: EqDecDb.
Hint Resolve bop_dec: EqDecDb.
Hint Resolve fbop_dec: EqDecDb.
Hint Resolve list_const_dec: EqDecDb.
Hint Resolve floating_point_dec: EqDecDb.
Hint Resolve cmd_dec: EqDecDb.
Hint Resolve inbounds_dec: EqDecDb.
Hint Resolve truncop_dec: EqDecDb.
Hint Resolve extop_dec: EqDecDb.
Hint Resolve castop_dec: EqDecDb.
Hint Resolve cond_dec: EqDecDb.
Hint Resolve fcond_dec: EqDecDb.
Hint Resolve varg_dec: EqDecDb.

Lemma clattrs_dec : forall (c c0:clattrs), {c=c0}+{~c=c0}.
Proof.
  destruct c as [tailc5 callconv5 attributes1 attributes2];
  destruct c0 as [tailc0 callconv0 attributes0 attributes3];
  destruct_wrt_type3 tailc5 tailc0; subst; try solve [done_right];
  destruct_wrt_type3 callconv5 callconv0; subst; try solve [done_right];
  destruct_wrt_type3 attributes1 attributes0; subst; try solve [done_right];
  destruct_wrt_type3 attributes2 attributes3;
    subst; try solve [auto|done_right].
Defined.
Hint Resolve clattrs_dec: EqDecDb.

Definition align_dec : forall x y:align, {x = y} + {~ x = y} := Align.dec.
Hint Resolve align_dec: EqDecDb.

Definition sz_dec : forall x y:sz, {x = y} + {~ x = y} := Size.dec.
Hint Resolve sz_dec: EqDecDb.

Ltac dec_destruct x y :=
  match eval compute in (x = y) with
    | (?n = ?n) => fail 1
    | _ => let H := fresh in
      assert (H:{x = y}+{x <> y});
      [auto with EqDecDb|destruct H;[subst|right;congruence]]
  end.

Ltac dec_auto :=
repeat (
match goal with
  | [|- {_ ?x _ _ _ _ _ _ = _ ?y _ _ _ _ _ _ }+{_ ?x _ _ _ _ _ _ <>_ ?y _ _ _ _ _ _}] =>
    dec_destruct x y
  | [|- {_ ?x _ _ _ _ _ = _ ?y _ _ _ _ _ }+{_ ?x _ _ _ _ _ <>_ ?y _ _ _ _ _}] =>
    dec_destruct x y
  | [|- {_ ?x _ _ _ _ = _ ?y _ _ _ _ }+{_ ?x _ _ _ _ <>_ ?y _ _ _ _}] =>
    dec_destruct x y
  | [|- {_ ?x _ _ _ = _ ?y _ _ _ }+{_ ?x _ _ _ <>_ ?y _ _ _}] =>
    dec_destruct x y
  | [|- {_ ?x _ _ = _ ?y _ _ }+{_ ?x _ _ <>_ ?y _ _}] =>
    dec_destruct x y
  | [|- {_ ?x _ = _ ?y _ }+{_ ?x _ <>_ ?y _}] =>
    dec_destruct x y
  | [|- {_ ?x = _ ?y }+{_ ?x <>_ ?y}] =>
    dec_destruct x y
end);
auto.

(** reflection of decs **)

Lemma dec_r
  A (dec: forall (x1 x2:A), {x1 = x2} + {x1 <> x2})
  x1 x2 (H: dec x1 x2) :
  x1 = x2.
Proof.
  destruct dec; inv H; auto.
Qed.

Lemma bop_dec_r x1 x2 (H: bop_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma fbop_dec_r x1 x2 (H: fbop_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma extop_dec_r x1 x2 (H: extop_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma castop_dec_r x1 x2 (H: castop_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma cond_dec_r x1 x2 (H: cond_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma fcond_dec_r x1 x2 (H: fcond_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma floating_point_dec_r x1 x2 (H: floating_point_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma sz_dec_r x1 x2 (H: sz_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma const_dec_r x1 x2 (H: const_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma list_const_dec_r x1 x2 (H: list_const_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma typ_dec_r x1 x2 (H: typ_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma attributes_dec_r x1 x2 (H: attributes_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma noret_dec_r x1 x2 (H: noret_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma clattrs_dec_r x1 x2 (H: clattrs_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma varg_dec_r x1 x2 (H: varg_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

Lemma l_dec_r x1 x2 (H: l_dec x1 x2) : x1 = x2.
Proof.
  eapply dec_r; eauto.
Qed.

(** * Varied Decidability of Program *)

Definition cmd_body_dec (c1 c2: cmd): bool :=
  match c1,c2 with
    | insn_bop _ b1 s1 v1 w1,insn_bop _ b2 s2 v2 w2 =>
      bop_dec b1 b2 && sz_dec s1 s2 
      && value_dec v1 v2 && value_dec w1 w2
    | insn_fbop _ fb1 fp1 v1 w1,insn_fbop _ fb2 fp2 v2 w2 =>
      fbop_dec fb1 fb2 && floating_point_dec fp1 fp2
      && value_dec v1 v2 && value_dec w1 w2
    | insn_extractvalue _ t1 v1 lc1 u1,
      insn_extractvalue _ t2 v2 lc2 u2 =>
      typ_dec t1 t2 && value_dec v1 v2
      && list_const_dec lc1 lc2 && typ_dec u1 u2
    | insn_insertvalue _ t1 v1 u1 w1 lc1,
      insn_insertvalue _ t2 v2 u2 w2 lc2 =>
      typ_dec t1 t2 && value_dec v1 v2
      && typ_dec u1 u2 && value_dec w1 w2
      && list_const_dec lc1 lc2
    | insn_malloc _ t1 v1 a1,insn_malloc _ t2 v2 a2
    | insn_alloca _ t1 v1 a1,insn_alloca _ t2 v2 a2
    | insn_load _ t1 v1 a1,insn_load _ t2 v2 a2 =>
      typ_dec t1 t2 && value_dec v1 v2 && align_dec a1 a2
    | insn_free _ t1 v1,insn_free _ t2 v2 =>
      typ_dec t1 t2 && value_dec v1 v2
    | insn_store _ t1 v1 w1 a1,insn_store _ t2 v2 w2 a2 =>
      typ_dec t1 t2 && value_dec v1 v2 
      && value_dec w1 w2 && align_dec a1 a2
    | insn_gep _ ib1 t1 v1 svl1 u1,insn_gep _ ib2 t2 v2 svl2 u2 =>
      inbounds_dec ib1 ib2 && typ_dec t1 t2
      && value_dec v1 v2 && list_value_dec svl1 svl2
      && typ_dec u1 u2
    | insn_trunc _ top1 t1 v1 u1,insn_trunc _ top2 t2 v2 u2 =>
      truncop_dec top1 top2 && typ_dec t1 t2
      && value_dec v1 v2 && typ_dec u1 u2
    | insn_ext _ eop1 t1 v1 u1,insn_ext _ eop2 t2 v2 u2 =>
      extop_dec eop1 eop2 && typ_dec t1 t2
      && value_dec v1 v2 && typ_dec u1 u2
    | insn_cast _ cop1 t1 v1 u1,insn_cast _ cop2 t2 v2 u2 =>
      castop_dec cop1 cop2 && typ_dec t1 t2 
      && value_dec v1 v2 && typ_dec u1 u2
    | insn_icmp _ c1 t1 v1 w1,insn_icmp _ c2 t2 v2 w2 =>
      cond_dec c1 c2 && typ_dec t1 t2
      && value_dec v1 v2 && value_dec w1 w2
    | insn_fcmp _ fc1 fp1 v1 w1,insn_fcmp _ fc2 fp2 v2 w2 =>
      fcond_dec fc1 fc2 && floating_point_dec fp1 fp2
      && value_dec v1 v2 && value_dec w1 w2
    | insn_select _ v1 t1 w1 x1,insn_select _ v2 t2 w2 x2 =>
      value_dec v1 v2 && typ_dec t1 t2 
      && value_dec w1 w2 && value_dec x1 x2
    | insn_call _ nr1 cl1 t1 va1 v1 p1,
      insn_call _ nr2 cl2 t2 va2 v2 p2 =>
      noret_dec nr1 nr2 && clattrs_dec cl1 cl2
      && typ_dec t1 t2 && varg_dec va1 va2
      && value_dec v1 v2 && params_dec p1 p2
    | _,_ => false
  end.

Definition same_function_call (l r: option cmd): bool :=
  match l, r with
    | Some (insn_call lid lnr lct lt lva lv lp), 
      Some (insn_call rid rnr rct rt rva rv rp) =>
      (id_dec lid rid)
        && (noret_dec lnr rnr)
        && (clattrs_dec lct rct)
        && (typ_dec lt rt)
        && (varg_dec lva rva)
        && (value_dec lv rv)
        && (params_dec lp rp)
    | Some (insn_call _ _ _ _ _ _ _), _ => false
    | _, Some (insn_call _ _ _ _ _ _ _) => false
    | _, _ => true
  end.


(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop"  ***
*** coq-prog-args: ("-emacs-U" "-impredicative-set") ***
*** coq-load-path: ("../../release/theory/metatheory_8.3/" "../../release/vol/src3.0/Vellvm/" "../../release/vol/src3.0/Vellvm/compcert/" "../../release/vol/src3.0/Vellvm/monads/" "../../release/vol/src3.0/Vellvm/ott/" "../../release/vol/src3.0/Vellvm/Dominators/" "../../release/vol/src3.0/Vellvm/GraphBasics/" "../../release/vol/src3.0/Transforms/")  ***
*** End: ***
 *)
