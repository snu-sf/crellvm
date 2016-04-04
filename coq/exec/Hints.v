Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.

Require Import Exprs.

Set Implicit Arguments.

Import ListNotations.

Module Invariant.
  Structure aliasrel := mk_aliasrel {
    diffblock: PtrPairSet.t;
    noalias:  PtrPairSet.t;
  }.

  Structure unary := mk_unary {
    lessdef: ExprPairSet.t;
    alias: aliasrel;
    allocas: PtrSet.t;
    private: IdTSet.t;
  }.

  Structure t := mk {
    src: unary;
    tgt: unary;
    maydiff: IdTSet.t;
  }.

  Definition update_lessdef (f:ExprPairSet.t -> ExprPairSet.t) (invariant:unary): unary :=
    mk_unary
      (f invariant.(lessdef))
      invariant.(alias)
      invariant.(allocas)
      invariant.(private).

  Definition update_diffblock_rel (f:PtrPairSet.t -> PtrPairSet.t) (alias:aliasrel): aliasrel :=
    mk_aliasrel
      (f alias.(diffblock))
      alias.(noalias).

  Definition update_noalias_rel (f:PtrPairSet.t -> PtrPairSet.t) (alias:aliasrel): aliasrel :=
    mk_aliasrel
      alias.(diffblock)
      (f alias.(noalias)).

  Definition update_alias (f:aliasrel -> aliasrel) (invariant:unary): unary :=
    mk_unary
      invariant.(lessdef)
      (f invariant.(alias))
      invariant.(allocas)
      invariant.(private).

  Definition update_diffblock (f:PtrPairSet.t -> PtrPairSet.t) (invariant:unary): unary :=
    update_alias (update_diffblock_rel f) invariant.

  Definition update_noalias (f:PtrPairSet.t -> PtrPairSet.t) (invariant:unary): unary :=
    update_alias (update_noalias_rel f) invariant.

  Definition update_allocas (f:PtrSet.t -> PtrSet.t) (invariant:unary): unary :=
    mk_unary
      invariant.(lessdef)
      invariant.(alias)
      (f invariant.(allocas))
      invariant.(private).

  Definition update_private (f:IdTSet.t -> IdTSet.t) (invariant:unary): unary :=
    mk_unary
      invariant.(lessdef)
      invariant.(alias)
      invariant.(allocas)
      (f invariant.(private)).

  Definition update_src (f:unary -> unary) (invariant:t): t :=
    mk
      (f invariant.(src))
      invariant.(tgt)
      invariant.(maydiff).

  Definition update_tgt (f:unary -> unary) (invariant:t): t :=
    mk
      invariant.(src)
      (f invariant.(tgt))
      invariant.(maydiff).

  Definition update_maydiff (f:IdTSet.t -> IdTSet.t) (invariant:t): t :=
    mk
      invariant.(src)
      invariant.(tgt)
      (f invariant.(maydiff)).

  Definition is_private (inv:unary) (value:ValueT.t): bool :=
    match value with
    | ValueT.id id => IdTSet.mem id inv.(private)
    | ValueT.const _ => false
    end.

  Definition implies_alias (alias0 alias:aliasrel): bool :=
    PtrPairSet.subset (alias.(noalias)) (alias0.(noalias)) &&
    PtrPairSet.subset (alias.(diffblock)) (alias0.(diffblock)).

  Definition implies_unary (inv0 inv:unary): bool :=
    ExprPairSet.subset (inv.(lessdef)) (inv0.(lessdef)) &&
    implies_alias (inv.(alias)) (inv0.(alias)) &&
    PtrSet.subset (inv.(allocas)) (inv0.(allocas)) &&
    IdTSet.subset (inv.(private)) (inv0.(private)).

  Definition implies (inv0 inv:t): bool :=
    implies_unary (inv0.(src)) (inv.(src)) &&
    implies_unary (inv0.(tgt)) (inv.(tgt)) &&
    IdTSet.subset (inv0.(maydiff)) (inv.(maydiff)).

  Definition is_noalias (inv:unary) (i1:IdT.t) (i2:IdT.t) :=
    let e1 := ValueT.id i1 in
    let e2 := ValueT.id i2 in
    PtrPairSet.exists_ (fun p1p2 =>
                         match p1p2 with
                           | ((xe1, _), (xe2, _)) =>
                             (ValueT.eq_dec e1 xe1 && ValueT.eq_dec e2 xe2) ||
                             (ValueT.eq_dec e1 xe2 && ValueT.eq_dec e2 xe1)
                         end) inv.(alias).(noalias).
(*
  Definition is_noalias (inv:unary) (i1:IdT.t) (i2:IdT.t) :=
    let e1 := ValueT.id i1 in
    let e2 := ValueT.id i2 in
    ValueTPairSet.mem (e1, e2) inv.(noalias) || ValueTPairSet.mem (e2, e1) inv.(noalias).
*)
  Definition not_in_maydiff (inv:t) (value:ValueT.t): bool :=
    match value with
    | ValueT.id id =>
      negb (IdTSet.mem id inv.(maydiff))
    | ValueT.const _ => true
    end.

  Definition inject_value (inv:t) (value_src value_tgt:ValueT.t): bool :=
    (ValueT.eq_dec value_src value_tgt && not_in_maydiff inv value_src) ||
    (ExprPairSet.mem (Expr.value value_src, Expr.value value_tgt) inv.(tgt).(lessdef) && not_in_maydiff inv value_src) ||
    (ExprPairSet.mem (Expr.value value_src, Expr.value value_tgt) inv.(src).(lessdef) && not_in_maydiff inv value_tgt).

  Definition is_empty_alias (alias:aliasrel): bool :=
    PtrPairSet.is_empty alias.(noalias) &&
    PtrPairSet.is_empty alias.(diffblock).

  Definition not_in_maydiff_expr (inv:t) (expr: Expr.t): bool :=
    List.forallb (not_in_maydiff inv) (Expr.get_valueTs expr).

  Definition is_empty_unary (inv:unary): bool :=
    ExprPairSet.is_empty inv.(lessdef) &&
    is_empty_alias inv.(alias) &&
    PtrSet.is_empty inv.(allocas) &&
    IdTSet.is_empty inv.(private).

  Definition is_empty (inv:t): bool :=
    is_empty_unary inv.(src) &&
    is_empty_unary inv.(tgt) &&
    IdTSet.is_empty inv.(maydiff).

  Definition get_idTs_unary (u: unary): list IdT.t :=
    let (lessdef, alias, allocas, private) := u in
    List.concat
      (List.map
         (fun (p: ExprPair.t) =>
            let (x, y) := p in Expr.get_idTs x ++ Expr.get_idTs y)
         (ExprPairSet.elements lessdef)) ++
    List.concat
      (List.map
         (fun (p: PtrPair.t) =>
            let (x, y) := p in TODO.filter_map Ptr.get_idTs [x ; y])
         (PtrPairSet.elements (alias.(noalias)))) ++
      TODO.filter_map Ptr.get_idTs (PtrSet.elements allocas) ++
      IdTSet.elements private.

  Definition get_idTs (inv: t): list IdT.t :=
    let (src, tgt, maydiff) := inv in
    (get_idTs_unary src)
      ++ (get_idTs_unary tgt)
      ++ (IdTSet.elements maydiff).
End Invariant.

Module Infrule.
  Inductive t :=
  | add_associative (x:IdT.t) (y:IdT.t) (z:IdT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (s:sz)
  | add_const_not (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | add_sub (z:IdT.t) (minusy:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | sub_add (z:IdT.t) (minusy:ValueT.t) (x:IdT.t) (y:ValueT.t) (s:sz)
  | neg_val (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | add_mask (z:IdT.t) (y:IdT.t) (y':IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | add_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | add_select_zero (z:IdT.t) (x:IdT.t) (y:IdT.t) (c:ValueT.t) (n:ValueT.t) (a:ValueT.t) (s:sz)
  | add_select_zero2 (z:IdT.t) (x:IdT.t) (y:IdT.t) (c:ValueT.t) (n:ValueT.t) (a:ValueT.t) (s:sz)
  | add_shift (y:IdT.t) (v:ValueT.t) (s:sz) 
  | add_signbit (x:IdT.t) (e1:ValueT.t) (e2:ValueT.t) (s:sz)
  | add_zext_bool (x:IdT.t) (y:IdT.t) (b:ValueT.t) (c:INTEGER.t) (c':INTEGER.t) (sz:sz)
  | mul_bool (z:IdT.t) (x:IdT.t) (y:IdT.t)
  | mul_neg (z:IdT.t) (mx:ValueT.t) (my:ValueT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)  
  | sub_mone (z:IdT.t) (x:ValueT.t) (s:sz) 
  | sub_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | sub_remove (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | sub_sdiv (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c:INTEGER.t) (c':INTEGER.t) (sz:sz)
  | sub_shl (z:IdT.t) (x:ValueT.t) (y:IdT.t) (mx:ValueT.t) (a:ValueT.t) (sz:sz)
  | transitivity (e1:Expr.t) (e2:Expr.t) (e3:Expr.t)
  | noalias_global_alloca (x:Ptr.t) (y:Ptr.t)
  | transitivity_pointer_lhs (p:ValueT.t) (q:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | transitivity_pointer_rhs (p:ValueT.t) (q:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | replace_rhs (x:IdT.t) (y:ValueT.t) (e1:Expr.t) (e2:Expr.t) (e2':Expr.t)

(* Updated semantics of rules should be located above this line *)

  | replace_rhs_opt (z:IdT.t) (x:IdT.t) (y:ValueT.t) (e:Expr.t) (e':Expr.t)
  | replace_lhs (x:IdT.t) (y:IdT.t) (e:Expr.t)
  | remove_maydiff (v:IdT.t) (e:Expr.t)
  | remove_maydiff_rhs (v:IdT.t) (e:IdT.t)
  | eq_generate_same_heap_value (x:IdT.t) (p:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | stash_variable (z:IdT.t) (v:id)
  | sub_const_not (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | add_mul_fold (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | add_dist_sub (z:IdT.t) (minusx:IdT.t) (minusy:IdT.t) (w:IdT.t) (s:sz) (x:ValueT.t) (y:ValueT.t)
  | add_distributive (z:IdT.t) (x:IdT.t) (y:IdT.t) (w:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  | sub_zext_bool (x:IdT.t) (y:IdT.t) (b:ValueT.t) (sz:sz) (c:INTEGER.t) (c':INTEGER.t)
  | sub_const_add (z:IdT.t) (y:IdT.t) (sz:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t)
  | sub_remove2 (z:IdT.t) (y:IdT.t) (sz:sz) (a:ValueT.t) (b:ValueT.t)
  | mul_mone (z:IdT.t) (sz:sz) (x:ValueT.t)
  | mul_commutative (z:IdT.t) (sz:sz) (x:ValueT.t) (y:ValueT.t)
  | mul_shl (z:IdT.t) (y:IdT.t) (sz:sz) (x:ValueT.t) (a:ValueT.t)
  | div_sub_srem (z:IdT.t) (b:IdT.t) (a:IdT.t) (sz:sz) (x:ValueT.t) (y:ValueT.t)
  | div_sub_urem (z:IdT.t) (b:IdT.t) (a:IdT.t) (sz:sz) (x:ValueT.t) (y:ValueT.t)
  | div_zext (z:IdT.t) (x:IdT.t) (y:IdT.t) (k:IdT.t) (sz1:sz) (sz2:sz) (a:ValueT.t) (b:ValueT.t)
  | div_mone (z:IdT.t) (sz:sz) (x:ValueT.t)
  | rem_zext (z:IdT.t) (x:IdT.t) (y:IdT.t) (k:IdT.t) (sz1:sz) (sz2:sz) (a:ValueT.t) (b:ValueT.t)
  | rem_neg (z:IdT.t) (my:IdT.t) (sz:sz) (x:ValueT.t) (y:ValueT.t)
  | rem_neg2 (z:IdT.t) (sz:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | inbound_remove (x:IdT.t) (y:IdT.t) (pty:typ) (pa:align) (ty:typ) (a:ValueT.t) (idx:list (sz*ValueT.t)) (u:typ) (v:ValueT.t)
  | inbound_remove2 (x:IdT.t) (y:IdT.t) (pty:typ) (pa:align) (ty:typ) (a:ValueT.t) (idx:list (sz*ValueT.t)) (u:typ) (v:ValueT.t)
  | select_trunc (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (sz1:sz) (sz2:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  | select_add (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (sz1:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t) (cond:ValueT.t)
  | select_const_gt (z:IdT.t) (b:IdT.t) (sz1:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | or_xor (z:IdT.t) (y:IdT.t) (sz1:sz) (a:ValueT.t) (b:ValueT.t)
  | or_commutative (z:IdT.t) (sz:sz) (x:ValueT.t) (y:ValueT.t)
  | trunc_onebit (z:IdT.t) (k:IdT.t) (sz:sz) (y:ValueT.t)
  | cmp_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | cmp_eq (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | cmp_ult (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | shift_undef (z:IdT.t) (s:sz) (a:ValueT.t)
  | and_same (z:IdT.t) (s:sz) (a:ValueT.t)
  | and_zero (z:IdT.t) (s:sz) (a:ValueT.t)
  | and_mone (z:IdT.t) (s:sz) (a:ValueT.t)
  | and_undef (z:IdT.t) (s:sz) (a:ValueT.t)
  | and_not (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t)
  | and_commutative (z:IdT.t) (sz:sz) (x:ValueT.t) (y:ValueT.t)
  | and_or (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (a:ValueT.t)
  | and_demorgan (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | and_not_or (z:IdT.t) (x:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | or_undef (z:IdT.t) (s:sz) (a:ValueT.t)
  | or_same (z:IdT.t) (s:sz) (a:ValueT.t)
  | or_zero (z:IdT.t) (s:sz) (a:ValueT.t)
  | or_mone (z:IdT.t) (s:sz) (a:ValueT.t)
  | or_not (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t)
  | or_and (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (a:ValueT.t)
  | xor_zero (z:IdT.t) (s:sz) (a:ValueT.t)
  | xor_same (z:IdT.t) (s:sz) (a:ValueT.t)
  | xor_commutative (z:IdT.t) (sz:sz) (x:ValueT.t) (y:ValueT.t)
  | xor_not (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t)
  | zext_trunc_and (z:IdT.t) (y:IdT.t) (x:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (c:INTEGER.t)
  | zext_trunc_and_xor (z:IdT.t) (y:IdT.t) (x:IdT.t) (w:IdT.t) (w':IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (c:INTEGER.t)
  | zext_xor (z:IdT.t) (y:IdT.t) (y':IdT.t) (a:ValueT.t) (s:sz)
  | sext_trunc (z:IdT.t) (y:IdT.t) (y':IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (n:INTEGER.t)
  | trunc_trunc (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (s3:sz)
  | trunc_zext1 (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz)
  | trunc_zext2 (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (s3:sz)
  | trunc_zext3 (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (s3:sz)
  | trunc_sext1 (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz)
  | trunc_sext2 (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (s3:sz)
  | trunc_sext3 (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (s3:sz)
  | zext_zext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (s3:sz)
  | sext_zext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (s3:sz)
  | sext_sext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (s1:sz) (s2:sz) (s3:sz)
  | fptoui_fpext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (t1:typ) (t2:typ) (t3:typ)
  | fptosi_fpext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (t1:typ) (t2:typ) (t3:typ)
  | uitofp_zext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (t1:typ) (t2:typ) (t3:typ)
  | sitofp_sext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (t1:typ) (t2:typ) (t3:typ)
  | fptrunc_fptrunc (z:IdT.t) (y:IdT.t) (a:ValueT.t) (t1:typ) (t2:typ) (t3:typ)
  | fptrunc_fpext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (t1:typ) (t2:typ)
  | fpext_fpext (z:IdT.t) (y:IdT.t) (a:ValueT.t) (t1:typ) (t2:typ) (t3:typ)
  | cmp_swap_ult (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_ugt (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_ule (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_uge (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_slt (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_sgt (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_sle (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_sge (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_eq (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_swap_ne (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (ty:typ)
  | cmp_slt_onebit (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | cmp_sgt_onebit (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | cmp_ugt_onebit (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | cmp_ule_onebit (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | cmp_uge_onebit (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | cmp_sle_onebit (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | cmp_sge_onebit (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t)
  | cmp_eq_sub (z:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | cmp_ne_sub (z:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | cmp_eq_srem (z:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | cmp_eq_srem2 (z:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | cmp_ne_srem (z:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | cmp_ne_srem2 (z:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | cmp_eq_xor (z:IdT.t) (x:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  | cmp_ne_xor (z:IdT.t) (x:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  .
End Infrule.

Module ValidationHint.
  Structure stmts := mk_stmts {
    phinodes: AssocList (list Infrule.t);
    invariant_after_phinodes: Invariant.t;
    cmds: list (list Infrule.t * Invariant.t);
  }.

  Definition fdef := AssocList stmts.
  Definition products := AssocList fdef.
  Definition module := products.
  Definition modules := list module.
  Definition system := modules.
End ValidationHint.
