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
  Structure unary := mk_unary {
    lessdef: ExprPairSet.t;
    noalias: ValueTPairSet.t;
    allocas: IdTSet.t;
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
      invariant.(noalias)
      invariant.(allocas)
      invariant.(private).

  Definition update_noalias (f:ValueTPairSet.t -> ValueTPairSet.t) (invariant:unary): unary :=
    mk_unary
      invariant.(lessdef)
      (f invariant.(noalias))
      invariant.(allocas)
      invariant.(private).

  Definition update_allocas (f:IdTSet.t -> IdTSet.t) (invariant:unary): unary :=
    mk_unary
      invariant.(lessdef)
      invariant.(noalias)
      (f invariant.(allocas))
      invariant.(private).

  Definition update_private (f:IdTSet.t -> IdTSet.t) (invariant:unary): unary :=
    mk_unary
      invariant.(lessdef)
      invariant.(noalias)
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

  Definition implies_unary (inv0 inv:unary): bool :=
    ExprPairSet.subset (inv.(lessdef)) (inv0.(lessdef)) &&
    ValueTPairSet.subset (inv.(noalias)) (inv0.(noalias)) &&
    IdTSet.subset (inv.(allocas)) (inv0.(allocas)) &&
    IdTSet.subset (inv.(private)) (inv0.(private)).

  Definition implies (inv0 inv:t): bool :=
    implies_unary (inv0.(src)) (inv.(src)) &&
    implies_unary (inv0.(tgt)) (inv.(tgt)) &&
    IdTSet.subset (inv0.(maydiff)) (inv.(maydiff)).

  Definition is_noalias (inv:unary) (i1:IdT.t) (i2:IdT.t) :=
    let e1 := ValueT.id i1 in
    let e2 := ValueT.id i2 in
    ValueTPairSet.mem (e1, e2) inv.(noalias) || ValueTPairSet.mem (e2, e1) inv.(noalias).

  Definition not_in_maydiff (inv:t) (value:ValueT.t): bool :=
    match value with
    | ValueT.id id =>
      negb (IdTSet.mem id inv.(maydiff))
    | ValueT.const _ => true
    end.

  Definition not_in_maydiff_expr (inv:t) (expr: Expr.t): bool :=
    List.forallb (not_in_maydiff inv) (Expr.get_valueTs expr).

  Definition get_lhs (inv:ExprPairSet.t) (rhs:Expr.t): ExprPairSet.t :=
    ExprPairSet.filter
       (fun (p: ExprPair.t) => Expr.eq_dec rhs (snd p))
       inv.
      
  Definition get_rhs (inv:ExprPairSet.t) (lhs:Expr.t): ExprPairSet.t :=
    ExprPairSet.filter
       (fun (p: ExprPair.t) => Expr.eq_dec lhs (fst p))
       inv.

  Definition inject_value (inv:t) (value_src value_tgt:ValueT.t): bool :=
    (ValueT.eq_dec value_src value_tgt && not_in_maydiff inv value_src) ||
    (ExprPairSet.mem (Expr.value value_src, Expr.value value_tgt) inv.(tgt).(lessdef) && not_in_maydiff inv value_src) ||
    (ExprPairSet.mem (Expr.value value_src, Expr.value value_tgt) inv.(src).(lessdef) && not_in_maydiff inv value_tgt) ||
    (ExprPairSet.exists_
       (fun (p: ExprPair.t) => 
          let (x, y) := p in 
          ((ExprPairSet.mem (y, Expr.value value_tgt) inv.(tgt).(lessdef)) &&
           (not_in_maydiff_expr inv y)))
       (get_rhs inv.(src).(lessdef) (Expr.value value_src))).

  Definition is_empty_unary (inv:unary): bool :=
    ExprPairSet.is_empty inv.(lessdef) &&
    ValueTPairSet.is_empty inv.(noalias) &&
    IdTSet.is_empty inv.(allocas) &&
    IdTSet.is_empty inv.(private).

  Definition is_empty (inv:t): bool :=
    is_empty_unary inv.(src) &&
    is_empty_unary inv.(tgt) &&
    IdTSet.is_empty inv.(maydiff).

  Definition get_idTs_unary (u: unary): list IdT.t :=
    let (lessdef, noalias, allocas, private) := u in
    List.concat
      (List.map
         (fun (p: ExprPair.t) =>
            let (x, y) := p in Expr.get_idTs x ++ Expr.get_idTs y)
         (ExprPairSet.elements lessdef)) ++
      List.concat
      (List.map
         (fun (p: ValueTPair.t) =>
            let (x, y) := p in TODO.filter_map ValueT.get_idTs [x ; y])
         (ValueTPairSet.elements noalias)) ++
      IdTSet.elements allocas ++ IdTSet.elements private.

  Definition get_idTs (inv: t): list IdT.t :=
    let (src, tgt, maydiff) := inv in
    (get_idTs_unary src)
      ++ (get_idTs_unary tgt)
      ++ (IdTSet.elements maydiff).
End Invariant.

Module Infrule.
  Inductive t :=
  | add_associative (x:IdT.t) (y:IdT.t) (z:IdT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (s:sz)
  | add_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_const_not (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | add_dist_sub (z:IdT.t) (minusx:IdT.t) (minusy:ValueT.t) (w:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_sub (z:IdT.t) (minusy:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_mask (z:IdT.t) (y:IdT.t) (y':IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | add_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | add_select_zero (z:IdT.t) (x:IdT.t) (y:IdT.t) (c:ValueT.t) (n:ValueT.t) (a:ValueT.t) (s:sz)
  | add_select_zero2 (z:IdT.t) (x:IdT.t) (y:IdT.t) (c:ValueT.t) (n:ValueT.t) (a:ValueT.t) (s:sz)
  | add_shift (y:IdT.t) (v:ValueT.t) (s:sz) 
  | add_signbit (x:IdT.t) (e1:ValueT.t) (e2:ValueT.t) (s:sz)
  | add_zext_bool (x:IdT.t) (y:IdT.t) (b:ValueT.t) (c:INTEGER.t) (c':INTEGER.t) (sz:sz)
  | and_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | and_de_morgan (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | bop_distributive_over_selectinst (opcode:bop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (bopsz:sz) (selty:typ)
  | bop_distributive_over_selectinst2 (opcode:bop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (bopsz:sz) (selty:typ)
  | bitcastptr (v:ValueT.t) (v':ValueT.t) (bitcastinst:Expr.t)
  | fadd_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (fty:floating_point)
  | fbop_distributive_over_selectinst (opcode:fbop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (fbopty:floating_point) (selty:typ)
  | fbop_distributive_over_selectinst2 (opcode:fbop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (fbopty:floating_point) (selty:typ)
  | gepzero (v:ValueT.t) (v':ValueT.t) (gepinst:Expr.t)
  | mul_bool (z:IdT.t) (x:IdT.t) (y:IdT.t)
  | mul_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | mul_mone (z:IdT.t) (x:ValueT.t) (sz:sz)
  | mul_neg (z:IdT.t) (mx:ValueT.t) (my:ValueT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)  
  | mul_shl (z:IdT.t) (y:IdT.t) (x:ValueT.t) (a:ValueT.t) (sz:sz)
  | neg_val (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | or_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | or_or  (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | or_or2  (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (y':ValueT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | or_xor (w:ValueT.t) (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | or_xor2 (z:ValueT.t) (x1:ValueT.t) (y1:ValueT.t) (x2:ValueT.t) (y2:ValueT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | rem_neg (z:IdT.t) (my:ValueT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | sdiv_mone (z:IdT.t) (x:ValueT.t) (sz:sz)
  | sdiv_sub_srem (z:IdT.t) (b:IdT.t) (a:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | sub_add (z:IdT.t) (minusy:ValueT.t) (x:IdT.t) (y:ValueT.t) (s:sz)
  | sub_const_add (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (sz:sz)
  | sub_const_not (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | sub_mone (z:IdT.t) (x:ValueT.t) (s:sz) 
  | sub_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | sub_remove (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | sub_sdiv (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c:INTEGER.t) (c':INTEGER.t) (sz:sz)
  | sub_shl (z:IdT.t) (x:ValueT.t) (y:IdT.t) (mx:ValueT.t) (a:ValueT.t) (sz:sz)
  | transitivity (e1:Expr.t) (e2:Expr.t) (e3:Expr.t)
  | transitivity_tgt (e1:Expr.t) (e2:Expr.t) (e3:Expr.t)
  | noalias_global_alloca (x:IdT.t) (y:IdT.t)
  | noalias_global_global (x:IdT.t) (y:IdT.t)
  | noalias_lessthan (x:ValueT.t) (y:ValueT.t) (x':ValueT.t) (y':ValueT.t)
  | transitivity_pointer_lhs (p:ValueT.t) (q:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | transitivity_pointer_rhs (p:ValueT.t) (q:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | bop_both_src_left (b:bop) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (sz:sz)
  | bop_both_src_right (b:bop) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (sz:sz)
  | bop_both_tgt_left (b:bop) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (sz:sz)
  | bop_both_tgt_right (b:bop) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (sz:sz)
  | intro_eq (x:Expr.t) (g:IdT.t)
  | replace_rhs (x:IdT.t) (y:ValueT.t) (e1:Expr.t) (e2:Expr.t) (e2':Expr.t)
  | replace_rhs_opt	(x:IdT.t) (y:ValueT.t) (e1:Expr.t) (e2:Expr.t) (e2':Expr.t)
  | udiv_sub_urem (z:IdT.t) (b:IdT.t) (a:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | udiv_zext (z:IdT.t) (x:IdT.t) (y:IdT.t) (k:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz1:sz) (sz2:sz)
  | urem_zext (z:IdT.t) (x:IdT.t) (y:IdT.t) (k:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz1:sz) (sz2:sz)
  | intro_ghost (x:ValueT.t) (g:id)
  | xor_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | xor_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)

(* Updated semantics of rules should be located above this line *)

  | replace_lhs (x:IdT.t) (y:IdT.t) (e:Expr.t)
  | remove_maydiff (v:IdT.t) (e:Expr.t)
  | remove_maydiff_rhs (v:IdT.t) (e:IdT.t)
  | eq_generate_same_heap_value (x:IdT.t) (p:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | stash_variable (z:IdT.t) (v:id)
  | add_mul_fold (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | add_distributive (z:IdT.t) (x:IdT.t) (y:IdT.t) (w:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  | rem_neg2 (z:IdT.t) (sz:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | inbound_remove (x:IdT.t) (y:IdT.t) (pty:typ) (pa:align) (ty:typ) (a:ValueT.t) (idx:list (sz*ValueT.t)) (u:typ) (v:ValueT.t)
  | inbound_remove2 (x:IdT.t) (y:IdT.t) (pty:typ) (pa:align) (ty:typ) (a:ValueT.t) (idx:list (sz*ValueT.t)) (u:typ) (v:ValueT.t)
  | select_trunc (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (sz1:sz) (sz2:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  | select_add (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (sz1:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t) (cond:ValueT.t)
  | select_const_gt (z:IdT.t) (b:IdT.t) (sz1:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
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
  | and_or (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (a:ValueT.t)
  | and_not_or (z:IdT.t) (x:IdT.t) (y:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t)
  | or_undef (z:IdT.t) (s:sz) (a:ValueT.t)
  | or_same (z:IdT.t) (s:sz) (a:ValueT.t)
  | or_zero (z:IdT.t) (s:sz) (a:ValueT.t)
  | or_mone (z:IdT.t) (s:sz) (a:ValueT.t)
  | or_not (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t)
  | or_and (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (a:ValueT.t)
  | xor_zero (z:IdT.t) (s:sz) (a:ValueT.t)
  | xor_same (z:IdT.t) (s:sz) (a:ValueT.t)
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
