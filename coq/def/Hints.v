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
  (* alias relation.
     Ptr is used because we want to use type information in alias reasoning.
     for example, i64* ptr cannot alias with i32 memory block *)
  Structure aliasrel := mk_aliasrel {
    diffblock: ValueTPairSet.t; (* strong no-alias, in different logic block *)
    noalias:  PtrPairSet.t; (* weak no-alias, maybe in the same logic block *)
  }.

  Definition false_encoding: ExprPair.t :=
    let wrap_Z x :=
        Expr.value (ValueT.const
                      (const_int Size.SixtyFour (INTEGER.of_Z 64%Z x%Z true)))
    in (wrap_Z 0, wrap_Z 42).

  Structure unary := mk_unary {
    lessdef: ExprPairSet.t;
    alias: aliasrel;
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
      invariant.(alias)
      invariant.(allocas)
      invariant.(private).

  Definition update_diffblock_rel (f:ValueTPairSet.t -> ValueTPairSet.t) (alias:aliasrel): aliasrel :=
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

  Definition update_diffblock (f:ValueTPairSet.t -> ValueTPairSet.t) (invariant:unary): unary :=
    update_alias (update_diffblock_rel f) invariant.

  Definition update_noalias (f:PtrPairSet.t -> PtrPairSet.t) (invariant:unary): unary :=
    update_alias (update_noalias_rel f) invariant.

  Definition update_allocas (f:IdTSet.t -> IdTSet.t) (invariant:unary): unary :=
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
    PtrPairSet.subset (alias0.(noalias)) (alias.(noalias)) &&
    ValueTPairSet.subset (alias0.(diffblock)) (alias.(diffblock)).

  Definition implies_unary (inv0 inv:unary): bool :=
    ExprPairSet.for_all
          (fun p => ExprPairSet.exists_
                      (fun q =>
                        (if (Expr.eq_dec (fst p) (fst q))
                         then ((Expr.eq_dec (snd p) (snd q)) ||
                               (match (snd p), (snd q) with
                                | Expr.value v, 
                                  Expr.value (ValueT.const (const_undef ty)) => true
                                | _, _ => false
                                end))
                         else false))
                      inv0.(lessdef))
    inv.(lessdef) &&
    implies_alias (inv.(alias)) (inv0.(alias)) &&
    IdTSet.subset (inv.(allocas)) (inv0.(allocas)) &&
    IdTSet.subset (inv.(private)) (inv0.(private)).

  Definition has_false (inv: t): bool :=
    (ExprPairSet.mem false_encoding inv.(src).(lessdef)).

  Definition implies (inv0 inv:t): bool :=
    (has_false inv0)
    || ((implies_unary (inv0.(src)) (inv.(src)))
          && implies_unary (inv0.(tgt)) (inv.(tgt))
          && IdTSet.subset (inv0.(maydiff)) (inv.(maydiff))).

  Definition is_noalias (inv:unary) (p1:Ptr.t) (p2:Ptr.t) :=
    PtrPairSet.exists_ (fun p1p2 =>
                         match p1p2 with
                           | (xp1, xp2) =>
                             (Ptr.eq_dec p1 xp1 && Ptr.eq_dec p2 xp2) ||
                             (Ptr.eq_dec p1 xp2 && Ptr.eq_dec p2 xp1)
                         end) inv.(alias).(noalias).

  Definition is_diffblock (inv:unary) (p1:Ptr.t) (p2:Ptr.t) :=
    let (v1, t1) := p1 in
    let (v2, t2) := p2 in
    ValueTPairSet.exists_
      (fun v1v2 =>
        match v1v2 with
        | (xv1, xv2) =>
            (ValueT.eq_dec v1 xv1 &&
             ValueT.eq_dec v2 xv2) ||
            (ValueT.eq_dec v1 xv2 &&
             ValueT.eq_dec v2 xv1)
        end) inv.(alias).(diffblock).

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

  Definition is_empty_alias (alias:aliasrel): bool :=
    PtrPairSet.is_empty alias.(noalias) &&
    ValueTPairSet.is_empty alias.(diffblock).

  Definition is_empty_unary (inv:unary): bool :=
    ExprPairSet.is_empty inv.(lessdef) &&
    is_empty_alias inv.(alias) &&
    IdTSet.is_empty inv.(allocas) &&
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
         (fun (pp: PtrPair.t) =>
            let (x, y) := pp in TODO.filter_map Ptr.get_idTs [x ; y])
         (PtrPairSet.elements (alias.(noalias)))) ++
      IdTSet.elements allocas ++ IdTSet.elements private.

  Definition get_idTs (inv: t): list IdT.t :=
    let (src, tgt, maydiff) := inv in
    (get_idTs_unary src)
      ++ (get_idTs_unary tgt)
      ++ (IdTSet.elements maydiff).
End Invariant.

Module Infrule.
  Inductive t :=
  | add_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_const_not (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | add_dist_sub (z:IdT.t) (minusx:IdT.t) (minusy:ValueT.t) (w:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_sub (z:IdT.t) (minusy:IdT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | add_mask (z:IdT.t) (y:IdT.t) (y':IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | add_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | add_or_and (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (x:IdT.t) (y:IdT.t) (s:sz)
  | add_select_zero (z:IdT.t) (x:IdT.t) (y:IdT.t) (c:ValueT.t) (n:ValueT.t) (a:ValueT.t) (s:sz)
  | add_select_zero2 (z:IdT.t) (x:IdT.t) (y:IdT.t) (c:ValueT.t) (n:ValueT.t) (a:ValueT.t) (s:sz)
  | add_shift (y:IdT.t) (v:ValueT.t) (s:sz) 
  | add_signbit (x:IdT.t) (e1:ValueT.t) (e2:ValueT.t) (s:sz)
  | add_xor_and (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (x:IdT.t) (y:IdT.t) (s:sz)
  | add_zext_bool (x:IdT.t) (y:IdT.t) (b:ValueT.t) (c:INTEGER.t) (c':INTEGER.t) (sz:sz)
  | and_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | and_de_morgan (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | and_mone (z:ValueT.t) (x:ValueT.t) (s:sz)
  | and_not (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | and_or (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (s:sz)
  | and_or_const2 (z:IdT.t) (y:IdT.t) (y':IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (sz:sz)
  | and_same (z:ValueT.t) (x:ValueT.t) (s:sz)
  | and_true_bool (x:ValueT.t) (y:ValueT.t)
  | and_undef (z:ValueT.t) (x:ValueT.t) (s:sz)
  | and_xor_const (z:IdT.t) (y:IdT.t) (y':IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (sz:sz)
  | and_zero (z:ValueT.t) (x:ValueT.t) (s:sz)
  | and_or_not1 (z:IdT.t) (x:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | bop_associative (x:IdT.t) (y:IdT.t) (z:IdT.t) (opcode:bop) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (s:sz)
  | bop_distributive_over_selectinst (opcode:bop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (bopsz:sz) (selty:typ)
  | bop_distributive_over_selectinst2 (opcode:bop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (bopsz:sz) (selty:typ)
  | bitcastptr (v:ValueT.t) (v':ValueT.t) (bitcastinst:Expr.t)
  | bitcast_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_load (ptr:ValueT.t) (ptrty:typ) (v1:ValueT.t) (ptrty2:typ) (v2:ValueT.t) (a:align)
  | bitcast_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_fptosi (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_fptoui (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_fptrunc (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_inttoptr (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_ptrtoint (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_sext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_sametype (src:ValueT.t) (dst:ValueT.t) (ty:typ)
  | bitcast_sitofp (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_trunc (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_uitofp (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_zext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | diffblock_global_alloca (gx:const) (y:IdT.t)
  | diffblock_global_global (gx:const) (gy:const)
  | diffblock_lessthan (x:ValueT.t) (y:ValueT.t) (x':ValueT.t) (y':ValueT.t)
  | diffblock_noalias (x:ValueT.t) (y:ValueT.t) (x':Ptr.t) (y':Ptr.t)
  | fadd_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (fty:floating_point)
  | fbop_distributive_over_selectinst (opcode:fbop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (fbopty:floating_point) (selty:typ)
  | fbop_distributive_over_selectinst2 (opcode:fbop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (fbopty:floating_point) (selty:typ)
  | fpext_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fpext_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptosi_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptosi_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptoui_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptoui_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptrunc_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptrunc_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | gepzero (v:ValueT.t) (v':ValueT.t) (gepinst:Expr.t)
  | gep_inbounds_remove (gepinst:Expr.t)
  | inttoptr_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | inttoptr_ptrtoint (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | inttoptr_zext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | inttoptr_load (ptr:ValueT.t) (intty:typ) (v1:ValueT.t) (ptrty:typ) (v2:ValueT.t) (a:align)
  | lessthan_undef (ty:typ) (v:ValueT.t)
  | lessthan_undef_tgt (ty:typ) (v:ValueT.t)
  | mul_bool (z:IdT.t) (x:IdT.t) (y:IdT.t)
  | mul_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | mul_mone (z:IdT.t) (x:ValueT.t) (sz:sz)
  | mul_neg (z:IdT.t) (mx:ValueT.t) (my:ValueT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)  
  | mul_shl (z:IdT.t) (y:IdT.t) (x:ValueT.t) (a:ValueT.t) (sz:sz)
  | neg_val (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | or_and (z:ValueT.t) (y:ValueT.t) (x:ValueT.t) (a:ValueT.t) (s:sz)
  | or_and_xor (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | or_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | or_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | or_false (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | or_mone (z:ValueT.t) (a:ValueT.t) (s:sz)
  | or_not (z:ValueT.t) (y:ValueT.t) (x:ValueT.t) (s:sz)
  | or_or  (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | or_or2  (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (y':ValueT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | or_same (z:ValueT.t) (a:ValueT.t) (s:sz)
  | or_undef (z:ValueT.t) (a:ValueT.t) (s:sz)
  | or_xor (w:ValueT.t) (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | or_xor2 (z:ValueT.t) (x1:ValueT.t) (y1:ValueT.t) (x2:ValueT.t) (y2:ValueT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | or_xor3 (z:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | or_xor4 (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (nb:ValueT.t) (s:sz)
  | or_zero (z:ValueT.t) (a:ValueT.t) (s:sz)
  | ptrtoint_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | ptrtoint_load (ptr:ValueT.t) (ptrty:typ) (v1:ValueT.t) (intty:typ) (v2:ValueT.t) (a:align)
  | replace_rhs (x:IdT.t) (y:ValueT.t) (e1:Expr.t) (e2:Expr.t) (e2':Expr.t)
  | replace_rhs_opt	(x:IdT.t) (y:ValueT.t) (e1:Expr.t) (e2:Expr.t) (e2':Expr.t)
  | rem_neg (z:IdT.t) (my:ValueT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | sdiv_mone (z:IdT.t) (x:ValueT.t) (sz:sz)
  | sdiv_sub_srem (z:IdT.t) (b:IdT.t) (a:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | sext_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | sext_sext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | sext_zext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | shift_undef1 (z:ValueT.t) (y:ValueT.t) (s:sz)
  | shift_undef2 (z:ValueT.t) (y:ValueT.t) (c:INTEGER.t) (s:sz)
  | shift_zero1 (z:ValueT.t) (y:ValueT.t) (s:sz)
  | shift_zero2 (z:ValueT.t) (y:ValueT.t) (s:sz)
  | sitofp_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | sitofp_sext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | sitofp_zext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | sub_add (z:IdT.t) (minusy:ValueT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | sub_const_add (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (sz:sz)
  | sub_const_not (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | sub_mone (z:IdT.t) (x:ValueT.t) (s:sz) 
  | sub_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | sub_or_xor (z:IdT.t) (a:ValueT.t) (b:ValueT.t) (x:IdT.t) (y:IdT.t) (s:sz)
  | sub_remove (z:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz:sz)
  | sub_sdiv (z:IdT.t) (y:IdT.t) (x:ValueT.t) (c:INTEGER.t) (c':INTEGER.t) (sz:sz)
  | sub_sub (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (w:ValueT.t) (s:sz)
  | sub_shl (z:IdT.t) (x:ValueT.t) (y:IdT.t) (mx:ValueT.t) (a:ValueT.t) (sz:sz)
  | transitivity (e1:Expr.t) (e2:Expr.t) (e3:Expr.t)
  | transitivity_tgt (e1:Expr.t) (e2:Expr.t) (e3:Expr.t)
  | transitivity_pointer_lhs (p:ValueT.t) (q:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | transitivity_pointer_rhs (p:ValueT.t) (q:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | trunc_onebit (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (orgsz:sz)
  | trunc_zext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | trunc_sext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | trunc_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | trunc_ptrtoint (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | trunc_trunc (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | substitute (x:IdT.t) (y:ValueT.t) (e:Expr.t)
  | substitute_rev (x:IdT.t) (y:ValueT.t) (e:Expr.t)
  | udiv_sub_urem (z:IdT.t) (b:IdT.t) (a:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | udiv_zext (z:IdT.t) (x:IdT.t) (y:IdT.t) (k:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz1:sz) (sz2:sz)
  | udiv_zext_const (z:IdT.t) (x:IdT.t) (c:INTEGER.t) (k:IdT.t) (a:ValueT.t) (sz1:sz) (sz2:sz)
  | uitofp_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | uitofp_zext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | urem_zext (z:IdT.t) (x:IdT.t) (y:IdT.t) (k:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz1:sz) (sz2:sz)
  | urem_zext_const (z:IdT.t) (x:IdT.t) (c:INTEGER.t) (k:IdT.t) (a:ValueT.t) (sz1:sz) (sz2:sz)
  | xor_commutative (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | xor_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | xor_not (z:ValueT.t) (y:ValueT.t) (x:ValueT.t) (s:sz)
  | xor_same (z:ValueT.t) (a:ValueT.t) (s:sz)
  | xor_undef (z:ValueT.t) (a:ValueT.t) (s:sz)
  | xor_zero (z:ValueT.t) (a:ValueT.t) (s:sz)
  | zext_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | zext_trunc_and (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (w:ValueT.t) (c:const) (s:sz) (s':sz)
  | zext_trunc_and_xor (z:ValueT.t) (x:ValueT.t) (v:ValueT.t) (w:ValueT.t) (y:ValueT.t) (y':ValueT.t) (c:const) (s:sz) (s':sz)
  | zext_xor (z:ValueT.t) (y:ValueT.t) (y':ValueT.t) (x:ValueT.t)
  | zext_zext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | intro_ghost (x:Expr.t) (g:id)
  | intro_eq (x:ValueT.t)
  | intro_eq_tgt (x:ValueT.t)
  | icmp_inverse (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (v:INTEGER.t)
  | icmp_inverse_rhs (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (v:INTEGER.t)
  | icmp_swap_operands (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t)
  | icmp_eq_add_add (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_eq_same (ty:typ) (x:ValueT.t) (y:ValueT.t)
  | icmp_eq_sub_sub (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_eq_xor_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_eq_xor_xor (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_eq_sub (z:ValueT.t) (x:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_eq_srem (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | icmp_ne_add_add (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ne_sub (z:ValueT.t) (x:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ne_sub_sub (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ne_srem (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | icmp_ne_xor (z:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ne_xor_xor (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_neq_same (ty:typ) (x:ValueT.t) (y:ValueT.t)
  | icmp_sge_or_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_sgt_and_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_sle_or_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_slt_and_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_uge_or_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ugt_and_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ule_or_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ult_and_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)  
  | implies_false (x:const) (y:const)

(* Updated semantics of rules should be located above this line *)

  | remove_maydiff (v:IdT.t) (e:Expr.t)
  | remove_maydiff_rhs (v:IdT.t) (e:IdT.t)
  | eq_generate_same_heap_value (x:IdT.t) (p:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | stash_variable (z:IdT.t) (v:id)
  | add_mul_fold (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | add_distributive (z:IdT.t) (x:IdT.t) (y:IdT.t) (w:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  | rem_neg2 (z:IdT.t) (sz:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | select_trunc (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (sz1:sz) (sz2:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  | select_add (z:IdT.t) (x:IdT.t) (y:IdT.t) (z':IdT.t) (sz1:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t) (cond:ValueT.t)
  | select_const_gt (z:IdT.t) (b:IdT.t) (sz1:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
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
