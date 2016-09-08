Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.

Require Import Exprs.
Require Import Decs.
Require Import TODO.

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
    unique: atoms;
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
      invariant.(unique)
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
      invariant.(unique)
      invariant.(private).

  Definition update_diffblock (f:ValueTPairSet.t -> ValueTPairSet.t) (invariant:unary): unary :=
    update_alias (update_diffblock_rel f) invariant.

  Definition update_noalias (f:PtrPairSet.t -> PtrPairSet.t) (invariant:unary): unary :=
    update_alias (update_noalias_rel f) invariant.

  Definition update_unique (f:atoms -> atoms) (invariant:unary): unary :=
    mk_unary
      invariant.(lessdef)
      invariant.(alias)
      (f invariant.(unique))
      invariant.(private).

  Definition update_private (f:IdTSet.t -> IdTSet.t) (invariant:unary): unary :=
    mk_unary
      invariant.(lessdef)
      invariant.(alias)
      invariant.(unique)
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

  Definition is_unique_value (inv0:unary) (value:ValueT.t): bool :=
    match value with
    | ValueT.id idt =>
      (Tag.eq_dec idt.(fst) Tag.physical) &&
      (AtomSetImpl.mem idt.(snd) inv0.(unique))
    | _ => false
    end.

  Definition is_unique_ptr (inv0:unary) (ptr:Ptr.t): bool :=
    is_unique_value inv0 ptr.(fst).

  Definition implies_noalias (inv0:unary) (na0 na:PtrPairSet.t): bool :=
    flip PtrPairSet.for_all na
      (fun pp =>
         (negb (Ptr.eq_dec pp.(fst) pp.(snd)) &&
           is_unique_ptr inv0 pp.(fst) || is_unique_ptr inv0 pp.(snd)) ||
         (PtrPairSet.mem pp na0)
      ).

  Definition values_diffblock_from_unique (v:ValueT.t): bool :=
    match v with
    | ValueT.id (Tag.physical, _) => true
    | ValueT.const _ => true
    | _ => false
    end.

  Definition implies_diffblock (inv0:unary) (db0 db:ValueTPairSet.t): bool :=
    flip ValueTPairSet.for_all db
      (fun vp =>
         ((negb (ValueT.eq_dec vp.(fst) vp.(snd))) &&
           ((is_unique_value inv0 vp.(fst) &&
               values_diffblock_from_unique vp.(snd)) ||
            (is_unique_value inv0 vp.(snd) &&
               values_diffblock_from_unique vp.(fst)))) ||
         (ValueTPairSet.mem vp db0)
      ).

  Definition implies_alias inv0 (alias0 alias:aliasrel): bool :=
    implies_noalias inv0 (alias0.(noalias)) (alias.(noalias)) &&
    implies_diffblock inv0 (alias0.(diffblock)) (alias.(diffblock)).

  (* TODO: name? (trivial, ..) *)
  Definition syntactic_lessdef (e1 e2:Expr.t): bool :=
    (Expr.eq_dec e1 e2) ||
      (match e1, e2 with
       | Expr.value (ValueT.const (const_undef ty)),
         Expr.value v => true
       | _, _ => false
       end).

  Definition implies_lessdef (inv0 inv:ExprPairSet.t): bool :=
    flip ExprPairSet.for_all inv
         (fun q =>
            flip ExprPairSet.exists_ inv0
                 (fun p =>
                    (Expr.eq_dec p.(fst) q.(fst)) &&
                      (syntactic_lessdef p.(snd) q.(snd)))).

  Definition implies_unary (inv0 inv:unary): bool :=
    implies_lessdef inv0.(lessdef) inv.(lessdef) &&
    implies_alias inv0 (inv0.(alias)) (inv.(alias)) &&
    AtomSetImpl.subset (inv.(unique)) (inv0.(unique)) &&
    IdTSet.subset (inv.(private)) (inv0.(private)).

  Definition has_false (inv: t): bool :=
    (ExprPairSet.mem false_encoding inv.(src).(lessdef)).

  Definition implies (inv0 inv:t): bool :=
    (has_false inv0)
    || ((implies_unary (inv0.(src)) (inv.(src)))
          && implies_unary (inv0.(tgt)) (inv.(tgt))
          && IdTSet.subset (inv0.(maydiff)) (inv.(maydiff))).

  Definition is_noalias (inv:unary) (p1:Ptr.t) (p2:Ptr.t) :=
    flip PtrPairSet.exists_
         inv.(alias).(noalias)
      (fun pp =>
           (Ptr.eq_dec p1 pp.(fst) && Ptr.eq_dec p2 pp.(snd)) ||
           (Ptr.eq_dec p1 pp.(snd) && Ptr.eq_dec p2 pp.(fst))).

  Definition is_diffblock (inv:unary) (p1:Ptr.t) (p2:Ptr.t) :=
    flip ValueTPairSet.exists_
         inv.(alias).(diffblock)
      (fun vp =>
         (ValueT.eq_dec p1.(fst) vp.(fst) && ValueT.eq_dec p2.(fst) vp.(snd)) ||
         (ValueT.eq_dec p1.(fst) vp.(snd) && ValueT.eq_dec p2.(fst) vp.(fst))).

  Definition not_in_maydiff (inv:t) (value:ValueT.t): bool :=
    match value with
    | ValueT.id id =>
      negb (IdTSet.mem id inv.(maydiff))
    | ValueT.const _ => true
    end.

  Definition not_in_maydiff_expr (inv:t) (expr: Expr.t): bool :=
    List.forallb (not_in_maydiff inv) (Expr.get_valueTs expr).

  Definition get_lhs (inv:ExprPairSet.t) (rhs:Expr.t): ExprPairSet.t :=
    flip ExprPairSet.filter inv
         (fun (p: ExprPair.t) => Expr.eq_dec rhs p.(snd)).
      
  Definition get_rhs (inv:ExprPairSet.t) (lhs:Expr.t): ExprPairSet.t :=
    flip ExprPairSet.filter inv
       (fun (p: ExprPair.t) => Expr.eq_dec lhs p.(fst)).

  Definition inject_value (inv:t) (value_src value_tgt:ValueT.t): bool :=
    (ValueT.eq_dec value_src value_tgt && not_in_maydiff inv value_src) ||
    (ExprPairSet.mem (Expr.value value_src, Expr.value value_tgt) inv.(tgt).(lessdef) && not_in_maydiff inv value_src) ||
    (ExprPairSet.mem (Expr.value value_src, Expr.value value_tgt) inv.(src).(lessdef) && not_in_maydiff inv value_tgt) ||
    (ExprPairSet.exists_
       (fun (p: ExprPair.t) => 
          ((ExprPairSet.mem (p.(snd), Expr.value value_tgt) inv.(tgt).(lessdef)) &&
           (not_in_maydiff_expr inv p.(snd))))
       (get_rhs inv.(src).(lessdef) (Expr.value value_src))).

  (* On the definition of Expr.same_modulo_value *)
  (* There was a debate between @alxest and @jeehoonkang *)
  (* [here](https://github.com/snu-sf/llvmberry/pull/295#discussion_r76530070). *)
  (* I, @alxest, insist current form is much more readable. *)
  (* Expr.same_modulo_value only requires expr, and reader do not need to care *)
  (* about what f or data is and how it appears inside definition. *)
  (* Also, the name same_module_value very explicitly shows what it do. *)
  (* Actually, during this separation, I found a bug on original code's gep case. *)
  (* @jeehoonkang's concern was that there should be a provable spec for every definition. *)
  (* I think it is ok because its spec clearly appears on namee, *)
  (* and requiring all primitive definitions to have such spec is impossible. *)
  (* Also, all usage of this primitive definition is deep_check_expr, *)
  (* so this change does not increase definition spilled out without provable spec *)
  (* The conclusion was, keep this form and if we meet any difficulty during proving, *)
  (* come back then *)
  Definition deep_check_expr
             {A: Type} (f: A -> ValueT.t -> ValueT.t -> bool)
             (data: A) (e1 e2:Expr.t): bool :=
    (Expr.same_modulo_value e1 e2)
      && (list_forallb2 (f data) (Expr.get_valueTs e1) (Expr.get_valueTs e2)).

  Definition inject_expr (inv: Invariant.t) (es et:Expr.t): bool :=
    deep_check_expr Invariant.inject_value inv es et.

  Definition lessdef_expr (e: (Expr.t * Expr.t)) (lessdef: ExprPairSet.t): bool :=
    ExprPairSet.mem e lessdef
    || (deep_check_expr
          (fun data v1 v2 => ExprPairSet.mem (Expr.value v1, Expr.value v2) data)
          lessdef e.(fst) e.(snd)).

  Definition is_empty_alias (alias:aliasrel): bool :=
    PtrPairSet.is_empty alias.(noalias) &&
    ValueTPairSet.is_empty alias.(diffblock).

  Definition is_empty_unary (inv:unary): bool :=
    ExprPairSet.is_empty inv.(lessdef) &&
    is_empty_alias inv.(alias) &&
    AtomSetImpl.is_empty inv.(unique) &&
    IdTSet.is_empty inv.(private).

  Definition is_empty (inv:t): bool :=
    is_empty_unary inv.(src) &&
    is_empty_unary inv.(tgt) &&
    IdTSet.is_empty inv.(maydiff).

  Definition get_idTs_unary (u: unary): list IdT.t :=
    List.concat
      (List.map
         (fun (p: ExprPair.t) =>
            Expr.get_idTs p.(fst) ++ Expr.get_idTs p.(snd))
         (ExprPairSet.elements u.(lessdef))) ++
    List.concat
      (List.map
         (fun (pp: PtrPair.t) =>
            TODO.filter_map Ptr.get_idTs [pp.(fst) ; pp.(snd)])
         (PtrPairSet.elements (u.(alias).(noalias)))) ++
      (List.map (IdT.lift Tag.physical) (AtomSetImpl.elements u.(unique))) ++
      IdTSet.elements u.(private).

  Definition get_idTs (inv: t): list IdT.t :=
    (get_idTs_unary inv.(src))
      ++ (get_idTs_unary inv.(tgt))
      ++ (IdTSet.elements inv.(maydiff)).
End Invariant.

Module Infrule.
  Inductive t :=
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
  | bop_commutative (e:Expr.t) (opcode:bop) (x:ValueT.t) (y:ValueT.t) (s:sz)
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
  | mul_mone (z:IdT.t) (x:ValueT.t) (sz:sz)
  | mul_neg (z:IdT.t) (mx:ValueT.t) (my:ValueT.t) (x:ValueT.t) (y:ValueT.t) (s:sz)  
  | mul_shl (z:IdT.t) (y:IdT.t) (x:ValueT.t) (a:ValueT.t) (sz:sz)
  | neg_val (c1:INTEGER.t) (c2:INTEGER.t) (s:sz)
  | or_and (z:ValueT.t) (y:ValueT.t) (x:ValueT.t) (a:ValueT.t) (s:sz)
  | or_and_xor (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
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
  | select_icmp_eq (z y x v:ValueT.t) (c:const) (cty:typ)
  | select_icmp_eq_xor1 (z z' v x u w:ValueT.t) (c c':INTEGER.t) (s:sz)
  | select_icmp_eq_xor2 (z z' v x u w:ValueT.t) (c:INTEGER.t) (s:sz)
  | select_icmp_ne (z y x v:ValueT.t) (c:const) (cty:typ)
  | select_icmp_ne_xor1 (z z' v x u w:ValueT.t) (c c':INTEGER.t) (s:sz)
  | select_icmp_ne_xor2 (z z' v x u w:ValueT.t) (c:INTEGER.t) (s:sz)
  | select_icmp_sgt_const (z:IdT.t) (y x:ValueT.t) (c c':INTEGER.t) (selcomm:bool) (s:sz) 
  | select_icmp_sgt_xor1 (z z' v x u:ValueT.t) (c c':INTEGER.t) (s:sz)
  | select_icmp_sgt_xor2 (z z' v x u:ValueT.t) (c:INTEGER.t) (s:sz)
  | select_icmp_slt_const (z:IdT.t) (y x:ValueT.t) (c c':INTEGER.t) (selcomm:bool) (s:sz) 
  | select_icmp_slt_xor1 (z z' v x u:ValueT.t) (c c':INTEGER.t) (s:sz)
  | select_icmp_slt_xor2 (z z' v x u:ValueT.t) (c:INTEGER.t) (s:sz)
  | select_icmp_slt_one (z:ValueT.t) (y:IdT.t) (x:ValueT.t) (c c':INTEGER.t) (s:sz) 
  | select_icmp_ugt_const (z:IdT.t) (y x:ValueT.t) (c c':INTEGER.t) (selcomm:bool) (s:sz) 
  | select_icmp_ult_const (z:IdT.t) (y x:ValueT.t) (c c':INTEGER.t) (selcomm:bool) (s:sz) 
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
  | substitute_tgt (x:IdT.t) (y:ValueT.t) (e:Expr.t)
  | udiv_sub_urem (z:IdT.t) (b:IdT.t) (a:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | udiv_zext (z:IdT.t) (x:IdT.t) (y:IdT.t) (k:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz1:sz) (sz2:sz)
  | udiv_zext_const (z:IdT.t) (x:IdT.t) (c:INTEGER.t) (k:IdT.t) (a:ValueT.t) (sz1:sz) (sz2:sz)
  | uitofp_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | uitofp_zext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | urem_zext (z:IdT.t) (x:IdT.t) (y:IdT.t) (k:IdT.t) (a:ValueT.t) (b:ValueT.t) (sz1:sz) (sz2:sz)
  | urem_zext_const (z:IdT.t) (x:IdT.t) (c:INTEGER.t) (k:IdT.t) (a:ValueT.t) (sz1:sz) (sz2:sz)
  | xor_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (sz:sz)
  | xor_not (z:ValueT.t) (y:ValueT.t) (x:ValueT.t) (s:sz)
  | xor_same (z:ValueT.t) (a:ValueT.t) (s:sz)
  | xor_undef (z:ValueT.t) (a:ValueT.t) (s:sz)
  | xor_zero (z:ValueT.t) (a:ValueT.t) (s:sz)
  | zext_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | zext_trunc_and (z:ValueT.t) (x:ValueT.t) (y:ValueT.t) (w:ValueT.t) (c:const) (s:sz) (s':sz)
  | zext_trunc_and_xor (z:ValueT.t) (x:ValueT.t) (v:ValueT.t) (w:ValueT.t) (y:ValueT.t) (y':ValueT.t) (c:const) (s:sz) (s':sz)
  | zext_xor (z:ValueT.t) (y:ValueT.t) (y':ValueT.t) (x:ValueT.t) (s:sz)
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
End ValidationHint.
