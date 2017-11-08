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

  Definition clear_idt_alias (idt0: IdT.t) (t: aliasrel): aliasrel :=
    mk_aliasrel (ValueTPairSet.clear_idt idt0 t.(diffblock))
                (PtrPairSet.clear_idt idt0 t.(noalias))
  .

  Definition clear_idt_unary (idt0: IdT.t) (invst0: unary): unary :=
    mk_unary
      ((ExprPairSet.clear_idt idt0) invst0.(lessdef))
      (clear_idt_alias idt0 invst0.(alias))
      invst0.(unique)
      (IdTSet.clear_idt idt0 invst0.(private))
  .

  Definition clear_idt (idt0: IdT.t) (invst0: t): t :=
    mk (clear_idt_unary idt0 invst0.(src))
       (clear_idt_unary idt0 invst0.(tgt))
       (IdTSet.clear_idt idt0 invst0.(maydiff))
  .

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

  Definition values_diffblock_from_unique (v:ValueT.t): bool :=
    match v with
    | ValueT.id (Tag.physical, _) => true
    | ValueT.const _ => true
    | _ => false
    end.

  Definition diffblock_by_unique (inv0:unary) (v1 v2:ValueT.t): bool :=
    (negb (ValueTFacts.eq_dec_l v1 v2)) &&
    ((is_unique_value inv0 v1 && values_diffblock_from_unique v2) ||
     (is_unique_value inv0 v2 && values_diffblock_from_unique v1)).

  Definition implies_noalias (inv0:unary) (na0 na:PtrPairSet.t): bool :=
    flip PtrPairSet.for_all na
      (fun pp =>
         (diffblock_by_unique inv0 pp.(fst).(fst) pp.(snd).(fst)) ||
         (PtrPairSet.mem pp na0)).

  Definition implies_diffblock (inv0:unary) (db0 db:ValueTPairSet.t): bool :=
    flip ValueTPairSet.for_all db
      (fun vp =>
         (diffblock_by_unique inv0 vp.(fst) vp.(snd)) ||
         (ValueTPairSet.mem vp db0)).

  Definition implies_alias inv0 (alias0 alias:aliasrel): bool :=
    implies_noalias inv0 (alias0.(noalias)) (alias.(noalias)) &&
    implies_diffblock inv0 (alias0.(diffblock)) (alias.(diffblock)).

  Definition implies_lessdef (inv0 inv:ExprPairSet.t): bool :=
    flip ExprPairSet.for_all inv
         (fun p => flip ExprPairSet.exists_ inv0 (ExprPairFacts.eq_dec_l p))
  .

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
           (PtrFacts.eq_dec_l p1 pp.(fst) && PtrFacts.eq_dec_l p2 pp.(snd)) ||
           (PtrFacts.eq_dec_l p1 pp.(snd) && PtrFacts.eq_dec_l p2 pp.(fst))).

  Definition is_diffblock (inv:unary) (p1:Ptr.t) (p2:Ptr.t) :=
    flip ValueTPairSet.exists_
         inv.(alias).(diffblock)
      (fun vp =>
         (ValueTFacts.eq_dec_l p1.(fst) vp.(fst) && ValueTFacts.eq_dec_l p2.(fst) vp.(snd)) ||
         (ValueTFacts.eq_dec_l p1.(fst) vp.(snd) && ValueTFacts.eq_dec_l p2.(fst) vp.(fst))).

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
         (fun (p: ExprPair.t) => ExprFacts.eq_dec_l rhs p.(snd)).
      
  Definition get_rhs (inv:ExprPairSet.t) (lhs:Expr.t): ExprPairSet.t :=
    flip ExprPairSet.filter inv
       (fun (p: ExprPair.t) => ExprFacts.eq_dec_l lhs p.(fst)).

  Definition inject_value (inv:t) (value_src value_tgt:ValueT.t): bool :=
    (ValueTFacts.eq_dec_l value_src value_tgt && not_in_maydiff inv value_src) ||
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

  Local Notation "x [++] y" := (IdTSet.union x y) (at level 70, no associativity).

  Definition get_idTs_lessdef (ld: ExprPairSet.t): IdTSet.t :=
    ExprPairSet.fold (fun i s => IdTSet.add_list (ExprPair.get_idTs i) s) ld IdTSet.empty
  .

  Definition get_idTs_noalias (noal: PtrPairSet.t): IdTSet.t :=
    PtrPairSet.fold (fun i s => IdTSet.add_list (PtrPair.get_idTs i) s) noal IdTSet.empty
  .

  Definition get_idTs_diffblock (db: ValueTPairSet.t): IdTSet.t :=
    ValueTPairSet.fold (fun i s => IdTSet.add_list (ValueTPair.get_idTs i) s) db IdTSet.empty
  .

  Definition get_idTs_alias (ar: aliasrel): IdTSet.t :=
    (get_idTs_noalias ar.(noalias)) [++] (get_idTs_diffblock ar.(diffblock))
  .

  Definition get_idTs_unique (uniq: atoms): IdTSet.t :=
    AtomSetImpl.fold (fun i s => IdTSet.add (IdT.lift Tag.physical i) s) uniq IdTSet.empty
  .

  Definition get_idTs_private (prvt: IdTSet.t): IdTSet.t :=
    prvt
  .

  Definition get_idTs_unary (u: unary): IdTSet.t :=
    (get_idTs_lessdef u.(lessdef))
      [++] (get_idTs_alias u.(alias))
      [++] (get_idTs_unique u.(unique))
      [++] (get_idTs_private u.(private)).

  Definition get_idTs (inv: t): IdTSet.t :=
    (get_idTs_unary inv.(src))
      [++] (get_idTs_unary inv.(tgt))
      [++] (inv.(maydiff)).

  (* Subset predicates *)

  Inductive Subset_unary (inv1 inv2: unary): Prop :=
  | Subset_unary_intro
      (SUBSET_LESSDEF: ExprPairSet.Subset inv1.(lessdef) inv2.(lessdef))
      (SUBSET_NOALIAS: ValueTPairSet.Subset inv1.(alias).(diffblock) inv2.(alias).(diffblock) /\
                       PtrPairSet.Subset inv1.(alias).(noalias) inv2.(alias).(noalias))
      (SUBSET_UNIQUE: AtomSetImpl.Subset inv1.(unique) inv2.(unique))
      (SUBSET_PRIVATE: IdTSet.Subset inv1.(private) inv2.(private))
  .

  Inductive Subset (inv1 inv2: t): Prop :=
  | Subset_intro
      (SUBSET_SRC: Subset_unary inv1.(src) inv2.(src))
      (SUBSET_TGT: Subset_unary inv1.(tgt) inv2.(tgt))
      (SUBSET_MAYDIFF: IdTSet.Subset inv2.(maydiff) inv1.(maydiff))
  .

  Definition getGvarIDs (ps: products) :=
    filter_map (fun p => match p with
                         | product_gvar gv => Some (getGvarID gv)
                         | _ => None
                         end) ps
  .

  Definition add_Gvar_IDs (ps: products) :=
    List.fold_right
      (fun id inv =>
         match lookupTypViaGIDFromProducts ps id with
         | Some (typ_pointer ty) =>
           ExprPairSet.add (Expr.value (ValueT.const (const_undef (typ_pointer ty))),
                            Expr.value (ValueT.const (const_gid ty id))) inv
         | _ => inv
         end)
      ExprPairSet.empty (getGvarIDs ps)
  .

  Definition add_Args_IDs (la: args) :=
    List.fold_right
      (fun id inv =>
         let ty := lookupTypViaIDFromArgs la id in
         match lookupTypViaIDFromArgs la id with
         | Some ty =>
           ExprPairSet.add (Expr.value (ValueT.const (const_undef ty)),
                            Expr.value (ValueT.id (Tag.physical, id))) inv
         | None => inv
         end)
      ExprPairSet.empty (getArgsIDs la)
  .

  Definition function_entry_inv (la_src la_tgt: args) (products_src products_tgt: products): t :=
    let inv_src :=
        ExprPairSet.union (add_Args_IDs la_src) (add_Gvar_IDs products_src) in
    let inv_tgt :=
        ExprPairSet.union (add_Args_IDs la_tgt) (add_Gvar_IDs products_tgt) in
    mk
      (mk_unary
         inv_src
         (mk_aliasrel
            ValueTPairSet.empty
            PtrPairSet.empty)
         AtomSetImpl.empty
         IdTSet.empty)
      (mk_unary
         inv_tgt
         (mk_aliasrel
            ValueTPairSet.empty
            PtrPairSet.empty)
         AtomSetImpl.empty
         IdTSet.empty)
      IdTSet.empty
  .
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
  | and_true_bool_tgt (x:ValueT.t) (y:ValueT.t)
  | and_undef (z:ValueT.t) (x:ValueT.t) (s:sz)
  | and_xor_const (z:IdT.t) (y:IdT.t) (y':IdT.t) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (sz:sz)
  | and_zero (z:ValueT.t) (x:ValueT.t) (s:sz)
  | and_or_not1 (z:IdT.t) (x:IdT.t) (y:IdT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | bop_associative (x:IdT.t) (y:IdT.t) (z:IdT.t) (opcode:bop) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t) (s:sz)
  | bop_commutative (e:Expr.t) (opcode:bop) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | bop_commutative_rev (e:Expr.t) (opcode:bop) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | bop_commutative_tgt (e:Expr.t) (opcode:bop) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | bop_commutative_rev_tgt (e:Expr.t) (opcode:bop) (x:ValueT.t) (y:ValueT.t) (s:sz)
  | fbop_commutative (e:Expr.t) (opcode:fbop) (x:ValueT.t) (y:ValueT.t) (fty:floating_point)
  | fbop_commutative_rev (e:Expr.t) (opcode:fbop) (x:ValueT.t) (y:ValueT.t) (fty:floating_point)
  | fbop_commutative_tgt (e:Expr.t) (opcode:fbop) (x:ValueT.t) (y:ValueT.t) (fty:floating_point)
  | fbop_commutative_rev_tgt (e:Expr.t) (opcode:fbop) (x:ValueT.t) (y:ValueT.t) (fty:floating_point)
  | bop_distributive_over_selectinst (opcode:bop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (bopsz:sz) (selty:typ)
  | bop_distributive_over_selectinst2 (opcode:bop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (bopsz:sz) (selty:typ)
  | bitcastptr (v':ValueT.t) (bitcastinst:Expr.t)
  | bitcast_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_bitcast_rev_tgt (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | bitcast_double_i64 (src:const) (tgt:INTEGER.t)
  | bitcast_load (ptr:ValueT.t) (ty:typ) (v1:ValueT.t) (ty2:typ) (v2:ValueT.t) (a:align)
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
  | diffblock_unique (x:IdT.t) (y:IdT.t)
  | diffblock_global_unique (gx:const) (y:IdT.t)
  | diffblock_global_global (gx:const) (gy:const)
  | diffblock_lessthan (x:ValueT.t) (y:ValueT.t) (x':ValueT.t) (y':ValueT.t)
  | diffblock_noalias (x:ValueT.t) (y:ValueT.t) (x':Ptr.t) (y':Ptr.t)
  | fadd_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (fty:floating_point)
  | fbop_distributive_over_selectinst (opcode:fbop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (fbopty:floating_point) (selty:typ)
  | fbop_distributive_over_selectinst2 (opcode:fbop) (r:IdT.t) (s:IdT.t) (t':IdT.t) (t0:IdT.t) (x:ValueT.t) (y:ValueT.t) (z:ValueT.t) (c:ValueT.t) (fbopty:floating_point) (selty:typ)
  | fmul_commutative_tgt (z:IdT.t) (x:ValueT.t) (y:ValueT.t) (fty:floating_point)
  | fpext_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fpext_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptosi_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptosi_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptoui_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptoui_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptrunc_bitcast (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | fptrunc_fpext (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | gepzero (v':ValueT.t) (gepinst:Expr.t)
  | gep_inbounds_remove (gepinst:Expr.t)
  | gep_inbounds_remove_tgt (gepinst:Expr.t)
  | gep_inbounds_add (v:ValueT.t) (ptr:ValueT.t) (loadty:typ) (al:align) (e:Expr.t)
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
  | or_false_tgt (x:ValueT.t) (y:ValueT.t) (sz:sz)
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
  | ptrtoint_inttoptr (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | ptrtoint_load (ptr:ValueT.t) (ptrty:typ) (v1:ValueT.t) (intty:typ) (v2:ValueT.t) (a:align)
  | ptrtoint_zero (ptrty:typ) (intty:typ)
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
  | sext_trunc_ashr (z x x' v:ValueT.t) (s1 s2:sz) (i3:INTEGER.t)
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
  | trunc_trunc_rev_tgt (src:ValueT.t) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (dstty:typ)
  | trunc_load_bitcast_rev_tgt (src:ValueT.t) (mid1:ValueT.t) (mid2:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (a:align)
  | trunc_load_const_bitcast_rev_tgt (src:const) (mid:ValueT.t) (dst:ValueT.t) (srcty:typ) (midty:typ) (a:align)
  | substitute (x:IdT.t) (y:ValueT.t) (e:Expr.t)
  | substitute_rev (x:IdT.t) (y:ValueT.t) (e:Expr.t)
  | substitute_tgt (x:IdT.t) (y:ValueT.t) (e:Expr.t)
  | substitute_rev_tgt (x:IdT.t) (y:ValueT.t) (e:Expr.t)
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
  | intro_ghost_src (x:Expr.t) (g:id)
  | intro_ghost (x:Expr.t) (g:id)
  | intro_eq (x:Expr.t)
  | intro_eq_tgt (x:Expr.t)
  | icmp_inverse (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (v:INTEGER.t)
  | icmp_inverse_rhs (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (v:INTEGER.t)
  | icmp_inverse_tgt (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (v:INTEGER.t)
  | icmp_inverse_rhs_tgt (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (v:INTEGER.t)
  | icmp_swap_operands (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (e:Expr.t)
  | icmp_swap_operands_rev (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (e:Expr.t)
  | icmp_swap_operands_tgt (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (e:Expr.t)
  | icmp_swap_operands_rev_tgt (c:cond) (ty:typ) (x:ValueT.t) (y:ValueT.t) (e:Expr.t)
  | fcmp_swap_operands (c:fcond) (fty:floating_point) (x:ValueT.t) (y:ValueT.t) (e:Expr.t)
  | fcmp_swap_operands_rev (c:fcond) (fty:floating_point) (x:ValueT.t) (y:ValueT.t) (e:Expr.t)
  | fcmp_swap_operands_tgt (c:fcond) (fty:floating_point) (x:ValueT.t) (y:ValueT.t) (e:Expr.t)
  | fcmp_swap_operands_rev_tgt (c:fcond) (fty:floating_point) (x:ValueT.t) (y:ValueT.t) (e:Expr.t)
  | icmp_eq_add_add (z:ValueT.t) (w:ValueT.t) (x:ValueT.t) (y:ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_eq_same (ty:typ) (x:ValueT.t) (y:ValueT.t)
  | icmp_eq_same_tgt (ty:typ) (x:ValueT.t) (y:ValueT.t)
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
  | icmp_neq_same_tgt (ty:typ) (x:ValueT.t) (y:ValueT.t)
  | icmp_sge_or_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_sgt_and_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_sle_or_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_slt_and_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_uge_or_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ugt_and_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ule_or_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)
  | icmp_ult_and_not (z:ValueT.t) (z':ValueT.t) (a:ValueT.t) (b:ValueT.t) (s:sz)  
  | implies_false (x:const) (y:const)
  (* temporary *)
  | old_reduce_maydiff
  | old_reduce_maydiff_non_physical

  (* Updated semantics of rules should be located above this line *)
  .

  Definition is_arithmetic (infrule : t) : bool :=
    match infrule with
    | transitivity _ _ _ => false
    | transitivity_tgt _ _ _ => false
    | transitivity_pointer_lhs _ _ _ _ _ => false
    | transitivity_pointer_rhs _ _ _ _ _ => false
    | diffblock_unique _ _ => false
    | diffblock_global_unique _ _ => false
    | diffblock_global_global _ _ => false
    | diffblock_lessthan _ _ _ _ => false
    | diffblock_noalias _ _ _ _ => false
    | substitute _ _ _ => false
    | substitute_rev _ _ _ => false
    | substitute_tgt _ _ _ => false
    | intro_ghost_src _ _ => false
    | intro_ghost _ _ => false
    | intro_eq _ => false
    | intro_eq_tgt _ => false
    | implies_false _ _ => false
    | _ => true
    end.

  Definition is_used_outside_instcombine (infrule : t) :bool :=
    match infrule with
    | intro_ghost _ _ => true
    | transitivity _ _ _ => true
    | transitivity_tgt _ _ _ => true
    | intro_eq_tgt _ => true
    | substitute _ _ _ => true
    | substitute_rev _ _ _ => true
    | substitute_tgt _ _ _ => true
    | gep_inbounds_remove _ => true
    | and_true_bool _ _ => true
    | and_true_bool_tgt _ _ => true
    | or_false _ _ _ => true
    | or_false_tgt _ _ _ => true
    | icmp_eq_same _ _ _ => true
    | icmp_neq_same _ _ _ => true
    | icmp_eq_same_tgt _ _ _ => true
    | icmp_neq_same_tgt _ _ _ => true
    | bop_commutative _ _ _ _ _ => true
    | bop_commutative_tgt _ _ _ _ _ => true
    | bop_commutative_rev _ _ _ _ _ => true
    | bop_commutative_rev_tgt _ _ _ _ _ => true
    | fbop_commutative _ _ _ _ _ => true
    | fbop_commutative_tgt _ _ _ _ _ => true
    | fbop_commutative_rev _ _ _ _ _ => true
    | fbop_commutative_rev_tgt _ _ _ _ _ => true
    | icmp_swap_operands _ _ _ _ _ => true
    | icmp_swap_operands_tgt _ _ _ _ _ => true
    | icmp_swap_operands_rev _ _ _ _ _ => true
    | icmp_swap_operands_rev_tgt _ _ _ _ _ => true
    | fcmp_swap_operands _ _ _ _ _ => true
    | fcmp_swap_operands_tgt _ _ _ _ _ => true
    | fcmp_swap_operands_rev _ _ _ _ _ => true
    | fcmp_swap_operands_rev_tgt _ _ _ _ _ => true
    | icmp_inverse _ _ _ _ _ => true
    | icmp_inverse_tgt _ _ _ _ _ => true
    | icmp_inverse_rhs _ _ _ _ _ => true
    | icmp_inverse_rhs_tgt _ _ _ _ _ => true
    | trunc_trunc_rev_tgt _ _ _ _ _ _ => true
    | bitcast_bitcast_rev_tgt _ _ _ _ _ _ => true
    | trunc_load_const_bitcast_rev_tgt _ _ _ _ _ _ => true
    | trunc_load_bitcast_rev_tgt _ _ _ _ _ _ _ => true
    | lessthan_undef _ _ => true
    | lessthan_undef_tgt _ _ => true
    | _ => false
    end
  .

  Definition is_of_interest (infrule : t) : bool :=
    (negb (is_arithmetic infrule)) && (is_used_outside_instcombine infrule).
  
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

  Definition update_invariant_after_phinodes (f:Invariant.t -> Invariant.t) (blockinv: stmts): stmts :=
    mk_stmts
      blockinv.(phinodes)
      (f blockinv.(invariant_after_phinodes))
      blockinv.(cmds).

  Definition update_cmd_invariants (f:list Invariant.t -> list Invariant.t) (blockinv: stmts): stmts :=
    mk_stmts
      blockinv.(phinodes)
      blockinv.(invariant_after_phinodes)
      (combine (List.map fst blockinv.(cmds)) (f (List.map snd blockinv.(cmds)))).
  
End ValidationHint.
