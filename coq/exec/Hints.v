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

Module Invariant.
  Structure unary := mk_unary {
    lessdef: ExprPairSet.t;
    noalias: ExprPairSet.t;
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

  Definition update_noalias (f:ExprPairSet.t -> ExprPairSet.t) (invariant:unary): unary :=
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
    ExprPairSet.subset (inv.(noalias)) (inv0.(noalias)) &&
    IdTSet.subset (inv.(private)) (inv0.(private)).

  Definition implies (inv0 inv:t): bool :=
    implies_unary (inv0.(src)) (inv.(src)) &&
    implies_unary (inv0.(tgt)) (inv.(tgt)) &&
    IdTSet.subset (inv0.(maydiff)) (inv.(maydiff)).

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

  (* TODO *)

  Definition physical_to_previous_idt (idt:IdT.t): IdT.t :=
    match idt with
      | (Tag.physical, id) => (Tag.previous, id)
      | _ => idt
    end.

  Definition physical_to_previous_value (v:ValueT.t): ValueT.t :=
    match v with
      | ValueT.id i => ValueT.id (physical_to_previous_idt i)
      | ValueT.const c => v
    end.

  Definition physical_to_previous_expr (e:Expr.t): Expr.t :=
    match e with
      | Expr.bop op s v1 v2 =>
        Expr.bop op s (physical_to_previous_value v1) (physical_to_previous_value v2)
      | Expr.fbop op fp v1 v2 =>
        Expr.fbop op fp (physical_to_previous_value v1) (physical_to_previous_value v2)
      | Expr.extractvalue ty1 v lc ty2 =>
        Expr.extractvalue ty1 (physical_to_previous_value v) lc ty2
      | Expr.insertvalue ty1 v1 ty2 v2 lc =>
        Expr.insertvalue ty1 (physical_to_previous_value v1) ty2 (physical_to_previous_value v2) lc
      | Expr.gep ib ty1 v1 lsv ty2 =>
        let lsv' := List.map (fun sv => match sv with
                              | (sz, v) => (sz, physical_to_previous_value v)
                            end) lsv in
        Expr.gep ib ty1 (physical_to_previous_value v1) lsv' ty2
      | Expr.trunc top ty1 v ty2 =>
        Expr.trunc top ty1 (physical_to_previous_value v) ty2
      | Expr.ext eop ty1 v ty2 =>
        Expr.ext eop ty1 (physical_to_previous_value v) ty2
      | Expr.cast cop ty1 v ty2 =>
        Expr.cast cop ty1 (physical_to_previous_value v) ty2
      | Expr.icmp c ty v1 v2 =>
        Expr.icmp c ty (physical_to_previous_value v1) (physical_to_previous_value v2)
      | Expr.fcmp fc fp v1 v2 =>
        Expr.fcmp fc fp (physical_to_previous_value v1) (physical_to_previous_value v2)
      | Expr.select v1 ty v2 v3 =>
        Expr.select (physical_to_previous_value v1) ty (physical_to_previous_value v2) (physical_to_previous_value v3)
      | Expr.value v =>
        Expr.value (physical_to_previous_value v)
      | Expr.load v ty al =>
        Expr.load (physical_to_previous_value v) ty al
      | Expr.global i => Expr.global i
    end.

  Definition physical_to_previous_exprpair (ep:ExprPair.t): ExprPair.t :=
    match ep with
      | (e1, e2) => (physical_to_previous_expr e1, physical_to_previous_expr e2)
    end.

  Definition no_previous_idt (idt:IdT.t): bool :=
    match idt with
      | (Tag.previous, i) => false
      | _ => true
    end.

  Definition has_no_previous_in_value (v:ValueT.t): bool :=
    match v with
      | ValueT.id idt => no_previous_idt idt
      | ValueT.const _ => true
    end.

  Definition has_no_previous_in_expr (e:Expr.t): bool :=
    match e with
      | Expr.bop op s v1 v2 =>
        has_no_previous_in_value v1 && has_no_previous_in_value v2
      | Expr.fbop op fp v1 v2 =>
        has_no_previous_in_value v1 && has_no_previous_in_value v2
      | Expr.extractvalue ty1 v lc ty2 =>
        has_no_previous_in_value v
      | Expr.insertvalue ty1 v1 ty2 v2 lc =>
        has_no_previous_in_value v1 && has_no_previous_in_value v2
      | Expr.gep ib ty1 v1 lsv ty2 =>
        has_no_previous_in_value v1 &&
        List.forallb (fun sv => match sv with
                                  | (sz, v) => has_no_previous_in_value v
                                end) lsv
      | Expr.trunc top ty1 v ty2 =>
        has_no_previous_in_value v
      | Expr.ext eop ty1 v ty2 =>
        has_no_previous_in_value v
      | Expr.cast cop ty1 v ty2 =>
        has_no_previous_in_value v
      | Expr.icmp c ty v1 v2 =>
        has_no_previous_in_value v1 && has_no_previous_in_value v2
      | Expr.fcmp fc fp v1 v2 =>
        has_no_previous_in_value v1 && has_no_previous_in_value v2
      | Expr.select v1 ty v2 v3 =>
        has_no_previous_in_value v1 && has_no_previous_in_value v2
      | Expr.value v =>
        has_no_previous_in_value v
      | Expr.load v ty al =>
        has_no_previous_in_value v
      | Expr.global i => true (* global?? *)
    end.

  Definition has_no_previous_in_exprpair (ep:ExprPair.t): bool :=
    match ep with
      | (e1, e2) => has_no_previous_in_expr e1 && has_no_previous_in_expr e2
    end.

  Definition snapshot_exprpairset (eps0:ExprPairSet.t): ExprPairSet.t :=
    let eps1 := ExprPairSet.filter has_no_previous_in_exprpair eps0 in
    let eps2 := ExprPairSet.fold
                  (fun ep eps =>
                     ExprPairSet.add (physical_to_previous_exprpair ep) eps)
                  eps1 eps1 in
    eps2.

  Definition snapshot_idtset (is0:IdTSet.t): IdTSet.t :=
    let is1 := IdTSet.filter no_previous_idt is0 in
    let is2 := IdTSet.fold
                 (fun idt is =>
                    IdTSet.add (physical_to_previous_idt idt) is)
                 is1 is1 in
    is2.

  Definition snapshot_unary (inv0:unary): unary :=
    let inv1 := update_lessdef snapshot_exprpairset inv0 in
    let inv2 := update_noalias snapshot_exprpairset inv1 in
    let inv3 := update_allocas snapshot_idtset inv2 in
    let inv4 := update_private snapshot_idtset inv3 in
    inv4.
  
  Definition snapshot_maydiff (inv0:IdTSet.t): IdTSet.t :=
    let inv1 := IdTSet.filter no_previous_idt inv0 in
    let inv2 := IdTSet.fold
                  (fun idt s =>
                     IdTSet.add (physical_to_previous_idt idt) s) inv1 inv1 in
    inv2.

  Definition snapshot (inv0:t): t :=
    let inv1 := update_src snapshot_unary inv0 in
    let inv2 := update_tgt snapshot_unary inv1 in
    let inv3 := update_maydiff snapshot_maydiff inv2 in
    inv3.

  (* TODO *)

  Definition ids_not_in_id (ids:IdTSet.t) (i:IdT.t): bool :=
    IdTSet.mem i ids.

  Definition ids_not_in_value (ids:IdTSet.t) (v:ValueT.t): bool :=
    match v with
      | ValueT.id idt => ids_not_in_id ids idt
      | ValueT.const _ => true
    end.
    
  Definition ids_not_in_expr (ids:IdTSet.t) (e:Expr.t): bool :=
    match e with
      | Expr.bop op s v1 v2 =>
        ids_not_in_value ids v1 && ids_not_in_value ids v2
      | Expr.fbop op fp v1 v2 =>
        ids_not_in_value ids v1 && ids_not_in_value ids v2
      | Expr.extractvalue ty1 v lc ty2 =>
        ids_not_in_value ids v
      | Expr.insertvalue ty1 v1 ty2 v2 lc =>
        ids_not_in_value ids v1 && ids_not_in_value ids v2
      | Expr.gep ib ty1 v1 lsv ty2 =>
        ids_not_in_value ids v1 &&
        List.forallb (fun sv => match sv with
                                  | (sz, v) => ids_not_in_value ids v
                                end) lsv
      | Expr.trunc top ty1 v ty2 =>
        ids_not_in_value ids v
      | Expr.ext eop ty1 v ty2 =>
        ids_not_in_value ids v
      | Expr.cast cop ty1 v ty2 =>
        ids_not_in_value ids v
      | Expr.icmp c ty v1 v2 =>
        ids_not_in_value ids v1 && ids_not_in_value ids v2
      | Expr.fcmp fc fp v1 v2 =>
        ids_not_in_value ids v1 && ids_not_in_value ids v2
      | Expr.select v1 ty v2 v3 =>
        ids_not_in_value ids v1 && ids_not_in_value ids v2
      | Expr.value v =>
        ids_not_in_value ids v
      | Expr.load v ty al =>
        ids_not_in_value ids v
      | Expr.global i => true
    end.

  Definition ids_not_in_exprpair (ids:IdTSet.t) (ep:ExprPair.t): bool :=
    match ep with
      | (e1, e2) => ids_not_in_expr ids e1 && ids_not_in_expr ids e2
    end.
  
  Definition forget_unary (ids:IdTSet.t) (inv0:unary): unary :=
    let inv1 := update_lessdef
                  (ExprPairSet.filter (ids_not_in_exprpair ids)) inv0 in
    let inv2 := update_noalias
                  (ExprPairSet.filter
                     (ids_not_in_exprpair ids)) inv1 in
    let inv3 := update_allocas
                  (IdTSet.filter (ids_not_in_id ids)) inv2 in
    let inv4 := update_private
                  (IdTSet.filter (ids_not_in_id ids)) inv3 in
    inv4.
    
  Definition forget
             (s_src s_tgt:IdTSet.t)
             (inv0:t): t :=
    let inv1 := update_src (forget_unary s_src) inv0 in
    let inv2 := update_tgt (forget_unary s_tgt) inv1 in
    let inv3 := update_maydiff (IdTSet.union (IdTSet.union s_src s_tgt)) inv2 in
    inv3.
 
  (* TODO *)

  Definition ptr_ids_not_in_expr (ids:IdTSet.t) (e:Expr.t): bool :=
    match e with
      | Expr.load v ty al =>
        ids_not_in_value ids v
      | _ => true
    end.

  Definition ptr_ids_not_in_exprpair (ids:IdTSet.t) (ep:ExprPair.t): bool :=
    match ep with
      | (e1, e2) => ptr_ids_not_in_expr ids e1 && ptr_ids_not_in_expr ids e2
    end.

  Definition noalias_id_id (na:ExprPairSet.t) (idt1:IdT.t) (idt2:IdT.t) :=
    let e1 := (Expr.value (ValueT.id idt1), Expr.value (ValueT.id idt2)) in
    let e2 := (Expr.value (ValueT.id idt2), Expr.value (ValueT.id idt1)) in
    ExprPairSet.mem e1 na || ExprPairSet.mem e2 na.
    

  Definition noalias_id (na:ExprPairSet.t) (ids:IdTSet.t) (idt:IdT.t): bool :=
    IdTSet.for_all (noalias_id_id na idt) ids.
  
  Definition noalias_value (na:ExprPairSet.t) (ids:IdTSet.t) (v:ValueT.t): bool :=
    match v with
      | ValueT.id idt => noalias_id na ids idt
      | ValueT.const _ => true
    end.

  Definition noalias_expr (na:ExprPairSet.t) (ids:IdTSet.t) (e:Expr.t): bool :=
    match e with
      | Expr.bop op s v1 v2 =>
        noalias_value na ids v1 && noalias_value na ids v2
      | Expr.fbop op fp v1 v2 =>
        noalias_value na ids v1 && noalias_value na ids v2
      | Expr.extractvalue ty1 v lc ty2 =>
        noalias_value na ids v
      | Expr.insertvalue ty1 v1 ty2 v2 lc =>
        noalias_value na ids v1 && noalias_value na ids v2
      | Expr.gep ib ty1 v1 lsv ty2 =>
        noalias_value na ids v1 &&
        List.forallb (fun sv => match sv with
                                  | (sz, v) => noalias_value na ids v
                                end) lsv
      | Expr.trunc top ty1 v ty2 =>
        noalias_value na ids v
      | Expr.ext eop ty1 v ty2 =>
        noalias_value na ids v
      | Expr.cast cop ty1 v ty2 =>
        noalias_value na ids v
      | Expr.icmp c ty v1 v2 =>
        noalias_value na ids v1 && noalias_value na ids v2
      | Expr.fcmp fc fp v1 v2 =>
        noalias_value na ids v1 && noalias_value na ids v2
      | Expr.select v1 ty v2 v3 =>
        noalias_value na ids v1 && noalias_value na ids v2
      | Expr.value v =>
        noalias_value na ids v
      | Expr.load v ty al =>
        noalias_value na ids v
      | Expr.global i => true
    end.
    
  
  Definition noalias_exprpair (na:ExprPairSet.t) (ids:IdTSet.t) (ep:ExprPair.t): bool :=
    match ep with
      | (e1, e2) => noalias_expr na ids e1 && noalias_expr na ids e2
    end.
  
  Definition forget_memory_unary (ids:IdTSet.t) (inv0:unary): unary :=
    let inv1 := update_lessdef
                  (ExprPairSet.filter (noalias_exprpair (noalias inv0) ids)) inv0 in
    let inv2 := update_noalias
                  (ExprPairSet.filter (noalias_exprpair (noalias inv0) ids)) inv1 in
    inv2.
  
  Definition forget_memory
             (s_src s_tgt:IdTSet.t)
             (inv0:t): t :=
    let inv1 := update_src (forget_memory_unary s_src) inv0 in
    let inv2 := update_tgt (forget_memory_unary s_tgt) inv1 in
    inv2.

  (* TODO *)

  Definition reducible_maydiff (s_ld t_ld:ExprPairSet.t) (md:IdTSet.t) (v:IdT.t): bool :=
    let s_ld_vre := ExprPairSet.filter
                    (fun ld => match ld with
                                 | (Expr.value (ValueT.id v), _) => true
                                 | _ => false
                               end) s_ld in
    let t_ld_vle := ExprPairSet.filter
                    (fun ld => match ld with
                                 | (_, Expr.value (ValueT.id v)) => true
                                 | _ => false
                               end) s_ld in
    ExprPairSet.exists_ (fun ld =>
                           match ld with
                             | (e1, e2) =>
                               ids_not_in_expr md e2 &&
                               ExprPairSet.mem (e2, e1) t_ld_vle
                           end) s_ld_vre.
  
  Definition reduce_maydiff
             (inv0:t): t :=
    update_maydiff
      (fun md => 
         let to_remove := IdTSet.filter (reducible_maydiff (lessdef (src inv0))
                                                        (lessdef (tgt inv0))
                                                        md)
                                     md in
         IdTSet.diff md to_remove)
      inv0.
    

  Definition is_empty_unary (inv:unary): bool :=
    ExprPairSet.is_empty inv.(lessdef) &&
    ExprPairSet.is_empty inv.(noalias) &&
    IdTSet.is_empty inv.(allocas) &&
    IdTSet.is_empty inv.(private).

  Definition is_empty (inv:t): bool :=
    is_empty_unary inv.(src) &&
    is_empty_unary inv.(tgt) &&
    IdTSet.is_empty inv.(maydiff).
End Invariant.

Module Infrule.
  Inductive t :=
  | add_associative (z:IdT.t) (y:IdT.t) (x:ValueT.t) (s:sz) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t)
  | replace_rhs (z:IdT.t) (x:IdT.t) (y:ValueT.t) (e:Expr.t) (e':Expr.t)
  | replace_rhs_opt (z:IdT.t) (x:IdT.t) (y:ValueT.t) (e:Expr.t) (e':Expr.t)
  | replace_lhs (x:IdT.t) (y:IdT.t) (e:Expr.t)
  | remove_maydiff (v:IdT.t) (e:Expr.t)
  | remove_maydiff_rhs (v:IdT.t) (e:IdT.t)
  | eq_generate_same (x:IdT.t) (y:IdT.t) (e:Expr.t)
  | eq_generate_same_heap (x:IdT.t) (y:IdT.t) (p:ValueT.t) (ty:typ) (a:align)
  | eq_generate_same_heap_value (x:IdT.t) (p:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | add_signbit (x:IdT.t) (sz:sz) (e:ValueT.t) (s:ValueT.t)
  | add_zext_bool (x:IdT.t) (y:IdT.t) (b:ValueT.t) (sz:sz) (c:INTEGER.t) (c':INTEGER.t)
  | ptr_trans (p:IdT.t) (q:ValueT.t) (v:ValueT.t) (ty:typ) (a:align)
  | add_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | stash_variable (z:IdT.t) (v:id)
  | add_shift (y:IdT.t) (s:sz) (v:ValueT.t)
  | add_sub (z:IdT.t) (minusy:IdT.t) (s:sz) (x:ValueT.t) (y:ValueT.t)
  | add_commutative (z:IdT.t) (s:sz) (x:ValueT.t) (y:ValueT.t)
  | sub_add (z:IdT.t) (minusy:IdT.t) (s:sz) (x:ValueT.t) (y:ValueT.t)
  | sub_onebit (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
  | sub_mone (z:IdT.t) (s:sz) (x:ValueT.t)
  | sub_const_not (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | add_mul_fold (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | add_const_not (z:IdT.t) (y:IdT.t) (s:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | add_select_zero (z:IdT.t) (x:IdT.t) (y:IdT.t) (c:ValueT.t) (s:sz) (n:ValueT.t) (a:ValueT.t)
  | add_select_zero2 (z:IdT.t) (x:IdT.t) (y:IdT.t) (c:ValueT.t) (s:sz) (n:ValueT.t) (a:ValueT.t)
  | add_dist_sub (z:IdT.t) (minusx:IdT.t) (minusy:IdT.t) (w:IdT.t) (s:sz) (x:ValueT.t) (y:ValueT.t)
  | add_distributive (z:IdT.t) (x:IdT.t) (y:IdT.t) (w:IdT.t) (s:sz) (a:ValueT.t) (b:ValueT.t) (c:ValueT.t)
  | sub_zext_bool (x:IdT.t) (y:IdT.t) (b:ValueT.t) (sz:sz) (c:INTEGER.t) (c':INTEGER.t)
  | sub_const_add (z:IdT.t) (y:IdT.t) (sz:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t) (c3:INTEGER.t)
  | sub_remove (z:IdT.t) (y:IdT.t) (sz:sz) (a:ValueT.t) (b:ValueT.t)
  | sub_remove2 (z:IdT.t) (y:IdT.t) (sz:sz) (a:ValueT.t) (b:ValueT.t)
  | sub_sdiv (z:IdT.t) (y:IdT.t) (sz:sz) (x:ValueT.t) (c:INTEGER.t) (c':INTEGER.t)
  | sub_shl (z:IdT.t) (x:IdT.t) (y:IdT.t) (sz:sz) (mx:ValueT.t) (a:ValueT.t)
  | sub_mul (z:IdT.t) (y:IdT.t) (sz:sz) (x:ValueT.t) (c:INTEGER.t) (c':INTEGER.t)
  | sub_mul2 (z:IdT.t) (y:IdT.t) (sz:sz) (x:ValueT.t) (c:INTEGER.t) (c':INTEGER.t)
  | mul_mone (z:IdT.t) (sz:sz) (x:ValueT.t)
  | mul_neg (z:IdT.t) (mx:IdT.t) (my:IdT.t) (sz:sz) (x:ValueT.t) (y:ValueT.t)
  | mul_bool (z:IdT.t) (x:ValueT.t) (y:ValueT.t)
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
  | add_mask (z:IdT.t) (y:IdT.t) (y':IdT.t) (s:sz) (x:ValueT.t) (c1:INTEGER.t) (c2:INTEGER.t)
  | neq_generate_gm (x:id) (y:IdT.t)
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

Module Hints.
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
End Hints.
