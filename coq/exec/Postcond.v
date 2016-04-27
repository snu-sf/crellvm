Require Import List.
Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import Coqlib.
Require Import infrastructure.
Require Import Metatheory.
Import LLVMsyntax.
Import LLVMinfra.

Require Import Exprs.
Require Import Hints.
Require Import Decs.
Require Import TODO.
Require Import Debug.

Import ListNotations.
Set Implicit Arguments.

Module LiftPred.
  Section LiftPred.
    Variable IdT: IdT.t -> bool.

    Definition ValueT (v:ValueT.t): bool :=
      match v with
      | ValueT.id i => IdT i
      | _ => false
      end.

    Definition ValueTPair (ep:ValueTPair.t): bool := ValueT (fst ep) || ValueT (snd ep).

    Definition Expr (e:Expr.t): bool :=
      match e with
      | Expr.bop op s v1 v2 => ValueT v1 || ValueT v2
      | Expr.fbop op fp v1 v2 => ValueT v1 || ValueT v2
      | Expr.extractvalue ty1 v lc ty2 => ValueT v
      | Expr.insertvalue ty1 v1 ty2 v2 lc => ValueT v1 || ValueT v2
      | Expr.gep ib ty1 v1 lsv ty2 => ValueT v1 || List.existsb (compose ValueT snd) lsv
      | Expr.trunc top ty1 v ty2 => ValueT v
      | Expr.ext eop ty1 v ty2 => ValueT v
      | Expr.cast cop ty1 v ty2 => ValueT v
      | Expr.icmp c ty v1 v2 => ValueT v1 || ValueT v2
      | Expr.fcmp fc fp v1 v2 => ValueT v1 || ValueT v2
      | Expr.select v1 ty v2 v3 => ValueT v1 || ValueT v2 || ValueT v3
      | Expr.value v => ValueT v
      | Expr.load v ty al => ValueT v
      end.

    Definition ExprPair (ep:ExprPair.t): bool := Expr (fst ep) || Expr (snd ep).

    Definition Ptr (p: Ptr.t): bool := ValueT (fst p).

    Definition PtrPair (pp: PtrPair.t): bool := Ptr (fst pp) || Ptr (snd pp).
  End LiftPred.
End LiftPred.

Module Previousify.
  Definition Tag (t:Tag.t): Tag.t :=
    match t with
    | Tag.physical => Tag.previous
    | _ => t
    end.

  Definition IdT (i:IdT.t): IdT.t := (Tag (fst i), snd i).

  Definition ValueT (v:ValueT.t): ValueT.t :=
    match v with
    | ValueT.id i => ValueT.id (IdT i)
    | ValueT.const c => v
    end.

  Definition ValueTPair (ep:ValueTPair.t): ValueTPair.t := (ValueT (fst ep), ValueT (snd ep)).

  Definition Expr (e:Expr.t): Expr.t :=
    match e with
    | Expr.bop op s v1 v2 => Expr.bop op s (ValueT v1) (ValueT v2)
    | Expr.fbop op fp v1 v2 => Expr.fbop op fp (ValueT v1) (ValueT v2)
    | Expr.extractvalue ty1 v lc ty2 => Expr.extractvalue ty1 (ValueT v) lc ty2
    | Expr.insertvalue ty1 v1 ty2 v2 lc => Expr.insertvalue ty1 (ValueT v1) ty2 (ValueT v2) lc
    | Expr.gep ib ty1 v1 lsv ty2 =>
      let lsvT := List.map (fun elt => (fst elt, ValueT (snd elt))) lsv in
      Expr.gep ib ty1 (ValueT v1) lsvT ty2
    | Expr.trunc top ty1 v ty2 => Expr.trunc top ty1 (ValueT v) ty2
    | Expr.ext eop ty1 v ty2 => Expr.ext eop ty1 (ValueT v) ty2
    | Expr.cast cop ty1 v ty2 => Expr.cast cop ty1 (ValueT v) ty2
    | Expr.icmp c ty v1 v2 => Expr.icmp c ty (ValueT v1) (ValueT v2)
    | Expr.fcmp fc fp v1 v2 => Expr.fcmp fc fp (ValueT v1) (ValueT v2)
    | Expr.select v1 ty v2 v3 => Expr.select (ValueT v1) ty (ValueT v2) (ValueT v3)
    | Expr.value v => Expr.value (ValueT v)
    | Expr.load v ty al => Expr.load (ValueT v) ty al
    end.

  Definition ExprPair (ep:ExprPair.t): ExprPair.t := (Expr (fst ep), Expr (snd ep)).

  Definition Ptr (p:Ptr.t): Ptr.t := (ValueT (fst p), snd p).

  Definition PtrPair (pp:PtrPair.t): PtrPair.t := (Ptr (fst pp), Ptr (snd pp)).
End Previousify.

(* TODO: move *)
Definition ValueTPairSet_map f s :=
  ValueTPairSet.fold
    (compose ValueTPairSet.add f)
    s
    ValueTPairSet.empty.

(* TODO: move *)
Definition ExprPairSet_map f s :=
  ExprPairSet.fold
    (compose ExprPairSet.add f)
    s
    ExprPairSet.empty.

(* TODO: move *)
Definition IdTSet_map f s :=
  IdTSet.fold
    (compose IdTSet.add f)
    s
    IdTSet.empty.

(* TODO: move *)
Definition PtrPairSet_map f s :=
  PtrPairSet.fold
    (compose PtrPairSet.add f)
    s
    PtrPairSet.empty.

(* TODO: move *)
Definition PtrSet_map f s :=
  PtrSet.fold
    (compose PtrSet.add f)
    s
    PtrSet.empty.

Module Snapshot.
  Definition IdT (i:IdT.t): bool :=
    if Tag.eq_dec (fst i) Tag.previous
    then true
    else false.

  Definition Ptr (p:Ptr.t): bool :=
    match fst p with
    | ValueT.id i => IdT i
    | ValueT.const _ => false
    end.

  Definition ValueTPairSet (inv0:ValueTPairSet.t): ValueTPairSet.t :=
    let inv1 := ValueTPairSet.filter (compose negb (LiftPred.ValueTPair IdT)) inv0 in
    let inv2 := ValueTPairSet.union inv1 (ValueTPairSet_map Previousify.ValueTPair inv1) in
    inv2.

  Definition ExprPairSet (inv0:ExprPairSet.t): ExprPairSet.t :=
    let inv1 := ExprPairSet.filter (compose negb (LiftPred.ExprPair IdT)) inv0 in
    let inv2 := ExprPairSet.union inv1 (ExprPairSet_map Previousify.ExprPair inv1) in
    inv2.

  Definition IdTSet (inv0:IdTSet.t): IdTSet.t :=
    let inv1 := IdTSet.filter (compose negb IdT) inv0 in
    let inv2 := IdTSet.union inv1 (IdTSet_map Previousify.IdT inv1) in
    inv2.

  Definition PtrSet (inv0:PtrSet.t): PtrSet.t :=
    let inv1 := PtrSet.filter (compose negb Ptr) inv0 in
    let inv2 := PtrSet.union inv0 (PtrSet_map Previousify.Ptr inv1) in
    inv2.

  Definition noalias (inv0:PtrPairSet.t): PtrPairSet.t :=
    let inv1 := PtrPairSet.filter (compose negb (LiftPred.PtrPair IdT)) inv0 in
    let inv2 := PtrPairSet.union inv1 (PtrPairSet_map Previousify.PtrPair inv1) in
    inv2.

  Definition diffblock (inv0:ValueTPairSet.t): ValueTPairSet.t :=
    let inv1 := ValueTPairSet.filter (compose negb (LiftPred.ValueTPair IdT)) inv0 in
    let inv2 := ValueTPairSet.union inv1 (ValueTPairSet_map Previousify.ValueTPair inv1) in
    inv2.

  Definition alias (inv0: Invariant.aliasrel): Invariant.aliasrel :=
    let inv1 := Invariant.update_noalias_rel noalias inv0 in
    let inv2 := Invariant.update_diffblock_rel diffblock inv0 in
    inv1.

  Definition physical_previous_lessdef (inv:Invariant.unary): ExprPairSet.t :=
    let idt_set := IdTSet_from_list (Invariant.get_idTs_unary inv) in
    let prev_idt_set := IdTSet.filter IdT idt_set in
    IdTSet.fold
      (fun idt eps =>
         let id_expr_prev := Expr.value (ValueT.id idt) in
         let id_expr_phys := Expr.value (ValueT.id (IdT.lift Tag.physical (snd idt))) in
         (ExprPairSet.add (id_expr_phys, id_expr_prev)
                          (ExprPairSet.add (id_expr_prev, id_expr_phys) eps)))
      prev_idt_set ExprPairSet.empty.

  Definition unary (inv0:Invariant.unary): Invariant.unary :=
    let inv1 := Invariant.update_lessdef ExprPairSet inv0 in
    let inv2 := Invariant.update_alias alias inv1 in
    let inv3 := Invariant.update_allocas IdTSet inv2 in
    let inv4 := Invariant.update_private IdTSet inv3 in
    let inv5 := Invariant.update_lessdef
                  (ExprPairSet.union
                     (physical_previous_lessdef inv4)) inv4 in
    inv5.

  Definition t (inv0:Invariant.t): Invariant.t :=
    let inv1 := Invariant.update_src unary inv0 in
    let inv2 := Invariant.update_tgt unary inv1 in
    let inv3 := Invariant.update_maydiff IdTSet inv2 in
    inv3.
End Snapshot.

Module Forget.
  Definition alias (ids:IdTSet.t) (inv0:Invariant.aliasrel): Invariant.aliasrel :=
    let inv1 := Invariant.update_diffblock_rel (ValueTPairSet.filter (compose negb (LiftPred.ValueTPair (flip IdTSet.mem ids)))) inv0 in
    let inv2 := Invariant.update_noalias_rel (PtrPairSet.filter (compose negb (LiftPred.PtrPair (flip IdTSet.mem ids)))) inv1 in
    inv2.

  Definition unary (ids:IdTSet.t) (inv0:Invariant.unary): Invariant.unary :=
    let inv1 := Invariant.update_lessdef (ExprPairSet.filter (compose negb (LiftPred.ExprPair (flip IdTSet.mem ids)))) inv0 in
    let inv2 := Invariant.update_alias (alias ids) inv1 in
    let inv3 := Invariant.update_allocas (IdTSet.filter (compose negb (flip IdTSet.mem ids))) inv2 in
    let inv4 := Invariant.update_private (IdTSet.filter (compose negb (flip IdTSet.mem ids))) inv3 in
    inv4.

  Definition t (s_src s_tgt:IdTSet.t) (inv0:Invariant.t): Invariant.t :=
    let inv1 := Invariant.update_src (unary s_src) inv0 in
    let inv2 := Invariant.update_tgt (unary s_tgt) inv1 in
    let inv3 := Invariant.update_maydiff (IdTSet.union (IdTSet.union s_src s_tgt)) inv2 in
    inv3.
End Forget.

Module ForgetMemory.
  Definition is_noalias_Ptr (inv:Invariant.unary) (ps:PtrSet.t) (p:Ptr.t): bool :=
    PtrSet.for_all (Invariant.is_noalias inv p) ps.

  Definition is_noalias_Expr (inv:Invariant.unary) (ps:PtrSet.t) (e:Expr.t): bool :=
    match e with
      | Expr.load v ty al => is_noalias_Ptr inv ps (v, ty)
      | _ => true
    end.
  
  Definition is_noalias_ExprPair (inv:Invariant.unary) (ps:PtrSet.t) (ep:ExprPair.t): bool :=
    is_noalias_Expr inv ps (fst ep) && is_noalias_Expr inv ps (snd ep).

  Definition is_noalias_PtrPair (inv: Invariant.unary) (ps:PtrSet.t) (pp:PtrPair.t): bool :=
    is_noalias_Ptr inv ps (fst pp) && is_noalias_Ptr inv ps (snd pp).

  Definition unary (ps:PtrSet.t) (inv0:Invariant.unary): Invariant.unary :=
    Invariant.update_lessdef (ExprPairSet.filter (is_noalias_ExprPair inv0 ps)) inv0.

  Definition t (s_src s_tgt:PtrSet.t) (inv0:Invariant.t): Invariant.t :=
    let inv1 := Invariant.update_src (unary s_src) inv0 in
    let inv2 := Invariant.update_tgt (unary s_tgt) inv1 in
    inv2.
End ForgetMemory.

Definition reduce_non_physical (inv0: Invariant.t): Invariant.t :=
  let (src, tgt, _) := inv0 in
  let used_ids := ((Invariant.get_idTs_unary src) ++ (Invariant.get_idTs_unary tgt)) in
  Invariant.update_maydiff
    (IdTSet.filter
       (fun idt =>
          if(Tag.eq_dec (fst idt) Tag.physical)
          then true
          else
            match List.find (IdT.eq_dec idt) used_ids with
              | (Some _) => true
              | None => false
            end
    ))
    inv0.

Definition inject_expr (inv:Invariant.t) (es et:Expr.t): bool :=
  match es, et with
  | Expr.bop b1 s1 v1 w1, Expr.bop b2 s2 v2 w2 => 
                                        (bop_dec b1 b2) &&
                                        (sz_dec s1 s2) &&
                                        (Invariant.inject_value inv v1 v2) && 
                                        (Invariant.inject_value inv w1 w2)
  | Expr.fbop fb1 fp1 v1 w1, Expr.fbop fb2 fp2 v2 w2 => 
                                        (fbop_dec fb1 fb2) &&
                                        (floating_point_dec fp1 fp2) &&
                                        (Invariant.inject_value inv v1 v2) && 
                                        (Invariant.inject_value inv w1 w2)
  | Expr.extractvalue t1 v1 lc1 u1, Expr.extractvalue t2 v2 lc2 u2 => 
                                        (typ_dec t1 t2) &&
                                        (list_eq_dec const_dec lc1 lc2) &&
                                        (typ_dec u1 u2) &&
                                        (Invariant.inject_value inv v1 v2)
  | Expr.insertvalue t1 v1 t'1 v'1 lc1, Expr.insertvalue t2 v2 t'2 v'2 lc2 =>
    (typ_dec t1 t2)
      && (Invariant.inject_value inv v1 v2)
      && (typ_dec t'1 t'2)
      && (Invariant.inject_value inv v'1 v'2)
      && (list_eq_dec const_dec lc1 lc2)
  | Expr.gep ib1 t1 v1 lsv1 u1, Expr.gep ib2 t2 v2 lsv2 u2 => 
                                        (inbounds_dec ib1 ib2) &&
                                        (typ_dec t1 t2) &&
                                        (list_eq_dec sz_dec (List.map fst lsv1) 
                                                            (List.map fst lsv2)) &&
                                        (List.existsb 
                                           (fun p => List.existsb
                                                       (fun q => Invariant.inject_value inv p q)
                                                       (List.map snd lsv2))
                                           (List.map snd lsv1)) &&
                                        (typ_dec u1 u2) &&
                                        (Invariant.inject_value inv v1 v2) 
  | Expr.trunc top1 t1 v1 u1, Expr.trunc top2 t2 v2 u2 => 
                                        (truncop_dec top1 top2) &&
                                        (typ_dec t1 t2) &&
                                        (typ_dec u1 u2) &&
                                        (Invariant.inject_value inv v1 v2)
  | Expr.ext eop1 t1 v1 u1, Expr.ext eop2 t2 v2 u2 => 
                                        (extop_dec eop1 eop2) &&
                                        (typ_dec t1 t2) &&
                                        (typ_dec u1 u2) &&
                                        (Invariant.inject_value inv v1 v2) 
  | Expr.cast cop1 t1 v1 u1, Expr.cast cop2 t2 v2 u2 => 
                                        (castop_dec cop1 cop2) &&
                                        (typ_dec t1 t2) &&
                                        (typ_dec u1 u2) &&
                                        (Invariant.inject_value inv v1 v2) 
  | Expr.icmp c1 t1 v1 w1, Expr.icmp c2 t2 v2 w2  => 
                                        (cond_dec c1 c2) &&
                                        (typ_dec t1 t2) &&
                                        (Invariant.inject_value inv v1 v2) &&
                                        (Invariant.inject_value inv w1 w2)
  | Expr.fcmp fc1 fp1 v1 w1, Expr.fcmp fc2 fp2 v2 w2  => 
                                        (fcond_dec fc1 fc2) &&
                                        (floating_point_dec fp1 fp2) &&
                                        (Invariant.inject_value inv v1 v2) &&
                                        (Invariant.inject_value inv w1 w2)
  | Expr.select v1 t1 w1 z1, Expr.select v2 t2 w2 z2 => 
                                        (typ_dec t1 t2) &&
                                        (Invariant.inject_value inv v1 v2) &&
                                        (Invariant.inject_value inv w1 w2) &&
                                        (Invariant.inject_value inv z1 z2)
  | Expr.value v1, Expr.value v2 => (Invariant.inject_value inv v1 v2)
  | Expr.load v1 t1 a1, Expr.load v2 t2 a2 => 
                                        (typ_dec t1 t2) &&
                                        (Decs.align_dec a1 a2) &&
                                        (Invariant.inject_value inv v1 v2)
  | _, _ => false
  end.

Definition reduce_maydiff (inv0:Invariant.t): Invariant.t :=
  let lessdef_src := inv0.(Invariant.src).(Invariant.lessdef) in
  let lessdef_tgt := inv0.(Invariant.tgt).(Invariant.lessdef) in
  let inv1 := Invariant.update_maydiff
                (IdTSet.filter
                   (fun id => negb (ExprPairSet.exists_
                                      (fun p => ExprPairSet.exists_
                                                  (fun q => inject_expr inv0 (snd p) (fst q))
                                                  (Invariant.get_lhs lessdef_tgt (fst p)))
                                   (Invariant.get_rhs lessdef_src (Expr.value (ValueT.id id)))))) inv0 in
  let inv2 := reduce_non_physical inv1 in
  inv2.

Definition reduce_maydiff_default (inv0:Invariant.t): Invariant.t :=
  let lessdef_src := inv0.(Invariant.src).(Invariant.lessdef) in
  let lessdef_tgt := inv0.(Invariant.tgt).(Invariant.lessdef) in
  let equations := ExprPairSet.filter
                     (fun elt => ExprPairSet.mem (snd elt, fst elt) lessdef_tgt)
                     lessdef_src in
  let inv1 := Invariant.update_maydiff
                (IdTSet.filter
                   (fun id => negb (ExprPairSet.exists_
                                      (fun ep => ((Expr.eq_dec (fst ep)
                                                               (Expr.value (ValueT.id id)))
                                                    && Invariant.not_in_maydiff_expr inv0 (snd ep)))
                                      equations)))
                inv0 in
  let inv2 := reduce_non_physical inv1 in
  inv2.

Module Cmd.
  Definition t := cmd.

  Definition get_def (c:t): option id := getCmdID c.

  Definition get_def_memory (c:t): option Ptr.t :=
    match c with
    | insn_malloc x ty v a => Some (ValueT.id (IdT.lift Tag.physical x), ty)
    | insn_free x ty v =>
      TODO.lift_option
        (fun id => (ValueT.id (IdT.lift Tag.physical id), ty))
        (getValueID v)
    | insn_alloca x ty v a => Some (ValueT.id (IdT.lift Tag.physical x), ty)
    | insn_store x ty v p a =>
      TODO.lift_option
        (fun id => (ValueT.id (IdT.lift Tag.physical id), typ_pointer ty))
        (getValueID p)
    | _ => None
    end.

  Definition get_rhs (c:t): option Expr.t :=
    match c with
    | insn_nop _ => None
    | insn_bop x b s v1 v2 => Some (Expr.bop b s (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))
    | insn_fbop x fb fp v1 v2 => Some (Expr.fbop fb fp (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))
    | insn_extractvalue x ty1 v lc ty2 => Some (Expr.extractvalue ty1 (ValueT.lift Tag.physical v) lc ty2)
    | insn_insertvalue x ty1 v1 ty2 v2 lc => Some (Expr.insertvalue ty1 (ValueT.lift Tag.physical v1) ty2 (ValueT.lift Tag.physical v2) lc)
    | insn_malloc x ty v a => None
    | insn_free x ty v => None
    | insn_alloca x ty v a => None
    | insn_load x ty p a => Some (Expr.load (ValueT.lift Tag.physical p) ty a)
    | insn_store x ty v p a => None
    | insn_gep x ib ty1 v lsv ty2 =>
      let lsvT := List.map (fun elt => (fst elt, ValueT.lift Tag.physical (snd elt))) lsv in
      Some (Expr.gep ib ty1 (ValueT.lift Tag.physical v) lsvT ty2)
    | insn_trunc x trop ty1 v ty2 => Some (Expr.trunc trop ty1 (ValueT.lift Tag.physical v) ty2)
    | insn_ext x eop ty1 v ty2 => Some (Expr.ext eop ty1 (ValueT.lift Tag.physical v) ty2)
    | insn_cast x cop ty1 v ty2 => Some (Expr.cast cop ty1 (ValueT.lift Tag.physical v) ty2)
    | insn_icmp x con ty v1 v2 => Some (Expr.icmp con ty (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))
    | insn_fcmp x fcon fp v1 v2 => Some (Expr.fcmp fcon fp (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))
    | insn_select x v1 ty v2 v3 => Some (Expr.select (ValueT.lift Tag.physical v1) ty (ValueT.lift Tag.physical v2) (ValueT.lift Tag.physical v3))
    | insn_call x _ _ typ _ f params => None
    end.

  Definition get_values (c: t): list value :=
    match c with
      | insn_nop _ => []
      | insn_bop x b s v1 v2 => [v1 ; v2]
      | insn_fbop x fb fp v1 v2 => [v1 ; v2]
      | insn_extractvalue x ty1 v lc ty2 => [v]
      | insn_insertvalue x ty1 v1 ty2 v2 lc => [v1 ; v2]
      | insn_malloc x ty v a => [v]
      | insn_free x ty v => [v]
      | insn_alloca x ty v a => [v]
      | insn_load x ty p a => [p]
      | insn_store x ty v p a => [v ; p]
      | insn_gep x ib ty1 v lsv ty2 => v :: (List.map snd lsv)
      | insn_trunc x trop ty1 v ty2 => [v]
      | insn_ext x eop ty1 v ty2 => [v]
      | insn_cast x cop ty1 v ty2 => [v]
      | insn_icmp x con ty v1 v2 => [v1 ; v2]
      | insn_fcmp x fcon fp v1 v2 => [v1 ; v2]
      | insn_select x v1 ty v2 v3 => [v1 ; v2 ; v3]
      | insn_call x nr attr ty va f ps => f :: (List.map snd ps)
    end.

  Definition get_ids (c: t): list id :=
    TODO.filter_map Value.get_ids (get_values c).
End Cmd.

Module Phinode.
  Definition t := phinode.
  Inductive assign :=
  | assign_intro (lhs:id) (ty:typ) (rhs:value)
  .

  Definition resolve (l_from:l) (phinode:t): option assign :=
    let '(insn_phi lhs ty values) := phinode in
    let values := List.map (fun elt => (snd elt, fst elt)) values in
    match lookupAL _ values l_from with
    | Some rhs => Some (assign_intro lhs ty rhs)
    | None => None
    end.

  Definition get_def (a:assign): id :=
    let '(assign_intro id _ _) := a in
    id.

  Definition get_rhs (a:assign): value :=
    let '(assign_intro _ _ rhs) := a in
    rhs.

  Definition get_use (a:assign): option id :=
    match get_rhs a with
    | value_id id => Some id
    | _ => None
    end.

  Definition get_equation (a:assign): Expr.t * Expr.t :=
    (Expr.value (IdT.lift Tag.physical (get_def a)),
     Expr.value (ValueT.lift Tag.previous (get_rhs a))).
End Phinode.

Definition get_br_cond
           (term:terminator)
           (l_to:l): ExprPairSet.t :=
  let sz := Size.One in
  match term with
    | insn_br _ v l1 l2 =>
      let cond_val := if (l_dec l_to l1) then 1%Z else 0%Z in
      ExprPairSet.singleton
        (Expr.value (ValueT.lift Tag.physical v),
         Expr.value (ValueT.const (const_int sz (INTEGER.of_Z (Size.to_Z sz) cond_val true))))
    | _ => ExprPairSet.empty
  end.

Definition postcond_branch
           (blocks_src blocks_tgt:blocks)
           (l_from l_to:l)
           (inv:Invariant.t): Invariant.t :=
  match lookupAL _ blocks_src l_from, lookupAL _ blocks_tgt l_from with
    | Some (stmts_intro _ _ term_src), Some (stmts_intro _ _ term_tgt) =>
      let inv1 := Invariant.update_src (Invariant.update_lessdef (ExprPairSet.union (get_br_cond term_src l_to))) inv in
      let inv2 := Invariant.update_tgt (Invariant.update_lessdef (ExprPairSet.union (get_br_cond term_tgt l_to))) inv1 in
      inv2
    | _, _ => inv
  end.

Definition postcond_phinodes_add_lessdef
           (assigns:list Phinode.assign)
           (inv0:ExprPairSet.t): ExprPairSet.t :=
  fold_left
    (fun result a =>
       let (lhs, rhs) := Phinode.get_equation a in
       ExprPairSet.add (lhs, rhs) (ExprPairSet.add (rhs, lhs) result))
    assigns inv0.

Definition postcond_phinodes_assigns
           (assigns_src assigns_tgt:list Phinode.assign)
           (inv0:Invariant.t): option Invariant.t :=
  let defs_src' := List.map Phinode.get_def assigns_src in
  let defs_tgt' := List.map Phinode.get_def assigns_tgt in
  let uses_src' := filter_map Phinode.get_use assigns_src in
  let uses_tgt' := filter_map Phinode.get_use assigns_tgt in

  let defs_src := IdTSet_from_list (List.map (IdT.lift Tag.physical) defs_src') in
  let defs_tgt := IdTSet_from_list (List.map (IdT.lift Tag.physical) defs_tgt') in

  if negb (unique id_dec defs_src' && unique id_dec defs_tgt')
  then None
  else

  let inv1 := Snapshot.t inv0 in
  let inv2 := Forget.t defs_src defs_tgt inv1 in
  let inv3 := Invariant.update_src (Invariant.update_lessdef (postcond_phinodes_add_lessdef assigns_src)) inv2 in
  let inv4 := Invariant.update_tgt (Invariant.update_lessdef (postcond_phinodes_add_lessdef assigns_tgt)) inv3 in
  let inv5 := reduce_maydiff inv4 in
  Some inv5.

Definition postcond_phinodes
           (l_from:l)
           (phinodes_src phinodes_tgt:phinodes)
           (inv0:Invariant.t): option Invariant.t :=
  match forallb_map (Phinode.resolve l_from) phinodes_src,
        forallb_map (Phinode.resolve l_from) phinodes_tgt with
  | Some assigns_src, Some assigns_tgt =>
    postcond_phinodes_assigns assigns_src assigns_tgt inv0
  | _, _ => None
  end.

Definition postcond_cmd_inject_event
           (src tgt:cmd)
           (inv:Invariant.t): bool :=
  match src, tgt with
  | insn_call x1 nr1 cl1 t1 va1 v1 p1,
    insn_call x2 nr2 cl2 t2 va2 v2 p2 =>
    noret_dec nr1 nr2 &&
    clattrs_dec cl1 cl2 &&
    typ_dec t1 t2 &&
    varg_dec va1 va2 &&
    Invariant.inject_value inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2) &&
    list_forallb2
      (fun p1 p2 =>
         let '(ty1, attr1, v1) := p1 in
         let '(ty2, attr2, v2) := p2 in
         typ_dec t1 t2 &&
         attributes_dec attr1 attr2 &&
         Invariant.inject_value inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))
      p1 p2
  | insn_call _ _ _ _ _ _ _, _
  | _, insn_call _ _ _ _ _ _ _ => false

  | insn_store _ t1 v1 p1 a1,
    insn_store _ t2 v2 p2 a2 =>
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2)
  | insn_store _ t1 v1 p1 a1, insn_nop _ =>
    Invariant.is_private inv.(Invariant.src) (ValueT.lift Tag.physical p1)
  (* | insn_store _ _ _ _ _, _ *)
  | _, insn_store _ _ _ _ _ => false

  | insn_load x1 t1 v1 a1, insn_load x2 t2 v2 a2 =>
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2) &&
    align_dec a1 a2
  | _, insn_load _ _ _ _ => false

  | insn_free _ t1 p1, insn_free _ t2 p2 =>
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift Tag.physical p1) (ValueT.lift Tag.physical p2)
  | insn_free _ _ _, _
  | _, insn_free _ _ _ => false

  | insn_alloca x1 t1 v1 a1, insn_alloca x2 t2 v2 a2 =>
    id_dec x1 x2 &&
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2) &&
    align_dec a1 a2
  | insn_alloca _ _ _ _, insn_nop _ => true
  | insn_nop _, insn_alloca _ _ _ _ => true
  (* | insn_alloca _ _ _ _, _ => false *)
  (* | _, insn_alloca _ _ _ _ => false *)

  | insn_malloc x1 t1 v1 a1, insn_malloc x2 t2 v2 a2 =>
    id_dec x1 x2 &&
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2) &&
    align_dec a1 a2
  | insn_malloc _ _ _ _, _ => false
  | _, insn_malloc _ _ _ _ => false

  | _, _ => true
  end.

Definition postcond_cmd_add_private_allocas
           (src tgt:cmd)
           (inv0:Invariant.t): Invariant.t :=
  match src, tgt with
  | insn_alloca aid_src _ _ _, insn_alloca aid_tgt _ _ _ =>
    let inv1 := Invariant.update_src (Invariant.update_allocas (IdTSet.add (IdT.lift Tag.physical aid_src))) inv0 in
    let inv2 := Invariant.update_tgt (Invariant.update_allocas (IdTSet.add (IdT.lift Tag.physical aid_tgt))) inv1 in
    inv2
  | insn_alloca aid_src _ _ _, insn_nop _ =>
    let inv1 := Invariant.update_src (Invariant.update_allocas (IdTSet.add (IdT.lift Tag.physical aid_src))) inv0 in
    let inv2 := Invariant.update_src (Invariant.update_private (IdTSet.add (IdT.lift Tag.physical aid_src))) inv1 in
    inv2
  | insn_nop _, insn_alloca aid_tgt _ _ _ =>
    let inv1 := Invariant.update_tgt (Invariant.update_allocas (IdTSet.add (IdT.lift Tag.physical aid_tgt))) inv0 in
    let inv2 := Invariant.update_tgt (Invariant.update_private (IdTSet.add (IdT.lift Tag.physical aid_tgt))) inv1 in
    inv2
  | _, _ => inv0
  end.

Definition postcond_cmd_get_lessdef
           (c:cmd): option ExprPair.t :=
  match Cmd.get_def c, Cmd.get_rhs c with
  | Some lhs, Some rhs => Some (Expr.value (IdT.lift Tag.physical lhs), rhs)
  | _, _ =>
    match c with
    | insn_store x ty v p a => Some (Expr.load (ValueT.lift Tag.physical p) ty a, Expr.value (ValueT.lift Tag.physical v))
    | _ => None
    end
  end.

Definition postcond_cmd_add_lessdef
           (c:cmd)
           (inv0:ExprPairSet.t): ExprPairSet.t :=
  match postcond_cmd_get_lessdef c with
  | None => inv0
  | Some (lhs, rhs) =>
    let inv1 := ExprPairSet.add (lhs, rhs) inv0 in
    let inv2 := ExprPairSet.add (rhs, lhs) inv1 in
    inv2
  end.

Definition postcond_cmd_add_diffblock
           (c:cmd)
           (allocas:IdTSet.t)
           (inv0:ValueTPairSet.t): ValueTPairSet.t :=
  match c with
  | insn_alloca x ty v a =>
    IdTSet.fold
      (fun alloca result0 =>
         let result1 := ValueTPairSet.add (ValueT.id alloca, ValueT.id (IdT.lift Tag.physical x)) result0 in
         let result2 := ValueTPairSet.add (ValueT.id (IdT.lift Tag.physical x), ValueT.id alloca) result1 in
         result2)
      allocas
      inv0
  | _ => inv0
  end.

 (* This removes the defined register from maydiff in 3 cases *)
 (* (alloca, malloc, call) because postcond do not *)
 (* produce any lessdef information from them *)
 (* so that reduce_maydiff doesn't remove them.   *)
Definition remove_def_from_maydiff (src tgt:cmd) (inv:Invariant.t): Invariant.t :=
  match src, tgt with
    | insn_alloca x _ _ _, insn_alloca x' _ _ _
    | insn_malloc x _ _ _, insn_malloc x' _ _ _
    | insn_call x _ _ _ _ _ _, insn_call x' _ _ _ _ _ _ =>
      if (id_dec x x')
      then Invariant.update_maydiff (IdTSet.remove (IdT.lift Tag.physical x)) inv
      else inv
    | _, _ => inv
  end.

Definition postcond_cmd
           (src tgt:cmd)
           (inv0:Invariant.t): option Invariant.t :=
  let def_src' := option_to_list (Cmd.get_def src) in
  let def_tgt' := option_to_list (Cmd.get_def tgt) in
  let def_memory_src' := option_to_list (Cmd.get_def_memory src) in
  let def_memory_tgt' := option_to_list (Cmd.get_def_memory tgt) in
  let def_src := IdTSet_from_list (List.map (IdT.lift Tag.physical) def_src') in
  let def_tgt := IdTSet_from_list (List.map (IdT.lift Tag.physical) def_tgt') in
  let def_memory_src := PtrSet_from_list def_memory_src' in
  let def_memory_tgt := PtrSet_from_list def_memory_tgt' in
  let uses_src := AtomSetImpl_from_list (Cmd.get_ids src) in
  let uses_tgt := AtomSetImpl_from_list (Cmd.get_ids tgt) in

  if negb (postcond_cmd_inject_event src tgt inv0)
  then None
  else
  if negb (AtomSetImpl.is_empty (AtomSetImpl.inter (AtomSetImpl_from_list def_src') uses_src) &&
           AtomSetImpl.is_empty (AtomSetImpl.inter (AtomSetImpl_from_list def_tgt') uses_tgt))
  then None
  else

  let inv1 := Forget.t def_src def_tgt inv0 in
  let inv2 := ForgetMemory.t def_memory_src def_memory_tgt inv1 in
  let inv3 := Invariant.update_src (Invariant.update_lessdef (postcond_cmd_add_lessdef src)) inv2 in
  let inv4 := Invariant.update_tgt (Invariant.update_lessdef (postcond_cmd_add_lessdef tgt)) inv3 in
  let inv5 := Invariant.update_src (Invariant.update_diffblock (postcond_cmd_add_diffblock src inv4.(Invariant.src).(Invariant.allocas))) inv4 in
  let inv6 := Invariant.update_tgt (Invariant.update_diffblock (postcond_cmd_add_diffblock tgt inv5.(Invariant.tgt).(Invariant.allocas))) inv5 in
  let inv7 := postcond_cmd_add_private_allocas src tgt inv6 in
  let inv8 := remove_def_from_maydiff src tgt inv7 in
  let inv9 := reduce_maydiff inv8 in
  Some inv9.
