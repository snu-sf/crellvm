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

Module Snapshot.
  Definition IdT (i:IdT.t): bool :=
    if Tag.eq_dec (fst i) Tag.previous
    then true
    else false.

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

  Definition unary (inv0:Invariant.unary): Invariant.unary :=
    let inv1 := Invariant.update_lessdef ExprPairSet inv0 in
    let inv2 := Invariant.update_noalias ValueTPairSet inv1 in
    let inv3 := Invariant.update_allocas IdTSet inv2 in
    let inv4 := Invariant.update_private IdTSet inv3 in
    inv4.

  Definition t (inv0:Invariant.t): Invariant.t :=
    let inv1 := Invariant.update_src unary inv0 in
    let inv2 := Invariant.update_tgt unary inv1 in
    let inv3 := Invariant.update_maydiff IdTSet inv2 in
    inv3.
End Snapshot.

Module Forget.
  Definition unary (ids:IdTSet.t) (inv0:Invariant.unary): Invariant.unary :=
    let inv1 := Invariant.update_lessdef (ExprPairSet.filter (compose negb (LiftPred.ExprPair (flip IdTSet.mem ids)))) inv0 in
    let inv2 := Invariant.update_noalias (ValueTPairSet.filter (compose negb (LiftPred.ValueTPair (flip IdTSet.mem ids)))) inv1 in
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
  Definition is_noalias_IdT (inv:Invariant.unary) (ids:IdTSet.t) (idt:IdT.t): bool :=
    IdTSet.for_all (Invariant.is_noalias inv idt) ids.

  Definition is_noalias_ValueT (inv:Invariant.unary) (ids:IdTSet.t) (v:ValueT.t): bool :=
    match v with
      | ValueT.id idt => is_noalias_IdT inv ids idt
      | ValueT.const _ => true
    end.

  Definition is_noalias_ValueTPair (inv:Invariant.unary) (ids:IdTSet.t) (ep:ValueTPair.t): bool :=
    is_noalias_ValueT inv ids (fst ep) && is_noalias_ValueT inv ids (snd ep).

  Definition is_noalias_Expr (inv:Invariant.unary) (ids:IdTSet.t) (e:Expr.t): bool :=
    match e with
      | Expr.load v ty al => is_noalias_ValueT inv ids v
      | _ => true
    end.

  Definition is_noalias_ExprPair (inv:Invariant.unary) (ids:IdTSet.t) (ep:ExprPair.t): bool :=
    is_noalias_Expr inv ids (fst ep) && is_noalias_Expr inv ids (snd ep).

  Definition unary (ids:IdTSet.t) (inv0:Invariant.unary): Invariant.unary :=
    let inv1 := Invariant.update_lessdef (ExprPairSet.filter (is_noalias_ExprPair inv0 ids)) inv0 in
    let inv2 := Invariant.update_noalias (ValueTPairSet.filter (is_noalias_ValueTPair inv0 ids)) inv1 in
    inv2.

  Definition t (s_src s_tgt:IdTSet.t) (inv0:Invariant.t): Invariant.t :=
    let inv1 := Invariant.update_src (unary s_src) inv0 in
    let inv2 := Invariant.update_tgt (unary s_tgt) inv1 in
    inv2.
End ForgetMemory.

Definition reduce_maydiff (inv0:Invariant.t): Invariant.t :=
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
  inv1.

Module Cmd.
  Definition t := cmd.

  Definition get_def (c:t): option id := getCmdID c.

  Definition get_def_memory (c:t): option id :=
    match c with
    | insn_malloc x ty v a => Some x
    | insn_free x ty v => getValueID v
    | insn_alloca x ty v a => Some x
    | insn_store x ty v p a => getValueID p
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

  Definition get_uses (c:cmd): list id :=
    match c with
    | insn_nop _ => []
    | insn_bop x b s v1 v2 => (Value.get_uses v1) ++ (Value.get_uses v2)
    | insn_fbop x fb fp v1 v2 => (Value.get_uses v1) ++ (Value.get_uses v2)
    | insn_extractvalue x ty1 v lc ty2 => (Value.get_uses v)
    | insn_insertvalue x ty1 v1 ty2 v2 lc => (Value.get_uses v1) ++ (Value.get_uses v2)
    | insn_malloc x ty v a => (Value.get_uses v)
    | insn_free x ty v => (Value.get_uses v)
    | insn_alloca x ty v a => (Value.get_uses v)
    | insn_load x ty p a => (Value.get_uses p)
    | insn_store x ty v p a => (Value.get_uses v) ++ (Value.get_uses p)
    | insn_gep x ib ty1 v lsv ty2 => (Value.get_uses v) ++ concat (List.map Value.get_uses (List.map snd lsv))
    | insn_trunc x trop ty1 v ty2 => (Value.get_uses v)
    | insn_ext x eop ty1 v ty2 => (Value.get_uses v)
    | insn_cast x cop ty1 v ty2 => (Value.get_uses v)
    | insn_icmp x con ty v1 v2 => (Value.get_uses v1) ++ (Value.get_uses v2)
    | insn_fcmp x fcon fp v1 v2 => (Value.get_uses v1) ++ (Value.get_uses v2)
    | insn_select x v1 ty v2 v3 => (Value.get_uses v1) ++ (Value.get_uses v2) ++ (Value.get_uses v3)
    | insn_call x nr attr ty va f ps => (Value.get_uses f) ++ concat (List.map Value.get_uses (List.map snd ps))
    end.
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

Definition postcond_cmd_add_noalias
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
  let def_memory_src := IdTSet_from_list (List.map (IdT.lift Tag.physical) def_memory_src') in
  let def_memory_tgt := IdTSet_from_list (List.map (IdT.lift Tag.physical) def_memory_tgt') in
  let uses_src := AtomSetImpl_from_list (Cmd.get_uses src) in
  let uses_tgt := AtomSetImpl_from_list (Cmd.get_uses tgt) in

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
  let inv5 := Invariant.update_src (Invariant.update_noalias (postcond_cmd_add_noalias src inv4.(Invariant.src).(Invariant.allocas))) inv4 in
  let inv6 := Invariant.update_tgt (Invariant.update_noalias (postcond_cmd_add_noalias tgt inv5.(Invariant.tgt).(Invariant.allocas))) inv5 in
  let inv7 := postcond_cmd_add_private_allocas src tgt inv6 in
  let inv8 := remove_def_from_maydiff src tgt inv7 in
  let inv9 := reduce_maydiff inv8 in
  Some inv9.
