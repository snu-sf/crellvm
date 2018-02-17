Require Import List.
Require Import syntax.
Require Import alist.
Require Import FMapWeakList.

Require Import sflib.
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

Module Cmd.
  Definition t := cmd.

  Definition get_def (c:t): option id := getCmdID c.

  Definition get_def_memory (c:t): option Ptr.t :=
    match c with
    | insn_free x ty p =>
      Some (ValueT.lift Tag.physical p, ty)
    | insn_store x ty v p a =>
      Some (ValueT.lift Tag.physical p, ty)
    | _ => None
    end.

  Definition get_rhs (c:t): option Expr.t :=
    match c with
    | insn_nop _ => None
    | insn_bop x b s v1 v2 =>
      Some (Expr.bop b s (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))
    | insn_fbop x fb fp v1 v2 =>
      Some (Expr.fbop fb fp (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2))
    | insn_extractvalue x ty1 v lc ty2 =>
      Some (Expr.extractvalue ty1 (ValueT.lift Tag.physical v) lc ty2)
    | insn_insertvalue x ty1 v1 ty2 v2 lc =>
      Some (Expr.insertvalue ty1 (ValueT.lift Tag.physical v1)
                             ty2 (ValueT.lift Tag.physical v2) lc)
    | insn_malloc x ty v a => None
    | insn_free x ty v => None
    | insn_alloca x ty v a => None
    | insn_load x ty p a => Some (Expr.load (ValueT.lift Tag.physical p) ty a)
    | insn_store x ty v p a => None
    | insn_gep x ib ty1 v lsv ty2 =>
      let lsvT :=
          List.map (fun elt => (fst elt, ValueT.lift Tag.physical (snd elt))) lsv in
      Some (Expr.gep ib ty1 (ValueT.lift Tag.physical v) lsvT ty2)
    | insn_trunc x trop ty1 v ty2 =>
      Some (Expr.trunc trop ty1 (ValueT.lift Tag.physical v) ty2)
    | insn_ext x eop ty1 v ty2 =>
      Some (Expr.ext eop ty1 (ValueT.lift Tag.physical v) ty2)
    | insn_cast x cop ty1 v ty2 =>
      Some (Expr.cast cop ty1 (ValueT.lift Tag.physical v) ty2)
    | insn_icmp x con ty v1 v2 =>
      Some (Expr.icmp con ty
                      (ValueT.lift Tag.physical v1)
                      (ValueT.lift Tag.physical v2))
    | insn_fcmp x fcon fp v1 v2 =>
      Some (Expr.fcmp fcon fp
                      (ValueT.lift Tag.physical v1)
                      (ValueT.lift Tag.physical v2))
    | insn_select x v1 ty v2 v3 =>
      Some (Expr.select (ValueT.lift Tag.physical v1) ty
                        (ValueT.lift Tag.physical v2)
                        (ValueT.lift Tag.physical v3))
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

    Definition get_leaked_values_to_memory (c: t): option value :=
    match c with
      | insn_store x ty v p a => Some v
      | _ => None
    end.

    Definition get_leaked_values (c: t): list value :=
    match c with
      | insn_nop _ => []
      | insn_store _ _ _ _ _ => []
      | insn_bop x b s v1 v2 => [v1 ; v2]
      | insn_fbop x fb fp v1 v2 => [v1 ; v2]
      | insn_extractvalue x ty1 v lc ty2 => [v]
      | insn_insertvalue x ty1 v1 ty2 v2 lc => [v1 ; v2]
      | insn_malloc x ty v a => [v]
      | insn_free x ty v => [v]
      | insn_alloca x ty v a => [v]
      | insn_load x ty p a => []
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

  Definition get_leaked_ids (c: t): list id :=
    TODO.filter_map Value.get_ids (get_leaked_values c).

  Definition get_leaked_ids_to_memory (c: t): option id :=
    match get_leaked_values_to_memory c with
    | Some v => Value.get_ids v
    | None => None
    end.
End Cmd.

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

  Definition ValueTPair (ep:ValueTPair.t): ValueTPair.t :=
    (ValueT (fst ep), ValueT (snd ep)).

  Definition Expr (e:Expr.t): Expr.t :=
    match e with
    | Expr.bop op s v1 v2 => Expr.bop op s (ValueT v1) (ValueT v2)
    | Expr.fbop op fp v1 v2 => Expr.fbop op fp (ValueT v1) (ValueT v2)
    | Expr.extractvalue ty1 v lc ty2 => Expr.extractvalue ty1 (ValueT v) lc ty2
    | Expr.insertvalue ty1 v1 ty2 v2 lc =>
      Expr.insertvalue ty1 (ValueT v1) ty2 (ValueT v2) lc
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
    let inv2 :=
        ValueTPairSet.union inv1 (ValueTPairSetFacts.map Previousify.ValueTPair inv1) in
    inv2.

  Definition ExprPairSet (inv0:ExprPairSet.t): ExprPairSet.t :=
    let inv1 := ExprPairSet.filter (compose negb (LiftPred.ExprPair IdT)) inv0 in
    let inv2 := ExprPairSet.union inv1 (ExprPairSetFacts.map Previousify.ExprPair inv1) in
    inv2.

  Definition IdTSet (inv0:IdTSet.t): IdTSet.t :=
    let inv1 := IdTSet.filter (compose negb IdT) inv0 in
    let inv2 := IdTSet.union inv1 (IdTSetFacts.map Previousify.IdT inv1) in
    inv2.

  Definition PtrSet (inv0:PtrSet.t): PtrSet.t :=
    let inv1 := PtrSet.filter (compose negb Ptr) inv0 in
    let inv2 := PtrSet.union inv0 (PtrSetFacts.map Previousify.Ptr inv1) in
    inv2.

  Definition noalias (inv0:PtrPairSet.t): PtrPairSet.t :=
    let inv1 := PtrPairSet.filter (compose negb (LiftPred.PtrPair IdT)) inv0 in
    let inv2 := PtrPairSet.union inv1 (PtrPairSetFacts.map Previousify.PtrPair inv1) in
    inv2.

  Definition diffblock (inv0:ValueTPairSet.t): ValueTPairSet.t :=
    let inv1 := ValueTPairSet.filter (compose negb (LiftPred.ValueTPair IdT)) inv0 in
    let inv2 :=
        ValueTPairSet.union inv1 (ValueTPairSetFacts.map Previousify.ValueTPair inv1) in
    inv2.

  Definition alias (inv0: Assertion.aliasrel): Assertion.aliasrel :=
    let inv1 := Assertion.update_noalias_rel noalias inv0 in
    let inv2 := Assertion.update_diffblock_rel diffblock inv1 in
    inv2.

  Definition physical_previous_lessdef (inv:Assertion.unary): ExprPairSet.t :=
    let idt_set := IdTSetFacts.from_list (Assertion.get_idTs_unary inv) in
    let prev_idt_set := IdTSet.filter IdT idt_set in
    IdTSet.fold
      (fun idt eps =>
         let id_expr_prev := Expr.value (ValueT.id idt) in
         let id_expr_phys := Expr.value (ValueT.id (IdT.lift Tag.physical (snd idt))) in
         (ExprPairSet.add (id_expr_phys, id_expr_prev)
                          (ExprPairSet.add (id_expr_prev, id_expr_phys) eps)))
      prev_idt_set ExprPairSet.empty.

  Definition unary (inv0:Assertion.unary): Assertion.unary :=
    let inv1 := Assertion.update_lessdef ExprPairSet inv0 in
    let inv2 := Assertion.update_alias alias inv1 in
    let inv3 := Assertion.update_private IdTSet inv2 in
    let inv4 := Assertion.update_lessdef
                  (ExprPairSet.union
                     (physical_previous_lessdef inv3)) inv3 in
    inv4.

  Definition t (inv0:Assertion.t): Assertion.t :=
    let inv1 := Assertion.update_src unary inv0 in
    let inv2 := Assertion.update_tgt unary inv1 in
    let inv3 := Assertion.update_maydiff IdTSet inv2 in
    inv3.
End Snapshot.

Definition lift_physical_atoms_idtset (a:atoms): IdTSet.t :=
  AtomSetImpl.fold (IdTSet.add <*> (IdT.lift Tag.physical)) a IdTSet.empty.

Lemma lift_physical_atoms_idtset_spec1
      id l:
  IdTSet.mem (Tag.physical, id) (lift_physical_atoms_idtset l) =
  AtomSetImpl.mem id l.
Proof.
  unfold lift_physical_atoms_idtset.
  rewrite AtomSetProperties.fold_spec_right.
  rewrite AtomSetFacts.elements_b, existsb_rev.
  unfold AtomSetImpl.elt.
  induction (rev (AtomSetImpl.elements l)); ss.
  unfold compose at 1. ss.
  rewrite IdTSetFacts.add_b, IHl0. f_equal.
  unfold IdT.lift, IdTSetFacts.eqb, AtomSetFacts.eqb.
  repeat (des_if; ss).
  - apply IdT.compare_leibniz in e. by inv e.
  - contradict n.
    subst. apply IdTSet.E.eq_refl.
Qed.

Module ForgetMemory.
  Definition is_noalias_Ptr
             (inv:Assertion.unary) (ps:Ptr.t) (p:Ptr.t): bool :=
    ((negb (ValueT.eq_dec ps.(fst) p.(fst))) && Assertion.is_unique_ptr inv p && Assertion.values_diffblock_from_unique (fst ps)) ||
    ((negb (ValueT.eq_dec ps.(fst) p.(fst))) && Assertion.is_unique_ptr inv ps && Assertion.values_diffblock_from_unique (fst p)) ||
    Assertion.is_noalias inv p ps ||
    Assertion.is_diffblock inv p ps.

  Definition is_noalias_Expr
             (inv:Assertion.unary) (ps:Ptr.t) (e:Expr.t): bool :=
    match e with
      | Expr.load v ty al => is_noalias_Ptr inv ps (v, ty)
      | _ => true
    end.

  Definition is_noalias_ExprPair
             (inv:Assertion.unary) (ps:Ptr.t) (ep:ExprPair.t): bool :=
    is_noalias_Expr inv ps ep.(fst) && is_noalias_Expr inv ps ep.(snd).

  Definition unary (def_mem:option Ptr.t) (leak_mem:option id) (inv0:Assertion.unary): Assertion.unary :=
    let inv1 :=
        match def_mem with
        | Some def_mem => Assertion.update_lessdef (ExprPairSet.filter (is_noalias_ExprPair inv0 def_mem)) inv0
        | None => inv0
        end
    in
    let inv2 :=
        match leak_mem with
        | Some leak_mem => Assertion.update_unique (AtomSetImpl.remove leak_mem) inv1
        | None => inv1
        end
    in
    inv2.

  Definition t (def_mem_src def_mem_tgt:option Ptr.t) (leak_mem_src leak_mem_tgt:option id) (inv0:Assertion.t): Assertion.t :=
    let inv1 := Assertion.update_src (unary def_mem_src leak_mem_src) inv0 in
    let inv2 := Assertion.update_tgt (unary def_mem_tgt leak_mem_tgt) inv1 in
    inv2.
End ForgetMemory.

Module ForgetStack.
  Definition alias (ids:AtomSetImpl.t) (inv0:Assertion.aliasrel): Assertion.aliasrel :=
    let inv1 :=
        Assertion.update_diffblock_rel
          (ValueTPairSet.filter
             (compose negb (LiftPred.ValueTPair ((flip IdTSet.mem (lift_physical_atoms_idtset ids)))))) inv0 in
    let inv2 :=
        Assertion.update_noalias_rel
          (PtrPairSet.filter
             (compose negb (LiftPred.PtrPair (flip IdTSet.mem (lift_physical_atoms_idtset ids))))) inv1 in
    inv2.

  Definition unary (defs leaks:AtomSetImpl.t) (inv0:Assertion.unary): Assertion.unary :=
    let inv1 :=
        Assertion.update_lessdef
          (ExprPairSet.filter
             (negb <*> (LiftPred.ExprPair (flip IdTSet.mem (lift_physical_atoms_idtset defs))))) inv0 in
    let inv2 := Assertion.update_alias (alias defs) inv1 in
    let inv3 := Assertion.update_unique (AtomSetImpl.filter
         (fun i => negb (AtomSetImpl.mem i (AtomSetImpl.union defs leaks)))) inv2 in
    let inv4 :=
        Assertion.update_private
          (IdTSet.filter (compose negb (flip IdTSet.mem (lift_physical_atoms_idtset defs)))) inv3 in
    inv4.

  Definition t (defs_src defs_tgt leaks_src leaks_tgt :AtomSetImpl.t) (inv0:Assertion.t): Assertion.t :=
    let inv1 := Assertion.update_src (unary defs_src leaks_src) inv0 in
    let inv2 := Assertion.update_tgt (unary defs_tgt leaks_tgt) inv1 in
    let inv3 := Assertion.update_maydiff (IdTSet.union (lift_physical_atoms_idtset (AtomSetImpl.union defs_src defs_tgt))) inv2 in
    inv3.
End ForgetStack.

Module ForgetMemoryCall.
  Definition is_private_Expr (inv:Assertion.unary) (e:Expr.t): bool :=
    match e with
    | Expr.load v ty al =>
      match v with
      | ValueT.id idt =>
        IdTSet.mem idt inv.(Assertion.private)
      | _ => false
      end
    | _ => true
    end.

  Definition is_private_ExprPair (inv:Assertion.unary) (ep:ExprPair.t): bool :=
    is_private_Expr inv ep.(fst) && is_private_Expr inv ep.(snd).

  Definition unary (inv0:Assertion.unary): Assertion.unary :=
    let inv1 := Assertion.update_lessdef
                  (ExprPairSet.filter (is_private_ExprPair inv0)) inv0 in
    let inv2 := Assertion.update_unique
                  (AtomSetImpl.filter (fun x => IdTSet.mem (Tag.physical, x) inv1.(Assertion.private))) inv1 in
    inv2.

  Definition t (inv0:Assertion.t): Assertion.t :=
    let inv1 := Assertion.update_src unary inv0 in
    let inv2 := Assertion.update_tgt unary inv1 in
    inv2.
End ForgetMemoryCall.

Module ForgetStackCall.
  Definition t (defs_src defs_tgt :AtomSetImpl.t) (inv0:Assertion.t): Assertion.t :=
    ForgetStack.t defs_src defs_tgt AtomSetImpl.empty AtomSetImpl.empty inv0.
End ForgetStackCall.

(* Definition reduce_maydiff_lessdef_old (inv0:Assertion.t): Assertion.t := *)
(*   let lessdef_src := inv0.(Assertion.src).(Assertion.lessdef) in *)
(*   let lessdef_tgt := inv0.(Assertion.tgt).(Assertion.lessdef) in *)
(*   let inject_id id := Assertion.inject_value inv0 (ValueT.id id) (ValueT.id id) *)
(*       (* negb (ExprPairSet.exists_ *) *)
(*       (*         (fun p => ExprPairSet.exists_ *) *)
(*       (*                     (fun q => Assertion.not_in_maydiff_expr inv0 (snd p)) *) *)
(*       (*                     (ExprPairSet.filter (fun q => ExprFacts.eq_dec_l (snd p) (fst q)) *) *)
(*       (*                                         (Assertion.get_lhs lessdef_tgt (fst p)))) *) *)
(*       (*         (Assertion.get_rhs lessdef_src *) *)
(*       (*                            (Expr.value (ValueT.id id)))) *) *)
(*   in *)
(*   (* O(|MD| * |LD| * log|LD|) *) *)
(*   Assertion.update_maydiff (IdTSet.filter (negb <*> inject_id)) inv0. *)

(*
swap: |LD|
intersection: |LD| * log |LD|
not_in_maydiff check: |LD| * log |MD|
*)

Definition swap_pair A (aa: A * A): A * A := (aa.(snd), aa.(fst)).

(* Definition swap_ExprPairSet (ld: ExprPairSet.t): ExprPairSet.t := *)
(*   ExprPairSet.fold (fun i s => ExprPairSet.add (swap_pair i) s) ld ExprPairSet.empty *)
(* . *)

(* get_IdT is already used in different meaning.. *)
(* it seems original get_IdT should be "collect_IdT", and this should be get_IdT *)
Definition project_into_IdT (e: Expr.t): option IdT.t :=
  match e with
  | Expr.value (ValueT.id i) => Some i
  | _ => None
  end
.

Definition project_into_IdTSet (ld: ExprPairSet.t): IdTSet.t :=
  ExprPairSet.fold (fun e s => match project_into_IdT e.(fst) with
                               | Some i => IdTSet.add i s
                               | None => s
                               end) ld IdTSet.empty
.

(* Definition reduce_maydiff_lessdef (inv0: Assertion.t): Assertion.t := *)
(*   let lessdef_src := inv0.(Assertion.src).(Assertion.lessdef) in *)
(*   let lessdef_tgt := inv0.(Assertion.tgt).(Assertion.lessdef) in *)
(*   let lessdef_tgt_swapped := swap_ExprPairSet lessdef_tgt in *)
(*   (* Time: |LD| * log |LD| *) *)
(*   let intersection := ExprPairSet.inter lessdef_src lessdef_tgt_swapped in *)
(*   (* Time: |LD| * log |LD| *) *)
(*   (* Size: |LD| *) *)
(*   let injected_intersection := *)
(*       ExprPairSet.filter (fun xy => Assertion.not_in_maydiff_expr inv0 xy.(snd)) intersection in *)
(*   (* Time: |LD| * log |MD| *) *)
(*   (* Size: |LD| *) *)
(*   let injected_idt := project_into_IdTSet injected_intersection in *)
(*   (* Time: |LD| * log |LD| *) *)
(*   (* Size: |LD| *) *)
(*   Assertion.update_maydiff (fun md => IdTSet.diff md injected_idt) inv0 *)
(*   (* Time: |MD| * log |MD| *) *)
(* . *)

  (* let indirect_inject_id (id: IdT.t) := *)
  (*     ExprPairSet.exists_ *)
  (*       (fun xy => (ExprFacts.eq_dec_l (Expr.value (ValueT.id id)) xy.(fst)) *)
  (*                    && Assertion.not_in_maydiff_expr inv0 xy.(snd)) intersection in *)
(* Time: |LD| * log |MD| *)
  (* Assertion.update_maydiff (IdTSet.filter (negb <*> indirect_inject_id)) inv0 *)
(* Time: |MD| * |LD| * log |MD| *)

(* Definition reduce_maydiff_lessdef (inv0: Assertion.t): Assertion.t := *)
Definition reduce_maydiff (inv0: Assertion.t): Assertion.t :=
  let ld_src := inv0.(Assertion.src).(Assertion.lessdef) in
  let ld_tgt := inv0.(Assertion.tgt).(Assertion.lessdef) in
  let ld_src_outer_idt :=
      ExprPairSet.filter (fun xy => project_into_IdT xy.(fst)) ld_src in
  (* Time: |LD| *)
  (* Size: |LD| *)
  let ld_src_mirrored_outer_idt :=
      ExprPairSet.filter (fun xy => let yx := (swap_pair xy) in
                                    ExprPairSet.mem yx ld_tgt) ld_src_outer_idt in
  (* Time: |LD| * log |LD| *)
  (* Size: |LD| *)
  let ld_src_mirrored_outer_idt_inner_injected :=
      ExprPairSet.filter (fun xy => Assertion.not_in_maydiff_expr inv0 xy.(snd)) ld_src_mirrored_outer_idt in
  (* Time: |LD| * log |MD| *)
  (* Size: |LD| *)
  let idts_of_interest := project_into_IdTSet ld_src_mirrored_outer_idt_inner_injected in
  (* Time: |LD| * log |LD| *)
  (* Size: |LD| *)
  Assertion.update_maydiff (fun md => IdTSet.diff md idts_of_interest) inv0
  (* Time: |MD| + |LD| *)
.

(* Definition reduce_maydiff (inv0:Assertion.t): Assertion.t := *)
  (* let inv1 := reduce_maydiff_lessdef inv0 in *)
  (* let inv2 := reduce_maydiff_non_physical inv1 in *)
  (* inv2. *)

(* TODO: unused. remove? *)
(* Definition reduce_maydiff_default (inv0:Assertion.t): Assertion.t := *)
(*   let lessdef_src := inv0.(Assertion.src).(Assertion.lessdef) in *)
(*   let lessdef_tgt := inv0.(Assertion.tgt).(Assertion.lessdef) in *)
(*   let equations := ExprPairSet.filter *)
(*                      (fun elt => ExprPairSet.mem (snd elt, fst elt) lessdef_tgt) *)
(*                      lessdef_src in *)
(*   let inv1 := Assertion.update_maydiff *)
(*                 (IdTSet.filter *)
(*                    (fun id => *)
(*                       negb (ExprPairSet.exists_ *)
(*                               (fun ep => *)
(*                                  ((ExprFacts.eq_dec_l (fst ep) *)
(*                                                (Expr.value (ValueT.id id))) *)
(*                                     && Assertion.not_in_maydiff_expr inv0 (snd ep))) *)
(*                               equations))) *)
(*                 inv0 in *)
(*   let inv2 := reduce_maydiff_non_physical inv1 in *)
(*   inv2. *)

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

  Definition get_lessdef (assigns:list assign): ExprPairSet.t :=
    let ld_assns :=
        List.fold_left
          (fun s eq =>
             ExprPairSet.add
               (eq.(fst), eq.(snd))
               (ExprPairSet.add (eq.(snd), eq.(fst)) s))
          (List.map get_equation assigns)
          ExprPairSet.empty
    in
    let defs:=
        List.fold_left
          (fun s a =>
             match a with
             | assign_intro x ty _ =>
               ExprPairSet.add (Expr.value (ValueT.const (const_undef ty)),
                                Expr.value (ValueT.id (Tag.physical, x))) s
             end
          )
          assigns
          ExprPairSet.empty
    in
    ExprPairSet.union ld_assns defs.
End Phinode.

Definition add_terminator_cond_lessdef
           (term:terminator)
           (l_to:l)
           (inv0:ExprPairSet.t): ExprPairSet.t :=
  match term with
  | insn_br _ v l1 l2 =>
    if (l_dec l1 l2)
    then inv0
    else
    let cond_val := if (l_dec l_to l1) then 1%Z else 0%Z in
    let expr1 := Expr.value (ValueT.lift Tag.physical v) in
    let expr2 := Expr.value
                   (ValueT.const (const_int Size.One (INTEGER.of_Z (Size.to_Z Size.One) cond_val true))) in
    ExprPairSet.add
      (expr1, expr2)
      (ExprPairSet.add (expr2, expr1) inv0)
  | insn_switch _ ty v l_dflt cl_l =>
    if (l_dec l_to l_dflt)
    then inv0
    else
    match filter (fun cl => (l_dec l_to (snd cl))) cl_l with
    | cl::nil =>
      match (fst cl), ty with
      | const_int _ i, typ_int sz =>
        let expr1 := Expr.value (ValueT.lift Tag.physical v) in
        let expr2 := Expr.value (ValueT.const (const_int sz i)) in
        ExprPairSet.add
          (expr1, expr2)
          (ExprPairSet.add (expr2, expr1) inv0)
      | _, _ => inv0
      end
    | _ => inv0
    end
  | _ => inv0
  end.

Definition add_terminator_cond
           (inv0:Assertion.t)
           (term_src term_tgt:terminator)
           (l_to:l): Assertion.t :=
  let inv1 :=
      Assertion.update_src
        (Assertion.update_lessdef
           (add_terminator_cond_lessdef term_src l_to))
        inv0
  in
  let inv2 :=
      Assertion.update_tgt
        (Assertion.update_lessdef
           (add_terminator_cond_lessdef term_tgt l_to))
        inv1
  in
  inv2.

Definition postcond_phinodes_add_lessdef
           (assigns:list Phinode.assign)
           (inv0:ExprPairSet.t): ExprPairSet.t :=
  ExprPairSet.union inv0 (Phinode.get_lessdef assigns).

Definition postcond_phinodes_assigns
           (assigns_src assigns_tgt:list Phinode.assign)
           (inv0:Assertion.t): option Assertion.t :=
  let defs_src := List.map Phinode.get_def assigns_src in
  let defs_tgt := List.map Phinode.get_def assigns_tgt in
  let uses_src := filter_map Phinode.get_use assigns_src in
  let uses_tgt := filter_map Phinode.get_use assigns_tgt in

  if negb (unique id_dec defs_src && unique id_dec defs_tgt)
  then None
  else

  let inv1 := Snapshot.t inv0 in
  let inv2 := ForgetStack.t (AtomSetImpl_from_list defs_src)
                       (AtomSetImpl_from_list defs_tgt)
                       (AtomSetImpl_from_list uses_src)
                       (AtomSetImpl_from_list uses_tgt)
                       inv1
  in
  let inv3 :=
      Assertion.update_src
        (Assertion.update_lessdef (postcond_phinodes_add_lessdef assigns_src)) inv2 in
  let inv4 :=
      Assertion.update_tgt
        (Assertion.update_lessdef (postcond_phinodes_add_lessdef assigns_tgt)) inv3 in
  let inv5 := reduce_maydiff inv4 in
  Some inv5.

Definition postcond_phinodes
           (l_from:l)
           (phinodes_src phinodes_tgt:phinodes)
           (inv0:Assertion.t): option Assertion.t :=
  match forallb_map (Phinode.resolve l_from) phinodes_src,
        forallb_map (Phinode.resolve l_from) phinodes_tgt with
  | Some assigns_src, Some assigns_tgt =>
    postcond_phinodes_assigns assigns_src assigns_tgt inv0
  | _, _ => None
  end.

Definition may_produce_UB (b0: bop): bool :=
  match b0 with
  | bop_udiv => true
  | bop_sdiv => true
  | bop_urem => true
  | bop_srem => true
  | _ => false
  end
.

Definition is_known_total (e0: Expr.t): bool :=
  match e0 with
  | Expr.value (ValueT.id idt0) => true
  | Expr.value (ValueT.const (const_undef ty0)) => true
  | _ => false
  end
.

(* Spec: if e0 is known to be calculated, then retval of this fuc is known to be nonzero *)
(* TODO: better definition, name, spec? *)
(* TODO: Under current semantics, this spec does not hold: undef/0 is calculated to undef. *)
(* However, it is problem of semantics, undef/0 should give UB too. calc denom first. *)
Definition get_dangerous_denom (e0: Expr.t): option ValueT.t :=
  match e0 with
  | Expr.bop b1 sz1 va1 vb1 =>
    if may_produce_UB b1
    then Some vb1
    else None
  | _ => None
  end
.


(* 1. x is total *)
(* 2. by semantics of lessdef, y is calculated *)
(* 3. by spec of get_dangerous_denom, y is nonzero *)
(* 4. by def of injection, denom_tgt is nonzero (if it was zero, src too) *)

(* Note that, 1. this reasoning holds for non-int case *)
(* 2. Even if it does not hold, we can add type-checking on our assertion *)
Definition is_known_nonzero_by_src (inv: Assertion.t) (denom_tgt: value): bool :=
  ExprPairSet.exists_
    (fun xy =>
       (is_known_total (xy.(fst)))
         &&
         (match (get_dangerous_denom (xy.(snd))) with
          | Some y => (Assertion.inject_value inv y (ValueT.lift Tag.physical denom_tgt))
          | None => false
          end))
    (inv.(Assertion.src).(Assertion.lessdef))
.

Definition is_known_total_nonzero (e0: Expr.t): bool :=
  match e0 with
  | Expr.value (ValueT.const (const_int sz0 i0)) =>
    negb (INTEGER.dec (INTEGER.of_Z (Size.to_Z sz0) 0%Z true) i0)
  | _ => false
  end
.

Definition is_known_nonzero_unary (inv: Assertion.unary) (denom: value): bool :=
  ExprPairSet.exists_
    (fun xy =>
       (is_known_total_nonzero xy.(fst))
         &&
         Expr.eq_dec (xy.(snd)) (ValueT.lift Tag.physical denom))
    (inv.(Assertion.lessdef))
.

Definition postcond_cmd_inject_event
           (src tgt:cmd)
           (inv:Assertion.t): bool :=
  match src, tgt with
  | insn_call x1 nr1 cl1 t1 va1 v1 p1,
    insn_call x2 nr2 cl2 t2 va2 v2 p2 =>
    noret_dec nr1 nr2 &&
    clattrs_dec cl1 cl2 &&
    typ_dec t1 t2 &&
    varg_dec va1 va2 &&
    (Assertion.inject_value
       inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2)) &&
    list_forallb2
      (fun p1 p2 =>
         let '(ty1, attr1, v1) := p1 in
         let '(ty2, attr2, v2) := p2 in
         typ_dec ty1 ty2 &&
         attributes_dec attr1 attr2 &&
         (Assertion.inject_value
            inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2)))
      p1 p2
  | insn_call _ _ _ _ _ _ _, _
  | _, insn_call _ _ _ _ _ _ _ => false

  | insn_store _ t1 v1 p1 a1,
    insn_store _ t2 v2 p2 a2 =>
    typ_dec t1 t2 &&
    (Assertion.inject_value
       inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2)) &&
    (Assertion.inject_value
       inv (ValueT.lift Tag.physical p1) (ValueT.lift Tag.physical p2)) &&
    align_dec a1 a2
  | insn_store _ t1 v1 p1 a1, insn_nop _ =>
    Assertion.is_private inv.(Assertion.src) (ValueT.lift Tag.physical p1)
  | insn_store _ _ _ _ _, _
  | _, insn_store _ _ _ _ _ => false

  | insn_load x1 t1 v1 a1, insn_load x2 t2 v2 a2 =>
    typ_dec t1 t2 &&
    (Assertion.inject_value
       inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2)) &&
    align_dec a1 a2
  (* | insn_nop _, insn_load x t v a => *)
  (*   (ExprPairSet.exists_ *)
  (*       (fun e_pair => *)
  (*          match e_pair with *)
  (*          | (e1, e2) => *)
  (*            andb *)
  (*            (ExprFacts.eq_dec_l e1 (Expr.value (ValueT.const (const_undef t)))) *)
  (*            (ExprFacts.eq_dec_l e2 (Expr.load (ValueT.lift Exprs.Tag.physical v) t a)) *)
  (*          end) inv.(Assertion.src).(Assertion.lessdef)) *)
  (*     && *)
  (*     Assertion.not_in_maydiff inv (ValueT.lift Exprs.Tag.physical v) *)
  (* @alxest: For more info: Issue#426 *)

  | _, insn_load _ _ _ _ => false

  | insn_free _ t1 p1, insn_free _ t2 p2 =>
    typ_dec t1 t2 &&
    (Assertion.inject_value
       inv (ValueT.lift Tag.physical p1) (ValueT.lift Tag.physical p2))
  | insn_free _ _ _, _
  | _, insn_free _ _ _ => false

  | insn_alloca x1 t1 v1 a1, insn_alloca x2 t2 v2 a2 =>
    id_dec x1 x2 &&
    typ_dec t1 t2 &&
    (Assertion.inject_value
       inv (ValueT.lift Tag.physical v1) (ValueT.lift Tag.physical v2)) &&
    align_dec a1 a2
  | insn_alloca _ _ _ _, insn_nop _ => true
  (* | insn_nop _, insn_alloca _ _ _ _ => true *)

  (* | insn_alloca _ _ _ _, _ => false *)
  | _, insn_alloca _ _ _ _ => false
  (* This change is introduced by @alxest, when sanitizing semantics of alloca *)
  (* We can allow nop-alloca case when arg is known to be int. *)
  (* This will sufficiently allow register spilling to be validated. *)
  (* We can also make new predicate (:= is defined && int) for more power *)

  | insn_malloc _ _ _ _, _ => false
  | _, insn_malloc _ _ _ _ => false

  | insn_bop _ b0 sz0 va0 vb0, insn_bop _ b1 sz1 va1 vb1 =>
    if (may_produce_UB b1)
    then (bop_dec b0 b1)
           && (sz_dec sz0 sz1)
           && (Assertion.inject_value inv (ValueT.lift Tag.physical va0) (ValueT.lift Tag.physical va1))
           && (Assertion.inject_value inv (ValueT.lift Tag.physical vb0) (ValueT.lift Tag.physical vb1))
    else true
  | _, insn_bop _ b1 sz1 va1 vb1 =>
    if (may_produce_UB b1)
    then (is_known_total_nonzero (ValueT.lift Tag.physical vb1))
         || (is_known_nonzero_by_src inv vb1)
         || (is_known_nonzero_unary inv.(Assertion.src) vb1)
    else true
  | _, _ => true
  end.

Lemma postcond_cmd_inject_event_non_malloc
      src tgt inv
      (INJECT: postcond_cmd_inject_event src tgt inv)
  :
    (<<NONMALLOC_SRC: (isMallocInst src = false)>>)
    /\ (<<NONMALLOC_TGT: (isMallocInst tgt = false)>>).
Proof.
  destruct src, tgt; ss.
Qed.

(* TODO: we will not consider insn_malloc more. *)

(* This removes the defined register from maydiff in 2 cases *)
(* (alloca, call) because postcond do not *)
(* produce any lessdef information from them *)
(* so that reduce_maydiff doesn't remove them.   *)
Definition remove_def_from_maydiff (src tgt:id) (inv:Assertion.t): Assertion.t :=
  if id_dec src tgt
  then Assertion.update_maydiff (IdTSet.remove (IdT.lift Tag.physical src)) inv
  else inv.

Definition postcond_cmd_add_inject
           (src tgt:cmd)
           (inv0:Assertion.t): Assertion.t :=
  match src, tgt with
  | insn_alloca aid_src _ _ _, insn_alloca aid_tgt _ _ _ =>
    let inv1 :=
        Assertion.update_src
          (Assertion.update_unique
             (AtomSetImpl.add aid_src)) inv0 in
    let inv2 := inv1 in
        (* Assertion.update_tgt *)
        (*   (Assertion.update_unique *)
        (*      (AtomSetImpl.add aid_tgt)) inv1 in *)
    let inv3 := remove_def_from_maydiff aid_src aid_tgt inv2 in
    inv3

  | insn_alloca aid_src _ _ _, insn_nop _ =>
    let inv1 :=
        Assertion.update_src
          (Assertion.update_unique
             (AtomSetImpl.add aid_src)) inv0 in
    let inv2 :=
        Assertion.update_src
          (Assertion.update_private
             (IdTSet.add (IdT.lift Tag.physical aid_src))) inv1 in
    inv2

  | insn_nop _, insn_alloca aid_tgt _ _ _ =>
    let inv1 := inv0 in
        (* Assertion.update_tgt *)
        (*   (Assertion.update_unique *)
        (*      (AtomSetImpl.add aid_tgt)) inv0 in *)
    let inv2 :=
        Assertion.update_tgt
          (Assertion.update_private
             (IdTSet.add (IdT.lift Tag.physical aid_tgt))) inv1 in
    inv2

  | insn_call id_src false _ _ _ _ _, insn_call id_tgt false _ _ _ _ _ =>
    remove_def_from_maydiff id_src id_tgt inv0

  | _, _ => inv0
  end.

Definition postcond_cmd_get_lessdef
           (c:cmd): option ExprPair.t :=
  match Cmd.get_def c, Cmd.get_rhs c with
  | Some lhs, Some rhs => Some (Expr.value (IdT.lift Tag.physical lhs), rhs)
  | _, _ =>
    match c with
    | insn_store x ty v p a =>
      Some (Expr.load (ValueT.lift Tag.physical p) ty a,
            Expr.value (ValueT.lift Tag.physical v))
    | insn_alloca x ty v a =>
      Some (Expr.load (ValueT.id (IdT.lift Tag.physical x)) ty a,
            Expr.value (ValueT.const (const_undef ty)))
    | _ => None
    end
  end.

Definition postcond_cmd_get_definedness (c:cmd)
  : option ExprPair.t :=
  match Cmd.get_def c, getCmdTyp c with
  | Some x, Some ty =>
    Some (Expr.value (ValueT.const (const_undef ty)),
                    Expr.value (ValueT.id (Tag.physical, x)))
  | _, _ => None
  end.

Definition postcond_cmd_add_lessdef
           (c:cmd)
           (inv0:ExprPairSet.t): ExprPairSet.t :=
  let inv0 :=
      match postcond_cmd_get_definedness c with
      | None => inv0
      | Some exp_pair => ExprPairSet.add exp_pair inv0
      end
  in
  match postcond_cmd_get_lessdef c with
  | None =>
    inv0
  | Some (lhs, rhs) =>
    let inv1 := ExprPairSet.add (lhs, rhs) inv0 in
    let inv2 := ExprPairSet.add (rhs, lhs) inv1 in
    match (lhs, rhs) with
    | (Expr.load v ty a, _) =>
      if (align_dec a Align.One)
      then inv2
      else let inv3 := ExprPairSet.add (Expr.load v ty Align.One, rhs) inv2 in
           let inv4 := ExprPairSet.add (rhs, Expr.load v ty Align.One) inv3 in
      inv4
    | (_, Expr.load v ty a) =>
      if (align_dec a Align.One)
      then inv2
      else let inv3 := ExprPairSet.add (lhs, Expr.load v ty Align.One) inv2 in
           let inv4 := ExprPairSet.add (Expr.load v ty Align.One, lhs) inv3 in
      inv4
    | (_, _) => inv2
    end
  end.

Lemma postcond_cmd_add_lessdef_Subset c inv0
  :
    ExprPairSet.Subset inv0 (postcond_cmd_add_lessdef c inv0).
Proof.
  ii.
  destruct c;
    cbn; des_ifs;
    repeat (apply ExprPairSetFacts.add_iff; right); ss.
  unfold postcond_cmd_add_lessdef.
  unfold postcond_cmd_get_lessdef.
  ss.
  des_ifs.
  apply ExprPairSetFacts.add_iff. eauto.
Qed.

Definition filter_leaked
           (c:cmd) (uniq0:atoms): atoms :=
  let uses := AtomSetImpl_from_list (Cmd.get_ids c) in
  let leaked :=
      match c with
      | insn_load _ _ (value_id i) _
      | insn_store _ _ _ (value_id i) _ =>
        AtomSetImpl.remove i uses
      | _ =>
        uses
      end
  in
  let uniq := AtomSetImpl.diff uniq0 leaked in
  uniq.

Definition postcond_unique_leakage
           (src tgt:cmd)
           (inv0:Assertion.t): Assertion.t :=
  let inv1 := Assertion.update_src
                (Assertion.update_unique (filter_leaked src)) inv0 in
  let inv2 := Assertion.update_tgt
                (Assertion.update_unique (filter_leaked tgt)) inv1 in
  inv2.

Definition postcond_cmd_check
           (src tgt:cmd)
           (def_src def_tgt uses_src uses_tgt:AtomSetImpl.t)
           (inv0:Assertion.t): bool :=
  if negb (AtomSetImpl.is_empty (AtomSetImpl.inter def_src uses_src))
  then failwith_false "valid_cmds: postcond_cmd returned None, Case 1_src" nil
  else

  if negb (AtomSetImpl.is_empty (AtomSetImpl.inter def_tgt uses_tgt))
  then failwith_false "valid_cmds: postcond_cmd returned None, Case 1_tgt" nil
  else

  if negb (postcond_cmd_inject_event src tgt inv0)
  then failwith_false "valid_cmds: postcond_cmd returned None, Case 2" nil
  else

  true.

Definition postcond_cmd_add
           (src tgt:cmd)
           (inv0:Assertion.t): Assertion.t :=
  let inv1 := postcond_cmd_add_inject src tgt inv0 in
  let inv2 := Assertion.update_src
                (Assertion.update_lessdef (postcond_cmd_add_lessdef src)) inv1 in
  let inv3 := Assertion.update_tgt
                (Assertion.update_lessdef (postcond_cmd_add_lessdef tgt)) inv2 in
  let inv4 := reduce_maydiff inv3 in
  inv4.

Definition postcond_cmd
           (src tgt:cmd)
           (inv0:Assertion.t): option Assertion.t :=
  let def_src := AtomSetImpl_from_list (option_to_list (Cmd.get_def src)) in
  let def_tgt := AtomSetImpl_from_list (option_to_list (Cmd.get_def tgt)) in
  let uses_src := AtomSetImpl_from_list (Cmd.get_ids src) in
  let uses_tgt := AtomSetImpl_from_list (Cmd.get_ids tgt) in
  let leaks_src := AtomSetImpl_from_list (Cmd.get_leaked_ids src) in
  let leaks_tgt := AtomSetImpl_from_list (Cmd.get_leaked_ids tgt) in
  let def_memory_src := Cmd.get_def_memory src in
  let def_memory_tgt := Cmd.get_def_memory tgt in
  let leaks_memory_src := Cmd.get_leaked_ids_to_memory src in
  let leaks_memory_tgt := Cmd.get_leaked_ids_to_memory tgt in

  let inv2 :=
      if Instruction.isCallInst src
      then
        let inv1 := ForgetMemoryCall.t inv0 in
        ForgetStackCall.t def_src def_tgt inv1
      else
        let inv1 := ForgetMemory.t def_memory_src def_memory_tgt leaks_memory_src leaks_memory_tgt inv0 in
        ForgetStack.t def_src def_tgt leaks_src leaks_tgt inv1
  in
  if postcond_cmd_check src tgt def_src def_tgt uses_src uses_tgt inv2
  then Some (postcond_cmd_add src tgt inv2)
  else None.
