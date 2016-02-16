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
Require Import decs.
Require Import TODO.

Import ListNotations.
Set Implicit Arguments.

Definition Invariant_remove_idTs
           (ids: list IdT.t)
           (inv0:Invariant.unary): Invariant.unary :=
  inv0.

Definition Invariant_ghostify_idTs
           (ids: list id)
           (inv0:Invariant.unary): Invariant.unary :=
  inv0.

Definition ghostify_idTs
           (ids: list id)
           (s:IdTSet.t): IdTSet.t :=
  s.

Definition IdTSet_from_list
           (ids:list IdT.t): IdTSet.t :=
  IdTSet.empty.

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
    (Expr.value (IdT.lift (get_def a) Tag.physical),
     Expr.value (ValueT.lift (get_rhs a) Tag.ghost)).
End Phinode.

Definition forget
           (l_src l_tgt:list IdT.t)
           (inv0:Invariant.t): Invariant.t :=
  let src := Invariant_remove_idTs l_src inv0.(Invariant.src) in
  let tgt := Invariant_remove_idTs l_tgt inv0.(Invariant.tgt) in
  let maydiff := IdTSet.diff inv0.(Invariant.maydiff) (IdTSet_from_list (l_src ++ l_tgt)) in
  Invariant.mk src tgt maydiff.

Definition ghostify
           (l_src l_tgt:list id)
           (inv0:Invariant.t): Invariant.t :=
  let src := Invariant_ghostify_idTs l_src inv0.(Invariant.src) in
  let tgt := Invariant_ghostify_idTs l_tgt inv0.(Invariant.tgt) in
  let maydiff := ghostify_idTs (l_src ++ l_tgt) inv0.(Invariant.maydiff) in (* TODO: should reduce maydiff *)
  Invariant.mk src tgt maydiff.

Definition reduce_maydiff
           (inv0:Invariant.t): Invariant.t :=
  inv0.

Definition postcond_phinodes_assigns
           (inv0:Invariant.t)
           (assigns_src assigns_tgt:list Phinode.assign): option Invariant.t :=
  let defs_src' := List.map Phinode.get_def assigns_src in
  let defs_tgt' := List.map Phinode.get_def assigns_tgt in
  let uses_src' := filter_map Phinode.get_use assigns_src in
  let uses_tgt' := filter_map Phinode.get_use assigns_tgt in

  let defs_src := List.map (flip IdT.lift Tag.physical) defs_src' in
  let defs_tgt := List.map (flip IdT.lift Tag.physical) defs_tgt' in
  let uses_src := List.map (flip IdT.lift Tag.ghost) uses_src' in
  let uses_tgt := List.map (flip IdT.lift Tag.ghost) uses_tgt' in

  if negb (unique id_dec defs_src' && unique id_dec defs_src')
  then None
  else

  let inv1 := forget uses_src uses_tgt inv0 in
  let inv2 := ghostify uses_src' uses_tgt' inv1 in
  let inv3 := forget defs_src defs_tgt inv2 in
  let inv4 := Invariant.update_maydiff (IdTSet.union (IdTSet_from_list (defs_src ++ defs_tgt))) inv3 in (* Add defs to maydiff *)
  let inv5 := (* Add to src's lessdefs *)
      Invariant.update_src
        (fold_left
           (fun result phi =>
              let (lhs, rhs) := Phinode.get_equation phi in
              Invariant.update_lessdef (ExprPairSet.add (lhs, rhs)) result)
           assigns_src)
        inv4
  in
  let inv6 := (* Add to tgt's lessdefs *)
      Invariant.update_tgt
        (fold_left
           (fun result phi =>
              let (lhs, rhs) := Phinode.get_equation phi in
              Invariant.update_lessdef (ExprPairSet.add (rhs, lhs)) result)
           assigns_src)
        inv5
  in
  let inv7 := reduce_maydiff inv6 in
  Some inv7.

Definition postcond_phinodes
           (inv0:Invariant.t)
           (l_from:l)
           (phinodes_src phinodes_tgt:phinodes): option Invariant.t :=
  match forallb_map (Phinode.resolve l_from) phinodes_src,
        forallb_map (Phinode.resolve l_from) phinodes_tgt with
  | Some assigns_src, Some assigns_tgt =>
    postcond_phinodes_assigns inv0 assigns_src assigns_tgt
  | _, _ => None
  end.

Definition postcond_cmd_inject_event
           (inv:Invariant.t)
           (src tgt:cmd): bool :=
  match src, tgt with
  | insn_call x1 nr1 cl1 t1 va1 v1 p1,
    insn_call x2 nr2 cl2 t2 va2 v2 p2 =>
    noret_dec nr1 nr2 &&
    clattrs_dec cl1 cl2 &&
    typ_dec t1 t2 && 
    varg_dec va1 va2 &&
    Invariant.inject_value inv (ValueT.lift v1 Tag.physical) (ValueT.lift v2 Tag.physical) &&
    list_forallb2
      (fun p1 p2 =>
         let '(ty1, attr1, v1) := p1 in
         let '(ty2, attr2, v2) := p2 in
         typ_dec t1 t2 && 
         attributes_dec attr1 attr2 &&
         Invariant.inject_value inv (ValueT.lift v1 Tag.physical) (ValueT.lift v2 Tag.physical))
      p1 p2
  | insn_call _ _ _ _ _ _ _, _
  | _, insn_call _ _ _ _ _ _ _ => false

  | insn_store _ t1 v1 p1 a1,
    insn_store _ t2 v2 p2 a2 =>
    typ_dec t1 t2 && 
    Invariant.inject_value inv (ValueT.lift v1 Tag.physical) (ValueT.lift v2 Tag.physical)
  | insn_store _ t1 v1 p1 a1, _ => (* TODO: _ should be noop *)
    Invariant.is_private inv.(Invariant.src) (ValueT.lift p1 Tag.physical)
  (* | insn_store _ _ _ _ _, _ *)
  | _, insn_store _ _ _ _ _ => false

  | insn_load x1 t1 v1 a1, insn_load x2 t2 v2 a2 =>
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift v1 Tag.physical) (ValueT.lift v2 Tag.physical) &&
    align_dec a1 a2
  | _, insn_load _ _ _ _ => false

  | insn_free _ t1 p1, insn_free _ t2 p2 =>
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift p1 Tag.physical) (ValueT.lift p2 Tag.physical)
  | insn_free _ _ _, _
  | _, insn_free _ _ _ => false

  | insn_alloca x1 t1 v1 a1, insn_alloca x2 t2 v2 a2 =>
    id_dec x1 x2 &&
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift v1 Tag.physical) (ValueT.lift v2 Tag.physical) &&
    align_dec a1 a2
  | insn_alloca _ _ _ _, _ => true (* TODO: nop *)
  | _, insn_alloca _ _ _ _ => true (* TODO: nop *)
  (* | insn_alloca _ _ _ _, _ => false *)
  (* | _, insn_alloca _ _ _ _ => false *)

  | insn_malloc x1 t1 v1 a1, insn_malloc x2 t2 v2 a2 =>
    id_dec x1 x2 &&
    typ_dec t1 t2 &&
    Invariant.inject_value inv (ValueT.lift v1 Tag.physical) (ValueT.lift v2 Tag.physical) &&
    align_dec a1 a2
  | insn_malloc _ _ _ _, _ => false
  | _, insn_malloc _ _ _ _ => false

  | _, _ => true
  end.

Definition postcond_cmd_update_allocas
           (inv0:Invariant.t)
           (src tgt:cmd): Invariant.t :=
  let inv1 :=
      Invariant.update_src
        (match src with
         | insn_alloca aid _ _ _ => Invariant.update_allocas (IdTSet.add (IdT.lift aid Tag.physical))
         | _ => fun allocas => allocas
         end)
        inv0
  in
  let inv2 :=
      Invariant.update_tgt
        (match tgt with
         | insn_alloca aid _ _ _ => Invariant.update_allocas (IdTSet.add (IdT.lift aid Tag.physical))
         | _ => fun allocas => allocas
         end)
        inv1
  in
  match src, tgt with
  | insn_alloca aid _ _ _, _ => (* TODO: nop *)
    Invariant.update_src (Invariant.update_private (IdTSet.add (IdT.lift aid Tag.physical))) inv2
  | _, insn_alloca aid _ _ _ => (* TODO: nop *)
    Invariant.update_tgt (Invariant.update_private (IdTSet.add (IdT.lift aid Tag.physical))) inv2
  | _, _ => inv2
  end.

Parameter atom_TODO: atom.

Definition postcond_cmd
           (inv0:Invariant.t)
           (src tgt:cmd): option Invariant.t :=
  let def_src := atom_TODO in
  let def_tgt := atom_TODO in
  let uses_src := AtomSetImpl.empty in (* TODO *)
  let uses_tgt := AtomSetImpl.empty in (* TODO *)

  if negb (postcond_cmd_inject_event inv0 src tgt)
  then None
  else
  if AtomSetImpl.mem def_src uses_src || AtomSetImpl.mem def_tgt uses_tgt
  then None
  else

  let inv1 := forget [IdT.lift def_src Tag.physical] [IdT.lift def_tgt Tag.physical] inv0 in
  let inv2 := inv1 in (* TODO: remove lessdef w.r.t. heap *)
  let inv3 := Invariant.update_maydiff (IdTSet.union (IdTSet_from_list [IdT.lift def_src Tag.physical; IdT.lift def_tgt Tag.physical])) inv2 in
  let inv4 := inv3 in (* TODO: add lessdef *)
  let inv5 := postcond_cmd_update_allocas inv4 src tgt in
  let inv6 := reduce_maydiff inv5 in
  Some inv6.
