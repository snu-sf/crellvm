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
Require Import TODO.
Require Import Postcond.
Require Import Infrules.

Set Implicit Arguments.

Fixpoint valid_cmds
         (src tgt:list cmd)
         (hint:list (list Infrule.t * Invariant.t))
         (inv0:Invariant.t): option Invariant.t :=
  match hint, src, tgt with
  | (infrules, inv)::hint, cmd_src::src, cmd_tgt::tgt =>
    match postcond_cmd cmd_src cmd_tgt inv0 with
    | None => None
    | Some inv1 =>
      let inv2 := apply_infrules infrules inv1 in
      if Invariant.implies inv2 inv
      then valid_cmds src tgt hint inv
      else None
    end
  | nil, nil, nil => Some inv0
  | _, _, _ => None
  end.

Definition valid_phinodes
           (hint_fdef:Hints.fdef)
           (inv0:Invariant.t)
           (blocks_src blocks_tgt:blocks)
           (l_from l_to:l): bool :=
  match lookupAL _ hint_fdef l_to, lookupAL _ blocks_src l_to, lookupAL _ blocks_tgt l_to with
  | Some hint_stmts, Some (stmts_intro phinodes_src _ _), Some (stmts_intro phinodes_tgt _ _) =>
    match lookupAL _ hint_stmts.(Hints.phinodes) l_from with
    | None => false
    | Some infrules =>
      match postcond_phinodes l_from phinodes_src phinodes_tgt inv0 with
      | None => false
      | Some inv1 =>
        let inv2 := apply_infrules infrules inv1 in
        Invariant.implies inv2 hint_stmts.(Hints.invariant_after_phinodes)
      end
    end
  | _, _, _ => false
  end.

Definition valid_terminator
           (hint_fdef:Hints.fdef)
           (inv0:Invariant.t)
           (blocks_src blocks_tgt:blocks)
           (bid:l)
           (src tgt:terminator): bool :=
  match src, tgt with
  | insn_return_void _, insn_return_void _ => true
  | insn_return _ ty_src val_src, insn_return _ ty_tgt val_tgt =>
    typ_dec ty_src ty_tgt &&
    Invariant.inject_value
      inv0
      (ValueT.lift Tag.physical val_src)
      (ValueT.lift Tag.physical val_tgt)
  | insn_br _ val_src l1_src l2_src, insn_br _ val_tgt l1_tgt l2_tgt =>
    Invariant.inject_value
      inv0
      (ValueT.lift Tag.physical val_src)
      (ValueT.lift Tag.physical val_tgt) &&
    l_dec l1_src l1_tgt &&
    l_dec l2_src l2_tgt &&
    valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l1_src &&
    valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l2_src
  | insn_br_uncond _ l_src, insn_br_uncond _ l_tgt =>
    l_dec l_src l_tgt &&
    valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l_src
  | insn_unreachable _, insn_unreachable _ => true
  | _, _ => false
  end.

Definition valid_stmts
           (hint_fdef:Hints.fdef)
           (hint:Hints.stmts)
           (blocks_src blocks_tgt:blocks)
           (bid:l) (src tgt:stmts): bool :=
  let '(stmts_intro phinodes_src cmds_src terminator_src) := src in
  let '(stmts_intro phinodes_tgt cmds_tgt terminator_tgt) := tgt in
  match valid_cmds cmds_src cmds_tgt hint.(Hints.cmds) hint.(Hints.invariant_after_phinodes) with
  | None => false
  | Some inv => valid_terminator hint_fdef inv blocks_src blocks_tgt bid terminator_src terminator_tgt
  end.

Definition valid_entry_block (src tgt:block): bool :=
  let '(bid_src, stmts_intro phinodes_src _ _) := src in
  let '(bid_tgt, stmts_intro phinodes_tgt _ _) := tgt in
  id_dec bid_src bid_tgt &&
  is_empty phinodes_src &&
  is_empty phinodes_tgt.

Definition valid_fdef
           (src tgt:fdef)
           (hint:Hints.fdef): bool :=
  let '(fdef_intro fheader_src blocks_src) := src in
  let '(fdef_intro fheader_tgt blocks_tgt) := tgt in
  fheader_dec fheader_src fheader_tgt &&
  match blocks_src, blocks_tgt with
  | (bid_src, stmts_intro phinodes_src _ _)::_, (bid_tgt, stmts_intro phinodes_tgt _ _)::_ =>
    id_dec bid_src bid_tgt &&
    is_empty phinodes_src &&
    is_empty phinodes_tgt &&
    match lookupAL _ hint bid_src with
    | None => false
    | Some hint_stmts => Invariant.is_empty hint_stmts.(Hints.invariant_after_phinodes)
    end
  | _, _ => false
  end &&
  forallb2AL
    (fun bid stmts_src stmts_tgt =>
       match lookupAL _ hint bid with
       | Some hint_stmts => valid_stmts hint hint_stmts blocks_src blocks_tgt bid stmts_src stmts_tgt
       | None => false
       end)
    blocks_src blocks_tgt.

Definition valid_product (hint:Hints.products) (src tgt:product): bool :=
  match src, tgt with
  | product_gvar gvar_src, product_gvar gvar_tgt =>
    gvar_dec gvar_src gvar_tgt
  | product_fdec fdec_src, product_fdec fdec_tgt =>
    fdec_dec fdec_src fdec_tgt
  | product_fdef fdef_src, product_fdef fdef_tgt =>
    let fid_src := getFdefID fdef_src in
    let fid_tgt := getFdefID fdef_tgt in
    id_dec fid_src fid_tgt &&
    match lookupAL _ hint fid_src with
    | None => false
    | Some hint_fdef => valid_fdef fdef_src fdef_tgt hint_fdef
    end
  | _, _ =>
    false
  end.

Definition valid_products (hint:Hints.products) (src tgt:products): bool :=
  list_forallb2 (valid_product hint) src tgt.

Definition valid_module (hint:Hints.module) (src tgt:module): bool :=
  let '(module_intro layouts_src namedts_src products_src) := src in
  let '(module_intro layouts_tgt namedts_tgt products_tgt) := tgt in
  layouts_dec layouts_src layouts_tgt &&
  namedts_dec namedts_src namedts_tgt &&
  valid_products hint products_src products_tgt.

Definition valid_modules (hint:Hints.modules) (src tgt:modules): bool :=
  list_forallb3 valid_module hint src tgt.

Definition valid_system (hint:Hints.system) (src tgt:system): bool :=
  valid_modules hint src tgt.