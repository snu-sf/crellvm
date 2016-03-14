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

Require Import String.

Set Implicit Arguments.

(* Definition debug_print {A:Type} (printer:A -> unit) (val:A): A := val. *)
(* Definition debug_print_with_msg {A:Type} (printer:A -> unit) (msg:string) (val:A): A := val. *)

Definition debug_print_bool (msg:string) (b:bool): bool := b.
Definition debug_print_option {A:Type} (msg:string) (o:option A): option A := o.

(* (* Definition debug_bool (msg:string) (b:bool): unit := b. *) *)
(* Parameter invariant_printer: Invariant.t -> unit. *)
(* Parameter infrules_printer: list Infrule.t -> unit. *)
(* Parameter string_printer: string -> unit. *)

Definition debug_print_validation_process
           (infrules: list Infrule.t)
           (inv0 inv1 inv2 inv3 inv: Invariant.t): Invariant.t := inv.

Fixpoint valid_cmds
         (src tgt:list cmd)
         (hint:list (list Infrule.t * Invariant.t))
         (inv0:Invariant.t): option Invariant.t :=
  match hint, src, tgt with
  | (infrules, inv)::hint, cmd_src::src, cmd_tgt::tgt =>
    match postcond_cmd cmd_src cmd_tgt inv0 with
    | None => debug_print_option "valid_cmds: postcond_cmd returned None" None
    | Some inv1 =>
      let inv2 := apply_infrules infrules inv1 in
      let inv3 := reduce_maydiff inv2 in
      let inv' := debug_print_validation_process infrules inv0 inv1 inv2 inv3 inv in
      if Invariant.implies inv3 inv'
      then valid_cmds src tgt hint inv'
      else debug_print_option "valid_cmds: Invariant.implies returned false" None
    end
  | nil, nil, nil => Some inv0
  | _, _, _ => None
  end.

Definition valid_phinodes
           (hint_fdef:ValidationHint.fdef)
           (inv0:Invariant.t)
           (blocks_src blocks_tgt:blocks)
           (l_from l_to:l): bool :=
  match lookupAL _ hint_fdef l_to, lookupAL _ blocks_src l_to, lookupAL _ blocks_tgt l_to with
  | Some hint_stmts, Some (stmts_intro phinodes_src _ _), Some (stmts_intro phinodes_tgt _ _) =>
    match lookupAL _ hint_stmts.(ValidationHint.phinodes) l_from with
    | None => debug_print_bool "valid_phinodes: phinode hint not exist" false
    | Some infrules =>
      match postcond_phinodes l_from phinodes_src phinodes_tgt inv0 with
      | None => debug_print_bool "valid_phinodes: postcond_phinodes returned None" false
      | Some inv1 =>
        let inv2 := apply_infrules infrules inv1 in
        let inv3 := reduce_maydiff inv2 in
        let inv := hint_stmts.(ValidationHint.invariant_after_phinodes) in
        let inv' := debug_print_validation_process infrules inv0 inv1 inv2 inv3 inv in
        debug_print_bool "valid_phinodes: Invariant.implies returned false"
                         (Invariant.implies inv3 inv')
      end
    end
  | _, _, _ => false
  end.

Definition valid_terminator
           (hint_fdef:ValidationHint.fdef)
           (inv0:Invariant.t)
           (blocks_src blocks_tgt:blocks)
           (bid:l)
           (src tgt:terminator): bool :=
  match src, tgt with
  | insn_return_void _, insn_return_void _ => true
  | insn_return _ ty_src val_src, insn_return _ ty_tgt val_tgt =>
    debug_print_bool "valid_terminator: return type not matched" (typ_dec ty_src ty_tgt) &&
    debug_print_bool
    "valid_terminator: inject_value of returned values failed"
    (Invariant.inject_value
       inv0
       (ValueT.lift Tag.physical val_src)
       (ValueT.lift Tag.physical val_tgt))
  | insn_br _ val_src l1_src l2_src, insn_br _ val_tgt l1_tgt l2_tgt =>
    debug_print_bool
      "valid_terminator: inject_value of branch conditions failed"
      (Invariant.inject_value
         inv0
         (ValueT.lift Tag.physical val_src)
         (ValueT.lift Tag.physical val_tgt)) &&
    debug_print_bool "valid_terminator: labels of true branches not matched" (l_dec l1_src l1_tgt) &&
    debug_print_bool "valid_terminator: labels of false branches not matched" (l_dec l2_src l2_tgt) &&
    debug_print_bool "valid_terminator: valid_phinodes of true branches failed"
    (valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l1_src) &&
    debug_print_bool "valid_terminator: valid_phinodes of false branches failed"
    (valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l2_src)
  | insn_br_uncond _ l_src, insn_br_uncond _ l_tgt =>
    debug_print_bool "valid_terminator: labels of unconditional branches not matched" (l_dec l_src l_tgt) &&
    debug_print_bool "valid_terminator: valid_phinodes of unconditional branches failed"
    (valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l_src)
  | insn_unreachable _, insn_unreachable _ => true
  | _, _ => debug_print_bool "valid_terminator: types of terminators not matched" false
  end.

Definition valid_stmts
           (hint_fdef:ValidationHint.fdef)
           (hint:ValidationHint.stmts)
           (blocks_src blocks_tgt:blocks)
           (bid:l) (src tgt:stmts): bool :=
  let '(stmts_intro phinodes_src cmds_src terminator_src) := src in
  let '(stmts_intro phinodes_tgt cmds_tgt terminator_tgt) := tgt in
  match valid_cmds cmds_src cmds_tgt hint.(ValidationHint.cmds) hint.(ValidationHint.invariant_after_phinodes) with
  | None => debug_print_bool "valid_stmts: valid_cmds failed" false
  | Some inv => debug_print_bool "valid_stmts: valid_terminator failed"
                           (valid_terminator hint_fdef inv blocks_src blocks_tgt bid terminator_src terminator_tgt)
  end.

Definition valid_entry_stmts (src tgt:stmts) (hint:ValidationHint.stmts): bool :=
  let '(stmts_intro phinodes_src _ _) := src in
  let '(stmts_intro phinodes_tgt _ _) := tgt in
  is_empty phinodes_src &&
  is_empty phinodes_tgt &&

debug_print_bool "valid_entry_stmts: phinode of source not empty" (is_empty phinodes_src) &&
  debug_print_bool "valid_entry_stmts: phinode of target not empty" (is_empty phinodes_tgt) &&
  debug_print_bool "valid_entry_stmts: invariant_after_phinodes of source not empty"
  Invariant.is_empty_unary hint.(ValidationHint.invariant_after_phinodes).(Invariant.src) &&
  debug_print_bool "valid_entry_stmts: invariant_after_phinodes of target not empty"
  Invariant.is_empty_unary hint.(ValidationHint.invariant_after_phinodes).(Invariant.tgt).

Definition valid_fdef
           (src tgt:fdef)
           (hint:ValidationHint.fdef): bool :=
  let '(fdef_intro fheader_src blocks_src) := src in
  let '(fdef_intro fheader_tgt blocks_tgt) := tgt in
  debug_print_bool "valid_fdef: function headers not matched"
             (fheader_dec fheader_src fheader_tgt) &&
  match blocks_src, blocks_tgt with
  | (bid_src, block_src)::_, (bid_tgt, block_tgt)::_ =>
    debug_print_bool "valid_fdef: entry block ids not matched" (id_dec bid_src bid_tgt) &&
    match lookupAL _ hint bid_src with
    | Some hint_stmts => debug_print_bool "valid_fdef: valid_entry_stmts failed"
                                    (valid_entry_stmts block_src block_tgt hint_stmts)
    | None => debug_print_bool "valid_fdef: entry block hint not exist" false
    end
  | _, _ => debug_print_bool "valid_fdef: empty source or target block" false
  end &&
  forallb2AL
    (fun bid stmts_src stmts_tgt =>
       match lookupAL _ hint bid with
       | Some hint_stmts => debug_print_bool "valid_fdef: valid_stmts failed"
                                       (valid_stmts hint hint_stmts blocks_src blocks_tgt bid stmts_src stmts_tgt)
       | None => debug_print_bool "valid_fdef: block hint not exist" false
       end)
    blocks_src blocks_tgt.

Definition valid_product (hint:ValidationHint.products) (src tgt:product): bool :=
  match src, tgt with
  | product_gvar gvar_src, product_gvar gvar_tgt =>
    debug_print_bool "valid_product: global variables not matched" (gvar_dec gvar_src gvar_tgt)
  | product_fdec fdec_src, product_fdec fdec_tgt =>
    debug_print_bool "valid_product: function declarations not matched" (fdec_dec fdec_src fdec_tgt)
  | product_fdef fdef_src, product_fdef fdef_tgt =>
    let fid_src := getFdefID fdef_src in
    let fid_tgt := getFdefID fdef_tgt in
    debug_print_bool "valid_product: function ids not matched" (id_dec fid_src fid_tgt) &&
    match lookupAL _ hint fid_src with
    | None => debug_print_bool "valid_product: hint of current function not exist" false
    | Some hint_fdef =>
      debug_print_bool "valid_product: valid_fdef failed"
                 (valid_fdef fdef_src fdef_tgt hint_fdef)
    end
  | _, _ =>
    debug_print_bool "valid_product: source and target product types not matched" false
  end.

Definition valid_products (hint:ValidationHint.products) (src tgt:products): bool :=
  list_forallb2 (valid_product hint) src tgt.

Definition valid_module (hint:ValidationHint.module) (src tgt:module): bool :=
  let '(module_intro layouts_src namedts_src products_src) := src in
  let '(module_intro layouts_tgt namedts_tgt products_tgt) := tgt in
  debug_print_bool "valid_module: layouts not matched" (layouts_dec layouts_src layouts_tgt) &&
  debug_print_bool "valid_module: named types not matched" (namedts_dec namedts_src namedts_tgt) &&
  debug_print_bool "valid_module: valid_products failed" (valid_products hint products_src products_tgt).

Definition valid_modules (hint:ValidationHint.modules) (src tgt:modules): bool :=
  list_forallb3 valid_module hint src tgt.

Definition valid_system (hint:ValidationHint.system) (src tgt:system): bool :=
  valid_modules hint src tgt.
