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

Definition debug_print (msg:string): bool := false.
Definition debug_print_option {A:Type} (msg:string): option A := None.

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
    | None => debug_print_option "valid_cmds: postcond_cmd returned None"
    | Some inv1 =>
      let inv2 := apply_infrules infrules inv1 in
      let inv3 := reduce_maydiff inv2 in
      let inv := debug_print_validation_process infrules inv0 inv1 inv2 inv3 inv in
      if Invariant.implies inv3 inv
      then valid_cmds src tgt hint inv
      else debug_print_option "valid_cmds: Invariant.implies returned false"
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
    | None => debug_print "valid_phinodes: phinode hint not exist"
    | Some infrules =>
      match postcond_phinodes l_from phinodes_src phinodes_tgt inv0 with
      | None => debug_print "valid_phinodes: postcond_phinodes returned None"
      | Some inv1 =>
        let inv2 := apply_infrules infrules inv1 in
        let inv3 := reduce_maydiff inv2 in
        let inv := hint_stmts.(ValidationHint.invariant_after_phinodes) in
        let inv := debug_print_validation_process infrules inv0 inv1 inv2 inv3 inv in
        if (Invariant.implies inv3 inv)
        then true
        else debug_print "valid_phinodes: Invariant.implies returned false"
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
    if negb (typ_dec ty_src ty_tgt)
    then debug_print "valid_terminator: return type not matched"
    else
    if negb (Invariant.inject_value
               inv0
               (ValueT.lift Tag.physical val_src)
               (ValueT.lift Tag.physical val_tgt))
    then debug_print "valid_terminator: inject_value of returned values failed"
    else true

  | insn_br _ val_src l1_src l2_src, insn_br _ val_tgt l1_tgt l2_tgt =>
    if negb (Invariant.inject_value
               inv0
               (ValueT.lift Tag.physical val_src)
               (ValueT.lift Tag.physical val_tgt))
    then debug_print "valid_terminator: inject_value of branch conditions failed"
    else
    if negb (l_dec l1_src l1_tgt)
    then debug_print "valid_terminator: labels of true branches not matched"
    else
    if negb (l_dec l2_src l2_tgt)
    then debug_print "valid_terminator: labels of false branches not matched"
    else
    if negb (valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l1_src)
    then debug_print "valid_terminator: valid_phinodes of true branches failed"
    else
    if negb (valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l2_src)
    then debug_print "valid_terminator: valid_phinodes of false branches failed"
    else true
    
  | insn_br_uncond _ l_src, insn_br_uncond _ l_tgt =>
    if negb (l_dec l_src l_tgt)
    then debug_print "valid_terminator: labels of unconditional branches not matched"
    else
    if negb (valid_phinodes hint_fdef inv0 blocks_src blocks_tgt bid l_src)
    then debug_print "valid_terminator: valid_phinodes of unconditional branches failed"
    else true
    
  | insn_unreachable _, insn_unreachable _ => true
  | _, _ => debug_print "valid_terminator: types of terminators not matched"
  end.

Definition valid_stmts
           (hint_fdef:ValidationHint.fdef)
           (hint:ValidationHint.stmts)
           (blocks_src blocks_tgt:blocks)
           (bid:l) (src tgt:stmts): bool :=
  let '(stmts_intro phinodes_src cmds_src terminator_src) := src in
  let '(stmts_intro phinodes_tgt cmds_tgt terminator_tgt) := tgt in
  match valid_cmds cmds_src cmds_tgt hint.(ValidationHint.cmds) hint.(ValidationHint.invariant_after_phinodes) with
  | None => debug_print "valid_stmts: valid_cmds failed"
  | Some inv =>
    if negb (valid_terminator hint_fdef inv blocks_src blocks_tgt bid terminator_src terminator_tgt)
    then debug_print "valid_stmts: valid_terminator failed"
    else true              
  end.

Definition valid_entry_stmts (src tgt:stmts) (hint:ValidationHint.stmts): bool :=
  let '(stmts_intro phinodes_src _ _) := src in
  let '(stmts_intro phinodes_tgt _ _) := tgt in
  if negb (is_empty phinodes_src)
  then debug_print "valid_entry_stmts: phinode of source not empty"
  else
  if negb (is_empty phinodes_tgt)
  then debug_print "valid_entry_stmts: phinode of target not empty"
  else
  if negb (Invariant.is_empty_unary hint.(ValidationHint.invariant_after_phinodes).(Invariant.src))
  then debug_print "valid_entry_stmts: invariant_after_phinodes of source not empty"
  else
  if negb (Invariant.is_empty_unary hint.(ValidationHint.invariant_after_phinodes).(Invariant.tgt))
  then debug_print "valid_entry_stmts: invariant_after_phinodes of target not empty"
  else true
  .

Definition valid_fdef
           (src tgt:fdef)
           (hint:ValidationHint.fdef): bool :=
  let '(fdef_intro fheader_src blocks_src) := src in
  let '(fdef_intro fheader_tgt blocks_tgt) := tgt in
  if negb (fheader_dec fheader_src fheader_tgt)
  then debug_print "valid_fdef: function headers not matched"
  else
  match blocks_src, blocks_tgt with
  | (bid_src, block_src)::_, (bid_tgt, block_tgt)::_ =>
    if negb (id_dec bid_src bid_tgt)
    then debug_print "valid_fdef: entry block ids not matched"
    else
    match lookupAL _ hint bid_src with
    | Some hint_stmts =>
      if negb (valid_entry_stmts block_src block_tgt hint_stmts)
      then debug_print "valid_fdef: valid_entry_stmts failed"
      else true
             
    | None => debug_print "valid_fdef: entry block hint not exist"
    end
      
  | _, _ => debug_print "valid_fdef: empty source or target block"
  end &&
  forallb2AL
    (fun bid stmts_src stmts_tgt =>
       match lookupAL _ hint bid with
       | Some hint_stmts =>
         if negb (valid_stmts hint hint_stmts blocks_src blocks_tgt bid stmts_src stmts_tgt)
         then debug_print "valid_fdef: valid_stmts failed"
         else true

       | None => debug_print "valid_fdef: block hint not exist"
       end)
    blocks_src blocks_tgt.

Definition valid_product (hint:ValidationHint.products) (src tgt:product): bool :=
  match src, tgt with
  | product_gvar gvar_src, product_gvar gvar_tgt =>
    if negb (gvar_dec gvar_src gvar_tgt)
    then debug_print "valid_product: global variables not matched"
    else true
  | product_fdec fdec_src, product_fdec fdec_tgt =>
    if negb (fdec_dec fdec_src fdec_tgt)
    then debug_print "valid_product: function declarations not matched"
    else true       
  | product_fdef fdef_src, product_fdef fdef_tgt =>
    let fid_src := getFdefID fdef_src in
    let fid_tgt := getFdefID fdef_tgt in
    if negb (id_dec fid_src fid_tgt)
    then debug_print "valid_product: function ids not matched"
    else 
    match lookupAL _ hint fid_src with
    | None => debug_print "valid_product: hint of current function not exist"
    | Some hint_fdef =>
      if negb (valid_fdef fdef_src fdef_tgt hint_fdef)
      then debug_print "valid_product: valid_fdef failed"
      else true  
    end
  | _, _ =>
    debug_print "valid_product: source and target product types not matched"
  end.

Definition valid_products (hint:ValidationHint.products) (src tgt:products): bool :=
  list_forallb2 (valid_product hint) src tgt.

Definition valid_module (hint:ValidationHint.module) (src tgt:module): bool :=
  let '(module_intro layouts_src namedts_src products_src) := src in
  let '(module_intro layouts_tgt namedts_tgt products_tgt) := tgt in
  if negb (layouts_dec layouts_src layouts_tgt)
  then debug_print "valid_module: layouts not matched"
  else
  if negb (namedts_dec namedts_src namedts_tgt)
  then debug_print "valid_module: named types not matched"
  else
  if negb (valid_products hint products_src products_tgt)
  then debug_print "valid_module: valid_products failed"
  else true.

Definition valid_modules (hint:ValidationHint.modules) (src tgt:modules): bool :=
  list_forallb3 valid_module hint src tgt.

Definition valid_system (hint:ValidationHint.system) (src tgt:system): bool :=
  valid_modules hint src tgt.
