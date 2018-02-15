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

Require Import Debug.

Set Implicit Arguments.

Parameter gen_infrules_from_insns : insn -> insn -> Assertion.t -> list Infrule.t.
Parameter gen_infrules_next_inv : bool -> Assertion.t -> Assertion.t -> list Infrule.t.

Fixpoint valid_cmds
         (m_src m_tgt:module)
         (src tgt:list cmd)
         (hint:list (list Infrule.t * Assertion.t))
         (inv0:Assertion.t): option Assertion.t :=
  match hint, src, tgt with
  | (infrules, inv)::hint, cmd_src::src, cmd_tgt::tgt =>
    let (cmd_src, cmd_tgt) :=
        (debug_print cmd_pair_printer (cmd_src, cmd_tgt)) in
    if (Assertion.has_false inv0) then valid_cmds m_src m_tgt src tgt hint inv else
    let oinv1 :=
        match postcond_cmd cmd_src cmd_tgt inv0 with
        | Some inv1 => Some inv1
        | None =>
          let infr := gen_infrules_from_insns (insn_cmd cmd_src)
                                              (insn_cmd cmd_tgt)
                                              inv0 in
          let inv0_infr := apply_infrules m_src m_tgt infr inv0 in
          let inv0_infr := debug_print_auto infr inv0_infr in
          postcond_cmd cmd_src cmd_tgt inv0_infr
        end
    in
    match oinv1 with
    | None => failwith_None "valid_cmds: postcond_cmd returned None" nil
    | Some inv1 =>
      let infrules_auto := gen_infrules_next_inv true inv1 inv0 in
      let inv2 := apply_infrules m_src m_tgt (infrules_auto++infrules) inv1 in
      let inv3 := reduce_maydiff inv2 in
      let inv := debug_print_validation_process infrules inv0 inv1 inv2 inv3 inv in
      if
        (if Assertion.implies inv3 inv
         then true
         else
           (* TODO: need new print method *)
           let infrules := gen_infrules_next_inv false inv3 inv in
           let inv3_infr := apply_infrules m_src m_tgt infrules inv3 in
           let inv3_red := reduce_maydiff inv3_infr in
           let inv3_red := debug_print_auto infrules inv3_red in
           Assertion.implies inv3_red inv)
      then valid_cmds m_src m_tgt src tgt hint inv
      else failwith_None "valid_cmds: Assertion.implies returned false" nil
    end
  | nil, nil, nil => Some inv0
  | _, _, _ => None
  end.

Definition lookup_phinodes_infrules hint_stmts l_from :=
  match lookupAL _ hint_stmts.(ValidationHint.phinodes) l_from with
  | None => nil
  | Some infrules => infrules
  end.

Definition valid_phinodes
           (hint_fdef:ValidationHint.fdef)
           (inv0:Assertion.t)
           (m_src m_tgt:module)
           (blocks_src blocks_tgt:blocks)
           (l_from l_to:l): bool :=
  let l_from := (debug_print atom_printer l_from) in
  let l_to := (debug_print atom_printer l_to) in
  match lookupAL _ hint_fdef l_to, lookupAL _ blocks_src l_to, lookupAL _ blocks_tgt l_to with
  | Some hint_stmts, Some (stmts_intro phinodes_src _ _), Some (stmts_intro phinodes_tgt _ _) =>
    let infrules := lookup_phinodes_infrules hint_stmts l_from in
    match postcond_phinodes l_from phinodes_src phinodes_tgt inv0 with
      | None => failwith_false "valid_phinodes: postcond_phinodes returned None at phinode" (l_from::l_to::nil)
      | Some inv1 =>
        let infrules_auto := gen_infrules_next_inv true inv1 inv0 in
        let inv2 := apply_infrules m_src m_tgt (infrules_auto++infrules) inv1 in
        let inv3 := reduce_maydiff inv2 in
        let inv4 := hint_stmts.(ValidationHint.assertion_after_phinodes) in
        let inv4 := debug_print_validation_process infrules inv0 inv1 inv2 inv3 inv4 in
        if negb (Assertion.implies inv3 inv4)
        then
          let infrules := gen_infrules_next_inv false inv3 inv4 in
          let inv3_infr := apply_infrules m_src m_tgt infrules inv3 in
          let inv3_red := reduce_maydiff inv3_infr in
          let inv3_red := debug_print_auto infrules inv3_red in
          if negb (Assertion.implies inv3_red inv4)
          then failwith_false "valid_phinodes: Assertion.implies returned false at phinode" (l_from::l_to::nil)
          else true
        else true
    end
  | _, _, _ => false
  end.

(* TODO: position *)
Lemma const_l_dec (cl1 cl2:const * l):
  {cl1 = cl2} + {cl1 <> cl2}.
Proof.
  decide equality. apply const_dec.
Defined.

(* TODO *)
Require Import sflib.

Lemma list_const_l_dec (cls1 cls2:list (const * l)):
  {cls1 = cls2} + {cls1 <> cls2}.
Proof.
  revert cls2.
  induction cls1; destruct cls2;
    (try by left);
    (try by right).
  decide equality. apply const_l_dec.
Defined.

Definition valid_terminator
           (hint_fdef:ValidationHint.fdef)
           (inv0:Assertion.t)
           (m_src m_tgt:module)
           (blocks_src blocks_tgt:blocks)
           (bid:l)
           (src tgt:terminator): bool :=
  if (Assertion.has_false inv0) then true else
  match src, tgt with
  | insn_return_void _, insn_return_void _ => true
  | insn_return _ ty_src val_src, insn_return _ ty_tgt val_tgt =>
    if negb (typ_dec ty_src ty_tgt)
    then failwith_false "valid_terminator: return type not matched at block" [bid]
    else

    if negb (Assertion.inject_value
               inv0
               (ValueT.lift Tag.physical val_src)
               (ValueT.lift Tag.physical val_tgt))
    then failwith_false "valid_terminator: inject_value of returned values failed at block" [bid]
    else true

  | insn_br _ val_src l1_src l2_src, insn_br _ val_tgt l1_tgt l2_tgt =>
    if negb (Assertion.inject_value
               inv0
               (ValueT.lift Tag.physical val_src)
               (ValueT.lift Tag.physical val_tgt))
    then failwith_false "valid_terminator: inject_value of branch conditions failed at block" [bid]
    else

    if negb (l_dec l1_src l1_tgt)
    then failwith_false "valid_terminator: labels of true branches not matched at block" [bid]
    else

    if negb (l_dec l2_src l2_tgt)
    then failwith_false "valid_terminator: labels of false branches not matched at block" [bid]
    else

    if negb (valid_phinodes hint_fdef (add_terminator_cond inv0 src tgt l1_src) m_src m_tgt blocks_src blocks_tgt bid l1_src)
    then failwith_false "valid_terminator: valid_phinodes of true branches failed at block" [bid]
    else

    if negb (valid_phinodes hint_fdef (add_terminator_cond inv0 src tgt l2_src) m_src m_tgt blocks_src blocks_tgt bid l2_src)
    then failwith_false "valid_terminator: valid_phinodes of false branches failed at block" [bid]
    else true

  | insn_br_uncond _ l_src, insn_br_uncond _ l_tgt =>
    if negb (l_dec l_src l_tgt)
    then failwith_false "valid_terminator: labels of unconditional branches not matched at block" [bid]
    else

    if negb (valid_phinodes hint_fdef (add_terminator_cond inv0 src tgt l_src) m_src m_tgt blocks_src blocks_tgt bid l_src)
    then failwith_false "valid_terminator: valid_phinodes of unconditional branches failed at block" [bid]
    else true

  | insn_switch _ typ_src val_src l0_src ls_src,
    insn_switch _ typ_tgt val_tgt l0_tgt ls_tgt =>
    if negb (typ_dec typ_src typ_tgt)
    then failwith_false "valid_terminator: types of switch conditions failed at block" [bid]
    else

    if negb (Assertion.inject_value
               inv0
               (ValueT.lift Tag.physical val_src)
               (ValueT.lift Tag.physical val_tgt))
    then failwith_false "valid_terminator: value of switch conditions failed at block" [bid]
    else

    if negb (l_dec l0_src l0_tgt)
    then failwith_false "valid_terminator: default labels of switch failed at block" [bid]
    else

    if negb (list_const_l_dec ls_src ls_tgt)
    then failwith_false "valid_terminator: other labels conditions failed at block" [bid]
    else

    if negb (forallb
               (fun cl =>
                  if negb (valid_phinodes hint_fdef (add_terminator_cond inv0 src tgt cl.(snd)) m_src m_tgt blocks_src blocks_tgt bid cl.(snd))
                  then failwith_false "valid_terminator: valid_phinodes of switches failed at block" [bid]
                  else true)
               ls_src)
    then failwith_false "valid_terminator: valid_phinodes failed" [bid]
    else

    if negb (valid_phinodes hint_fdef (add_terminator_cond inv0 src tgt l0_src) m_src m_tgt blocks_src blocks_tgt bid l0_src)
    then failwith_false "valid_terminator: valid_phinodes failed" [bid]
    else true

  | insn_unreachable _, insn_unreachable _ => true
  | _, _ => failwith_false "valid_terminator: types of terminators not matched at block" [bid]
  end.

Definition valid_stmts
           (hint_fdef:ValidationHint.fdef)
           (hint:ValidationHint.stmts)
           (m_src m_tgt:module)
           (blocks_src blocks_tgt:blocks)
           (bid:l) (src tgt:stmts): bool :=
  let '(stmts_intro phinodes_src cmds_src terminator_src) := src in
  let '(stmts_intro phinodes_tgt cmds_tgt terminator_tgt) := tgt in
  match valid_cmds m_src m_tgt cmds_src cmds_tgt hint.(ValidationHint.cmds) hint.(ValidationHint.assertion_after_phinodes) with
  | None => failwith_false "valid_stmts: valid_cmds failed at block" [bid]
  | Some inv =>
    (if (valid_terminator hint_fdef inv m_src m_tgt blocks_src blocks_tgt bid terminator_src terminator_tgt)
     then true
     else
       let infrules := gen_infrules_from_insns
                         (insn_terminator terminator_src)
                         (insn_terminator terminator_tgt)
                         inv in
       let inv' := apply_infrules m_src m_tgt infrules inv in
       let inv' := debug_print_auto infrules inv' in
       (if (valid_terminator hint_fdef inv' m_src m_tgt blocks_src blocks_tgt bid terminator_src terminator_tgt)
        then true
        else failwith_false "valid_stmts: valid_terminator failed at block" [bid]))
  end.

Definition valid_entry_stmts (src tgt:stmts) (hint:ValidationHint.stmts)
                             (la_src la_tgt:args) (products_src products_tgt:products): bool :=
  let '(stmts_intro phinodes_src _ _) := src in
  let '(stmts_intro phinodes_tgt _ _) := tgt in
  if negb (is_empty phinodes_src)
  then failwith_false "valid_entry_stmts: phinode of source not empty" nil
  else
  if negb (is_empty phinodes_tgt)
  then failwith_false "valid_entry_stmts: phinode of target not empty" nil
  else
  if negb (Assertion.implies (Assertion.function_entry_inv la_src la_tgt products_src products_tgt) hint.(ValidationHint.assertion_after_phinodes))
  then failwith_false "valid_entry_stmts: implies fail at function entry" nil
  else true
  .

Definition valid_fdef
           (m_src m_tgt:module)
           (src tgt:fdef)
           (hint:ValidationHint.fdef): bool :=
  let '(fdef_intro fheader_src blocks_src) := src in
  let '(fdef_intro fheader_tgt blocks_tgt) := tgt in
  let '(module_intro layouts_src namedts_src products_src) := m_src in
  let '(module_intro layouts_tgt namedts_tgt products_tgt) := m_tgt in

  let fid_src := getFheaderID fheader_src in
  let fid_tgt :=getFheaderID fheader_tgt in

  if negb (fheader_dec fheader_src fheader_tgt)
  then failwith_false "valid_fdef: function headers not matched at fheaders" (fid_src::fid_tgt::nil)
  else
  match blocks_src, blocks_tgt with
  | (bid_src, block_src)::_, (bid_tgt, block_tgt)::_ =>
    if negb (id_dec bid_src bid_tgt)
    then failwith_false "valid_fdef: entry block ids not matched at bids of" (fid_src::bid_src::bid_tgt::nil)
    else
    match lookupAL _ hint bid_src with
    | Some hint_stmts =>
      if negb (valid_entry_stmts block_src block_tgt hint_stmts (getArgsOfFdef src) (getArgsOfFdef tgt) products_src products_tgt)
      then failwith_false "valid_fdef: valid_entry_stmts failed at" (fid_src::bid_src::nil)
      else true

    | None => failwith_false "valid_fdef: entry block hint not exist at block" (fid_src::bid_src::nil)
    end

  | _, _ => failwith_false "valid_fdef: empty source or target block" (fid_src::nil)
  end &&
  forallb2AL
    (fun bid stmts_src stmts_tgt =>
       match lookupAL _ hint bid with
       | Some hint_stmts =>
         if negb (valid_stmts hint hint_stmts m_src m_tgt blocks_src blocks_tgt bid stmts_src stmts_tgt)
         then failwith_false "valid_fdef: valid_stmts failed at block" (fid_src::bid::nil)
         else true

       | None => failwith_false "valid_fdef: block hint not exist at block" (fid_src::bid::nil)
       end)
    blocks_src blocks_tgt.

Definition valid_product (hint:ValidationHint.products) (m_src m_tgt:module) (src tgt:product): bool :=
  match src, tgt with
  | product_gvar gvar_src, product_gvar gvar_tgt =>
    if negb (Decs.gvar_eqb gvar_src gvar_tgt)
    then failwith_false "valid_product: global variables not matched" ((getGvarID gvar_src)::(getGvarID gvar_tgt)::nil)
    else true
  | product_fdec fdec_src, product_fdec fdec_tgt =>
    if negb (fdec_dec fdec_src fdec_tgt)
    then failwith_false "valid_product: function declarations not matched" ((getFdecID fdec_src)::(getFdecID fdec_tgt)::nil)
    else true
  | product_fdef fdef_src, product_fdef fdef_tgt =>
    let fid_src := getFdefID fdef_src in
    let fid_tgt := getFdefID fdef_tgt in
    if negb (id_dec fid_src fid_tgt)
    then failwith_false "valid_product: function ids not matched" (fid_src::fid_tgt::nil)
    else
    match lookupAL _ hint fid_src with
    | None => failwith_false "valid_product: hint of function not exist" [fid_src]
    | Some hint_fdef =>
      if negb (valid_fdef m_src m_tgt fdef_src fdef_tgt hint_fdef)
      then failwith_false "valid_product: valid_fdef failed" [fid_src]
      else true
    end
  | _, _ =>
    failwith_false "valid_product: source and target product types not matched" nil
  end.

Definition valid_products (hint:ValidationHint.products) (m_src m_tgt:module) (src tgt:products): bool :=
  list_forallb2 (valid_product hint m_src m_tgt) src tgt.

Definition valid_module (hint:ValidationHint.module) (src tgt:module): option bool :=
  let '(module_intro layouts_src namedts_src products_src) := src in
  let '(module_intro layouts_tgt namedts_tgt products_tgt) := tgt in
  if negb (layouts_dec layouts_src layouts_tgt)
  then Some false
  else
  if negb (namedts_dec namedts_src namedts_tgt)
  then Some false
  else
  if negb (valid_products hint src tgt products_src products_tgt)
  then failwith_None "valid_module: valid_products failed" nil
  else Some true.
