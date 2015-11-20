(*********************************)
(* propagate information in hint *)
(*********************************)

open Infrastructure
(* open Interpreter *)
open Printf
open Llvm
open Arg
open Hints
open Syntax
open Syntax_ext
open MetatheoryAtom
open Datatype_base
open Syntax
open BinInt
open BinPos
open Vars_aux
open Validator_aux
open Extraction_defs
open AddInferenceHints
open PropagateHints
open Utility

let is_propagating raw_hint =
  match raw_hint.ParseHints.rhint_type with
  | ParseHints.InstrPropagate
  | ParseHints.Instr2Propagate
  | ParseHints.EqPropagate
  | ParseHints.NeqPropagate
  | ParseHints.StoreEqPropagate
  | ParseHints.AllocaPropagate
  | ParseHints.MaydiffPropagate
  | ParseHints.MaydiffGlobal
  | ParseHints.StashVariable 
  | ParseHints.IsoPropagate1
  | ParseHints.IsoPropagate2
    ->
     true
  | _ ->
     false
(* NOTE: Check here to add a new rule *)

let new_temp_var_count = ref 0
let new_temp_var () =
  let result = "#stash" ^ (string_of_int !new_temp_var_count) in
  let _ = new_temp_var_count := !new_temp_var_count + 1 in
  result

let rec get_orig_idx (n:noop_t) (idx:int) : int =
  if noop_idx_zero_exists n
  then 1+(get_orig_idx (noop_idx_zero_remove n) idx)
  else if idx=0
  then 0
  else 1+(get_orig_idx n (idx-1))

let propagate_micro raw_hint lfdef lnoop rfdef rnoop left_m right_m fdef_hint dom_tree : fdef_hint_t =
  match raw_hint.ParseHints.rhint_type with
  | ParseHints.InstrPropagate ->
     failwith "instr_propagate should have been normalized out."

  | ParseHints.Instr2Propagate ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (lhspos, lhslr, lhs, lhstyp) = getVar 0 args in
     let (rhspos, rhslr, rhs, rhstyp) = getVar 1 args in
     let tpos = getPos 2 args in
     let block_prev_opt = getBlock 3 args in

     let (lhsfdef, lhsnoop) =
       match lhslr with
       | ParseHints.Original -> (lfdef, lnoop)
       | ParseHints.Optimized -> (rfdef, rnoop)
     in
     let (rhsfdef, rhsnoop) =
       match rhslr with
       | ParseHints.Original -> (lfdef, lnoop)
       | ParseHints.Optimized -> (rfdef, rnoop)
     in
     let rhs_bb = fst rhspos in
     let rhs_block =
       match LLVMinfra.lookupBlockViaLabelFromFdef rhsfdef rhs_bb with
       | Some block -> block
       | None -> 
         (match LLVMinfra.lookupBlockViaIDFromFdef rhsfdef rhs with
         | Some block -> snd block
         | None -> 
           try 
             (match rhsfdef with
               Syntax_base.LLVMsyntax_base.Coq_fdef_intro (_,blks) -> 
                 snd (List.nth blks (int_of_string rhs_bb))
             )
           with Failure "int_of_string" -> 
             failwith "propagate_micro instr2_propagate rhs_block")
     in
     let rhs_insn =
       match snd rhspos with
       | ParseHints.CommandPos idx ->
         let rhsnoop = get_noop_by_bb rhs_bb rhsnoop in
         let orig_idx = get_orig_idx rhsnoop idx in
         let cmds = match rhs_block with Syntax_base.LLVMsyntax_base.Coq_stmts_intro (_,cmds,_) -> cmds in
         Syntax_base.LLVMsyntax_base.Coq_insn_cmd (List.nth cmds orig_idx)
       | _ ->
         (match LLVMinfra.lookupInsnViaIDFromFdef rhsfdef rhs with
         | Some insn -> insn
         | None -> failwith "propagate_micro instr2_propagate rhs_insn")
     in         
     let rhs_phivars =
       let LLVMsyntax.Coq_stmts_intro (phinodes, _, _) = rhs_block in
       List.map (fun (LLVMsyntax.Coq_insn_phi (phivar, _, _)) -> phivar) phinodes
     in
     let elt = make_eq_insn lhs rhs_insn rhs_phivars block_prev_opt in
     let fdef_hint =
       propagate
         ~block_prev_opt:block_prev_opt
         lhspos tpos
         (tag_lr lhslr elt)
         lhsfdef fdef_hint dom_tree
     in
     fdef_hint

  | ParseHints.EqPropagate ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let f1 = getVal 0 args in
     let f2 = getVal 1 args in
     let f = getPos 2 args in
     let t = getPos 3 args in
     let block_prev_opt = getBlock 4 args in
     let (fdef, noop) = (lfdef, lnoop) in
     let fdef_hint =
       propagate
         ~block_prev_opt:block_prev_opt
         f t
         (tag_lr ParseHints.Original (make_eq_reg f1 f2))
         fdef fdef_hint dom_tree
     in
     fdef_hint

  | ParseHints.NeqPropagate ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (f1pos, lr, f1, f1typ) = getVar 0 args in
     let (f2pos, _, f2, f2typ) = getVar 1 args in
     let tpos = getPos 2 args in
     let (fdef, noop) =
       match lr with
       | ParseHints.Original -> (lfdef, lnoop)
       | ParseHints.Optimized -> (rfdef, rnoop)
     in
     let fdef_hint = 
       propagate
         f2pos tpos
         (tag_lr lr (make_neq_reg (var2val f1 f1typ) (var2val f2 f2typ)))
         fdef fdef_hint dom_tree
     in
     fdef_hint

  | ParseHints.StoreEqPropagate ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let f1 = getVal 0 args in
     let (rhspos, rhslr, rhs, rhstyp) = getVar 1 args in
     let f = getPos 2 args in
     let t = getPos 3 args in
     let block_prev_opt = getBlock 4 args in
     let (fdef, noop) = (lfdef, lnoop) in
     let f2 = 
       let (rhsfdef, rhsnoop) =
         match rhslr with
         | ParseHints.Original -> (lfdef, lnoop)
         | ParseHints.Optimized -> (rfdef, rnoop)
       in
       let rhs_bb = fst rhspos in
       let rhs_block =
         match LLVMinfra.lookupBlockViaLabelFromFdef rhsfdef rhs_bb with
         | Some block -> block
         | None -> 
             try 
               (match rhsfdef with
                 Syntax_base.LLVMsyntax_base.Coq_fdef_intro (_,blks) -> 
                   snd (List.nth blks (int_of_string rhs_bb))
               )
             with Failure "int_of_string" -> 
               failwith "StoreEqPropagate rhs_block"
       in
       let rhs_insn =
         match snd rhspos with
         | ParseHints.CommandPos idx ->
           let rhsnoop = get_noop_by_bb rhs_bb rhsnoop in
           let orig_idx = get_orig_idx rhsnoop idx in
           let cmds = match rhs_block with Syntax_base.LLVMsyntax_base.Coq_stmts_intro (_,cmds,_) -> cmds in
           Syntax_base.LLVMsyntax_base.Coq_insn_cmd (List.nth cmds orig_idx)
         | _ ->
           (match LLVMinfra.lookupInsnViaIDFromFdef rhsfdef rhs with
           | Some insn -> insn
           | None -> failwith "StoreEqPropagate rhs_insn")
       in         
       match rhs_insn with
       | Syntax_base.LLVMsyntax_base.Coq_insn_cmd 
           (Syntax_base.LLVMsyntax_base.Coq_insn_store (_,_,v,_,_)) -> v
       | _ -> failwith "StoreEqPropagate f2"
     in
     let fdef_hint =
       propagate
         ~block_prev_opt:block_prev_opt
         f t
         (tag_lr ParseHints.Original (make_eq_reg f1 f2))
         fdef fdef_hint dom_tree
     in
     fdef_hint

  | ParseHints.AllocaPropagate ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (f_pos, _, f, _) = getVar 0 args in
     let t_pos = getPos 1 args in
     let (fdef, noop) = (lfdef, lnoop) in
     let fdef_hint =
       propagate
         f_pos t_pos
         (tag_lr ParseHints.Original (make_alloca f))
         fdef fdef_hint dom_tree
     in
     fdef_hint

  | ParseHints.MaydiffPropagate ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (vpos, lr, v, vtyp) = getVar 0 args in
     let fpos = getPos 1 args in
     let tpos = getPos 2 args in
     let (fdef, noop) =
       match lr with
       | ParseHints.Original -> (lfdef, lnoop)
       | ParseHints.Optimized -> (rfdef, rnoop)
     in
     let fdef_hint =
       propagate
         fpos tpos
         (Hint_maydiff (add_ntag v))
         fdef fdef_hint dom_tree
     in
     fdef_hint

  | ParseHints.MaydiffGlobal ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (fpos, lr, f, ftyp) = getVar 0 args in
     let fdef_hint = propagate_maydiff_in_fdef_hint (f, Coq_ntag_old) fdef_hint in
     let fdef_hint = propagate_maydiff_in_fdef_hint (f, Coq_ntag_new) fdef_hint in
     fdef_hint

  | ParseHints.IsoPropagate1 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (vpos, lr, v, vtyp) = getVar 0 args in
     let fpos = getPos 1 args in
     let (fdef, noop) =
       match lr with
       | ParseHints.Original -> (lfdef, lnoop)
       | ParseHints.Optimized -> (rfdef, rnoop)
     in
     let fdef_hint =
       propagate_iso
         fpos
         (Hint_iso_original (add_ntag v))
         fdef fdef_hint dom_tree
     in
     fdef_hint

  | ParseHints.IsoPropagate2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (vpos, lr, v, vtyp) = getVar 0 args in
     let fpos = getPos 1 args in
     let (fdef, noop) =
       match lr with
       | ParseHints.Original -> (lfdef, lnoop)
       | ParseHints.Optimized -> (rfdef, rnoop)
     in
     let fdef_hint =
       propagate_iso
         fpos
         (Hint_iso_optimized (add_ntag v))
         fdef fdef_hint dom_tree
     in
     fdef_hint

  | ParseHints.AddAssoc ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (y_ext, x_ext, sz, c1, c2) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz,
                            Coq_value_ext_id y_ext_0,
                            Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_0, c2))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_1,
                            x_ext,
                            Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_2, c1)))
              when (sz = sz_0 && sz = sz_1 && sz = sz_2 && y_ext = y_ext_0) ->
            (y_ext, x_ext, sz, c1, c2)
         | _, _ -> failwith "add_assoc: pattern matching failed"
       in
       let c3 = INTEGER_OPERATION.add c1 c2 in
       let infrule = Coq_rule_add_assoc (z_ext, y_ext, x_ext, sz, c1, c2, c3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.ReplaceRhs ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let y_value =
         match x_rhs with
         | Coq_rhs_ext_value y_value -> y_value
         | _ -> failwith "replace_rhs y_value"
       in
       let z_rhs' = replace_rhs_ext x_ext y_value z_rhs in
       let infrule = Coq_rule_replace_rhs (z_ext, x_ext, y_value, z_rhs, z_rhs') in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.ReplaceRhsOpt ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Optimized x insn_hint in
       let y_value =
         match x_rhs with
         | Coq_rhs_ext_value y_value -> y_value
         | _ -> failwith "replace_rhs_opt y_value"
       in
       let z_rhs' = replace_rhs_ext x_ext y_value z_rhs in
       let infrule = Coq_rule_replace_rhs_opt (z_ext, x_ext, y_value, z_rhs, z_rhs') in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.ReplaceLhs ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, x, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let y_ext = (y, Coq_ntag_new) in
       let infrule = Coq_rule_replace_lhs (x_ext, y_ext, x_rhs) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.RemoveMaydiff ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, id, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in
     let make_infrules insn_hint =
       let lefts = get_rhses_from_insn_hint ParseHints.Original id insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Optimized id insn_hint in
       let matches = List.append lefts rights in
       let infrules = List.map (fun (id_ext, id_rhs) -> Coq_rule_remove_maydiff (id_ext, id_rhs)) matches in
       infrules
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.EqGenerateSame ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, x, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let infrule = Coq_rule_eq_generate_same (x_ext, y_ext, x_rhs) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.EqGenerateSameHeap ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (pos, _, pos_var, _) = getVar 0 args in
     let (_, _, x, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (x_lhs, typ, align, x_ext) = get_reference_from_insn_hint ParseHints.Original x insn_hint in
       let (_, _, _, y_ext) = get_reference_from_insn_hint ParseHints.Original y insn_hint in
       let infrule = Coq_rule_eq_generate_same_heap (x_ext, y_ext, x_lhs, typ, align) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.EqGenerateSameHeapValue ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (pos, _, pos_var, _) = getVar 0 args in
     let (_, _, x, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (x_lhs, typ, align, x_ext) = get_reference_from_insn_hint ParseHints.Original x insn_hint in
       let (_, _, v_ext) = get_dereference_from_insn_hint_wo_var ParseHints.Original x x_lhs insn_hint in
       let infrule = Coq_rule_eq_generate_same_heap_value (x_ext, x_lhs, v_ext, typ, align) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

 | ParseHints.NeqGenerateGM ->
   let args = List.nth raw_hint.ParseHints.rhint_args 0 in
   let pos = getPos 0 args in
   let (_, _, x, _) = getVar 1 args in
   let (_, _, y, _) = getVar 2 args in
   let block_prev_opt = getBlock 3 args in
   let y_ext = add_ntag y in
   let infrule = Coq_rule_neq_generate_gm (x, y_ext) in
   let make_infrules _ = [infrule] in
   let fdef_hint = add_inference pos block_prev_opt
     make_infrules
     lfdef lnoop rfdef rnoop left_m right_m
     fdef_hint
   in
   fdef_hint

  | ParseHints.AddSignbit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, x, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (sz, lhs, rhs) =
         match x_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz, lhs, rhs) ->
            (sz, lhs, rhs)
         | _ -> failwith "add_signbit: pattern matching failed"
       in
       let infrule = Coq_rule_add_signbit (x_ext, sz, lhs, rhs) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddZextBool ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, x, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let x_insn = get_rhs_from_fdef x lfdef in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (x_ext, b, sz, c) =
         match x_insn, y_rhs with
         | LLVMsyntax.Coq_insn_cmd
           (LLVMsyntax.Coq_insn_ext
              (_, LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int _, b, LLVMsyntax.Coq_typ_int sz)),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_0,
                            Coq_value_ext_id x_ext,
                            Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_1, c)))
              when sz = sz_0 && sz = sz_1 ->
            (x_ext, b, sz, c)
         | _ -> failwith "add_zext_bool: pattern matching failed"
       in
       let c' = INTEGER_OPERATION.add c (INTEGER.of_Z (Size.to_Z sz) (Zpos Coq_xH) true) in
       let infrule = Coq_rule_add_zext_bool (x_ext, y_ext, add_ntag_value b, sz, c, c') in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.PtrTrans ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, p, p_typ) = getVar 1 args in
     let q = getVal 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let p_val = var2val p p_typ in
       let p_val_ext = add_ntag_value p_val in
       let (typ, align, value) = get_dereference_from_insn_hint ParseHints.Original p_val_ext insn_hint in
       let infrule = Coq_rule_ptr_trans (add_ntag p, add_ntag_value q, value, typ, align) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, lhs, rhs) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz, lhs, rhs) ->
            (sz, lhs, rhs)
         | _ -> failwith "add_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_add_onebit (z_ext, lhs, rhs) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.StashVariable ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let (_, _, z, _) = getVar 0 args in
     let pos_f = getPos 1 args in
     let pos_t = getPos 2 args in
     let block_prev_opt = getBlock 3 args in

     let ok = ref true in

     (* 1. stash_variable z into temp(old) *)
     let z_ext = add_ntag z in
     let temp_var = new_temp_var () in
     let temp_var_old = (temp_var, Coq_ntag_old) in
     let infrule = Coq_rule_stash_variable (z_ext, temp_var) in
     let make_infrules insn_hint =
       let is_defined x eqs =
         let eqs =
           EqRegSetImpl.filter
             (fun (lhs, rhs) -> x = lhs)
             eqs
         in
         let result = not (EqRegSetImpl.is_empty eqs) in
         let _ =
           if not result
           then ok := false
           else ()
         in
         result
       in
       if is_defined z_ext (eqs_eq_reg (invariant_original (hint_invariant insn_hint))) &&
          is_defined z_ext (eqs_eq_reg (invariant_original (hint_invariant insn_hint)))
       then [infrule]
       else []
     in
     let fdef_hint = add_inference pos_f None
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in

     if not (!ok)
     then
       let fdef_hint = propagate_maydiff_in_fdef_hint (z, Coq_ntag_old) fdef_hint in
       fdef_hint
     else
       (* 2. propagation of z=temp(old) *)
       let fdef_hint =
         propagate
           ~block_prev_opt:block_prev_opt
           pos_f pos_t
           (tag_lr ParseHints.Original (Eq_reg (temp_var_old, Coq_rhs_ext_value (Coq_value_ext_id z_ext))))
           lfdef fdef_hint dom_tree
       in
       let fdef_hint =
         propagate
           ~block_prev_opt:block_prev_opt
           pos_f pos_t
           (tag_lr ParseHints.Optimized (Eq_reg (temp_var_old, Coq_rhs_ext_value (Coq_value_ext_id z_ext))))
           rfdef fdef_hint dom_tree
       in

       (* 3. propagation of maydiff z(old) *)
       let fdef_hint =
         propagate
           ~block_prev_opt:block_prev_opt
           pos_f pos_t
           (Hint_maydiff (z, Coq_ntag_old))
           lfdef fdef_hint dom_tree
       in

       (* 4. remove_maydiff infrule of z *)
       let infrule = Coq_rule_remove_maydiff_rhs (temp_var_old, (z, Coq_ntag_old)) in
       let make_infrules _ = [infrule] in
       let fdef_hint = add_inference pos_t block_prev_opt
                                     make_infrules
                                     lfdef lnoop rfdef rnoop left_m right_m
                                     fdef_hint
       in

       fdef_hint

  | ParseHints.AddShift ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, y, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (sz, x_ext) =
         match y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz, x_ext, x_ext_0)
             when x_ext = x_ext_0 ->
            (sz, x_ext)
         | _ -> failwith "add_shift: pattern matching failed"
       in
       let infrule = Coq_rule_add_shift (y_ext, sz, x_ext) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddSub ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, minusy, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (minusy_ext, minusy_rhs) = get_rhs_from_insn_hint ParseHints.Original minusy insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       let get_one_infrule (z_ext,z_rhs) =
         match minusy_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, y_ext),
       Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_0, x_ext, (Coq_value_ext_id minusy_ext_0))
         when sz = sz_0 && minusy_ext = minusy_ext_0 ->
           [Coq_rule_add_sub (z_ext, minusy_ext, sz, x_ext, y_ext)]
         | _ -> []
       in
       List.fold_left
         (fun acc (z_ext,z_rhs) -> acc @ get_one_infrule (z_ext,z_rhs))
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddCommutative ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x_ext, y_ext) =
         match z_rhs with
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz, x_ext, y_ext) ->
             (sz, x_ext, y_ext)
         | _ -> failwith "add_commutative: pattern matching failed"
       in
       let infrule = Coq_rule_add_commutative (z_ext, sz, x_ext, y_ext) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubAdd ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, minusy, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (minusy_ext, minusy_rhs) = get_rhs_from_insn_hint ParseHints.Original minusy insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       let get_one_infrule (z_ext,z_rhs) =
         match minusy_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, y_ext),
       Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, x_ext, (Coq_value_ext_id minusy_ext_0))
         when sz = sz_0 && minusy_ext = minusy_ext_0 ->
           [Coq_rule_sub_add (z_ext, minusy_ext, sz, x_ext, y_ext)]
         | _ -> []
       in
       List.fold_left
         (fun acc (z_ext,z_rhs) -> acc @ get_one_infrule (z_ext,z_rhs))
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, lhs, rhs) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, lhs, rhs) ->
            (sz, lhs, rhs)
         | _ -> failwith "sub_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_sub_onebit (z_ext, lhs, rhs) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubMone ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, rhs) ->
            (sz, rhs)
         | _ -> failwith "sub_mone: pattern matching failed"
       in
       let infrule = Coq_rule_sub_mone (z_ext, sz, x) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubConstNot ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, c1, c2) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz, x, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_1, c1)), y)
           when sz = sz_0 && sz = sz_1 ->
           let c2 = INTEGER_OPERATION.add c1 (INTEGER.of_Z (Size.to_Z sz) (Zpos Coq_xH) true) in
            (sz, x, c1, c2)
         | _ -> failwith "sub_const_not: pattern matching failed"
       in
       let infrule = Coq_rule_sub_const_not (z_ext, y_ext, sz, x, c1, c2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddMulFold ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, c1, c2) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz, x, Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_0, c1))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_1, y, x_0)
           when sz = sz_0 && sz = sz_1 && x = x_0 ->
           let c2 = INTEGER_OPERATION.add c1 (INTEGER.of_Z (Size.to_Z sz) (Zpos Coq_xH) true) in
            (sz, x, c1, c2)
         | _ -> failwith "add_mul_fold: pattern matching failed"
       in
       let infrule = Coq_rule_add_mul_fold (z_ext, y_ext, sz, x, c1, c2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddConstNot ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, c1, c2) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz, x, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_0, y, Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_1, c1)))
           when sz = sz_0 && sz = sz_1 ->
           let c2 = INTEGER_OPERATION.sub c1 (INTEGER.of_Z (Size.to_Z sz) (Zpos Coq_xH) true) in
            (sz, x, c1, c2)
         | _ -> failwith "add_const_not: pattern matching failed"
       in
       let infrule = Coq_rule_add_const_not (z_ext, y_ext, sz, x, c1, c2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddSelectZero ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       List.fold_left
       (fun acc (z_ext,z_rhs) ->
         match x_rhs, y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, n, a),
           Coq_rhs_ext_select (c, _, x, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_0, y, a_0)
           when sz = sz_0 && a = a_0 ->
           acc @ [Coq_rule_add_select_zero (z_ext, x_ext, y_ext, c, sz, n, a)]
         | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddSelectZero2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       List.fold_left
       (fun acc (z_ext,z_rhs) ->
         match x_rhs, y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, n, a),
           Coq_rhs_ext_select (c, _, _, x),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_0, y, a_0)
           when sz = sz_0 && a = a_0 ->
           acc @ [Coq_rule_add_select_zero2 (z_ext, x_ext, y_ext, c, sz, n, a)]
         | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubZextBool ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, x, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let x_insn = get_rhs_from_fdef x lfdef in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (x_ext, b, sz, c) =
         match x_insn, y_rhs with
         | LLVMsyntax.Coq_insn_cmd
           (LLVMsyntax.Coq_insn_ext
              (_, LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int _, b, LLVMsyntax.Coq_typ_int sz)),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0,
                            Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_1, c)),
                            Coq_value_ext_id x_ext)
              when sz = sz_0 && sz = sz_1 ->
            (x_ext, b, sz, c)
         | _ -> failwith "sub_zext_bool: pattern matching failed"
       in
       let c' = INTEGER_OPERATION.sub c (INTEGER.of_Z (Size.to_Z sz) (Zpos Coq_xH) true) in
       let infrule = Coq_rule_sub_zext_bool (x_ext, y_ext, add_ntag_value b, sz, c, c') in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubConstAdd ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (sz, x_ext, c1, c2) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz_1,
                            x_ext,
                            Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_2, c1))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz,
                            Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_0, c2)),
                            Coq_value_ext_id y_ext_0)
              when (sz = sz_0 && sz = sz_1 && sz = sz_2 && y_ext = y_ext_0) ->
            (sz, x_ext, c1, c2)
         | _, _ -> failwith "sub_const_add: pattern matching failed"
       in
       let c3 = INTEGER_OPERATION.sub c2 c1 in
       let infrule = Coq_rule_sub_const_add (z_ext, y_ext, sz, x_ext, c1, c2, c3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubRemove ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original y insn_hint in
       List.fold_left
       (fun acc (y_ext,y_rhs) ->
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz, a, b),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, a_0, Coq_value_ext_id y_ext_0)
           when sz = sz_0 && a = a_0 && y_ext = y_ext_0 ->
           acc @ [Coq_rule_sub_remove (z_ext, y_ext, sz, a, b)]
         | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubRemove2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original y insn_hint in
       List.fold_left
       (fun acc (y_ext,y_rhs) ->
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, a, b),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, Coq_value_ext_id y_ext_0, a_0)
           when sz = sz_0 && a = a_0 && y_ext = y_ext_0 ->
           acc @ [Coq_rule_sub_remove2 (z_ext, y_ext, sz, a, b)]
         | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubSdiv ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (sz, x_ext, c) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sdiv, sz_1,
                            x_ext,
                            Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_2, c))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _,
                            Coq_value_ext_id y_ext_0)
              when (sz = sz_1 && sz = sz_2 && y_ext = y_ext_0) ->
            (sz, x_ext, c)
         | _, _ -> failwith "sub_sdiv: pattern matching failed"
       in
       let c' = INTEGER_OPERATION.sub (INTEGER.of_Z (Size.to_Z sz) Z0 true) c in
       let infrule = Coq_rule_sub_sdiv (z_ext, y_ext, sz, x_ext, c, c') in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubShl ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, mx, a) =
         match x_rhs, y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, mx),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_shl, sz_0, Coq_value_ext_id x_ext_0, a),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_1, _, Coq_value_ext_id y_ext_0)
              when (sz = sz_0 && sz = sz_1 && x_ext = x_ext_0 && y_ext = y_ext_0) ->
           (sz, mx, a)
         | _, _, _ -> failwith "sub_shl: pattern matching failed"
       in
       let infrule = Coq_rule_sub_shl (z_ext, x_ext, y_ext, sz, mx, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubMul ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, c) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz, x, Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_0, c))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_1, x_0, Coq_value_ext_id y_ext_0)
           when (sz = sz_0 && sz = sz_1 && x = x_0 && y_ext = y_ext_0) ->
           (sz, x, c)
         | _, _ -> failwith "sub_mul: pattern matching failed"
       in
       let c' = INTEGER_OPERATION.sub (INTEGER.of_Z (Size.to_Z sz) (Zpos Coq_xH) true) c in
       let infrule = Coq_rule_sub_mul (z_ext, y_ext, sz, x, c, c') in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SubMul2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, c) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz, x, Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_0, c))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_1, Coq_value_ext_id y_ext_0, x_0)
           when (sz = sz_0 && sz = sz_1 && x = x_0 && y_ext = y_ext_0) ->
           (sz, x, c)
         | _, _ -> failwith "sub_mul: pattern matching failed"
       in
       let c' = INTEGER_OPERATION.sub c (INTEGER.of_Z (Size.to_Z sz) (Zpos Coq_xH) true) in
       let infrule = Coq_rule_sub_mul2 (z_ext, y_ext, sz, x, c, c') in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.MulMone ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz, x, _) ->
           (sz, x)
         | _ -> failwith "mul_mone: pattern matching failed"
       in
       let infrule = Coq_rule_mul_mone (z_ext, sz, x) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.MulNeg ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, mx, _) = getVar 2 args in
     let (_, _, my, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (mx_ext, mx_rhs) = get_rhs_from_insn_hint ParseHints.Original mx insn_hint in
       let (my_ext, my_rhs) = get_rhs_from_insn_hint ParseHints.Original my insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, y) =
         match mx_rhs, my_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, x),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, _, y),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz_1, Coq_value_ext_id mx_ext_0, Coq_value_ext_id my_ext_0)
           when (sz = sz_0 && sz = sz_1 && mx_ext = mx_ext_0 && my_ext = my_ext_0) ->
           (sz, x, y)
         | _, _, _ -> failwith "mul_neg: pattern matching failed"
       in
       let infrule = Coq_rule_mul_neg (z_ext, mx_ext, my_ext, sz, x, y) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.MulBool ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (x, y) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, _, x, y) -> (x, y)
         | _ -> failwith "mul_bool: pattern matching failed"
       in
       let infrule = Coq_rule_mul_bool (z_ext, x, y) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.MulCommutative ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x_ext, y_ext) =
         match z_rhs with
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz, x_ext, y_ext) ->
             (sz, x_ext, y_ext)
         | _ -> failwith "mul_commutative: pattern matching failed"
       in
       let infrule = Coq_rule_mul_commutative (z_ext, sz, x_ext, y_ext) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.MulShl ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       List.fold_left
       (fun acc (z_ext,z_rhs) ->
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_shl, sz, _, a),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_mul, sz_0, Coq_value_ext_id y_ext_0, x)
           when sz = sz_0 && y_ext = y_ext_0 ->
           acc @ [Coq_rule_mul_shl (z_ext, y_ext, sz, x, a)]
         | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.DivSubSrem ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, b, _) = getVar 2 args in
     let (_, _, a, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (b_ext, b_rhs) = get_rhs_from_insn_hint ParseHints.Original b insn_hint in
       let (a_ext, a_rhs) = get_rhs_from_insn_hint ParseHints.Original a insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, y) =
         match b_rhs, a_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_srem, sz, x, y),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, x_0, Coq_value_ext_id b_ext_0),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sdiv, sz_1, Coq_value_ext_id a_ext_0, y_0)
           when (sz = sz_0 && sz = sz_1 && x = x_0 && y = y_0 && a_ext = a_ext_0 && b_ext = b_ext_0) ->
           (sz, x, y)
         | _, _, _ -> failwith "div_sub_srem: pattern matching failed"
       in
       let infrule = Coq_rule_div_sub_srem (z_ext, b_ext, a_ext, sz, x, y) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.DivSubUrem ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, b, _) = getVar 2 args in
     let (_, _, a, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (b_ext, b_rhs) = get_rhs_from_insn_hint ParseHints.Original b insn_hint in
       let (a_ext, a_rhs) = get_rhs_from_insn_hint ParseHints.Original a insn_hint in
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, y) =
         match b_rhs, a_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_urem, sz, x, y),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz_0, x_0, Coq_value_ext_id b_ext_0),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_udiv, sz_1, Coq_value_ext_id a_ext_0, y_0)
           when (sz = sz_0 && sz = sz_1 && x = x_0 && y = y_0 && a_ext = a_ext_0 && b_ext = b_ext_0) ->
           (sz, x, y)
         | _, _, _ -> failwith "div_sub_urem: pattern matching failed"
       in
       let infrule = Coq_rule_div_sub_urem (z_ext, b_ext, a_ext, sz, x, y) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.DivZext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let (_, _, k, _) = getVar 4 args in
     let block_prev_opt = getBlock 5 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Optimized x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (k_ext, k_rhs) = get_rhs_from_insn_hint ParseHints.Optimized k insn_hint in
       let (sz1, sz2, a, b) =
         match x_rhs, y_rhs, k_rhs, z_rhs with
         | Coq_rhs_ext_ext 
             (LLVMsyntax.Coq_extop_z, 
              LLVMsyntax.Coq_typ_int sz1, a, LLVMsyntax.Coq_typ_int sz2),
           Coq_rhs_ext_ext 
             (LLVMsyntax.Coq_extop_z, 
              LLVMsyntax.Coq_typ_int sz1_0, b, LLVMsyntax.Coq_typ_int sz2_0),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_udiv, sz1_1, a_0, b_0),
           Coq_rhs_ext_ext
             (LLVMsyntax.Coq_extop_z, 
              LLVMsyntax.Coq_typ_int sz1_2, Coq_value_ext_id k_ext_0, 
              LLVMsyntax.Coq_typ_int sz2_1)
             when (sz1 = sz1_0 && sz1 = sz1_1 && sz1 = sz1_2 && 
                 sz2 = sz2_0 && sz2 = sz2_1 && a = a_0 && b = b_0 &&
                 k_ext = k_ext_0) ->
           (sz1, sz2, a, b)
         | _, _, _, _ -> failwith "div_zext: pattern matching failed"
       in
       let infrule = Coq_rule_div_zext (z_ext, x_ext, y_ext, k_ext, sz1, sz2, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.DivMone ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sdiv, sz, x, _) -> (sz, x)
         | _ -> failwith "div_mone: pattern matching failed"
       in
       let infrule = Coq_rule_div_mone (z_ext, sz, x) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.RemZext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let (_, _, k, _) = getVar 4 args in
     let block_prev_opt = getBlock 5 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Optimized x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (k_ext, k_rhs) = get_rhs_from_insn_hint ParseHints.Optimized k insn_hint in
       let (sz1, sz2, a, b) =
         match x_rhs, y_rhs, k_rhs, z_rhs with
         | Coq_rhs_ext_ext 
             (LLVMsyntax.Coq_extop_z, 
              LLVMsyntax.Coq_typ_int sz1, a, LLVMsyntax.Coq_typ_int sz2),
           Coq_rhs_ext_ext 
             (LLVMsyntax.Coq_extop_z, 
              LLVMsyntax.Coq_typ_int sz1_0, b, LLVMsyntax.Coq_typ_int sz2_0),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_urem, sz1_1, a_0, b_0),
           Coq_rhs_ext_ext
             (LLVMsyntax.Coq_extop_z, 
              LLVMsyntax.Coq_typ_int sz1_2, Coq_value_ext_id k_ext_0, 
              LLVMsyntax.Coq_typ_int sz2_1)
             when (sz1 = sz1_0 && sz1 = sz1_1 && sz1 = sz1_2 && 
                 sz2 = sz2_0 && sz2 = sz2_1 && a = a_0 && b = b_0 &&
                 k_ext = k_ext_0) ->
           (sz1, sz2, a, b)
         | _, _, _, _ -> failwith "rem_zext: pattern matching failed"
       in
       let infrule = Coq_rule_rem_zext (z_ext, x_ext, y_ext, k_ext, sz1, sz2, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.RemNeg ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, my, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (my_ext, my_rhs) = get_rhs_from_insn_hint ParseHints.Original my insn_hint in
       let (sz, x, y) =
         match my_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, sz, _, y),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_srem, sz_0, x, (Coq_value_ext_id my_ext_0)) 
             when sz = sz_0 && my_ext = my_ext_0 -> (sz, x, y)
         | _ -> failwith "rem_neg: pattern matching failed"
       in
       let infrule = Coq_rule_rem_neg (z_ext, my_ext, sz, x, y) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.RemNeg2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x, c1, c2) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_srem, sz, x, Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz_0, c1)))
             when sz = sz_0 -> 
           let c2 = INTEGER_OPERATION.sub (INTEGER.of_Z (Size.to_Z sz) Z0 true) c1 in
           (sz, x, c1, c2)
         | _ -> failwith "rem_neg2: pattern matching failed"
       in
       let infrule = Coq_rule_rem_neg2 (z_ext, sz, x, c1, c2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.InboundRemove ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, x, x_typ) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let x_val = var2val x x_typ in
       let x_val_ext = add_ntag_value x_val in
       let (typ, align, v) = get_dereference_from_insn_hint ParseHints.Original x_val_ext insn_hint in
       let (pt,pa,t,a,idx,u,v) =
         match x_rhs, y_rhs with
         | Coq_rhs_ext_gep (true,t,a,idx,u),
           Coq_rhs_ext_gep (false,t_0,a_0,idx_0,u_0)
             when t = t_0 && u = u_0 -> 
           (typ,align,t,a,idx,u,v)
         | _ -> failwith "inbound_remove: pattern matching failed"
       in
       let infrule = Coq_rule_inbound_remove (x_ext, y_ext, pt, pa, t, a, idx, u ,v) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SelectTrunc ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let (_, _, z', _) = getVar 4 args in
     let block_prev_opt = getBlock 5 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Optimized x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (z'_ext, z'_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z' insn_hint in
       let (sz1, sz2, a, b, c) =
         match x_rhs, y_rhs, z'_rhs, z_rhs with
         | Coq_rhs_ext_trunc 
             (LLVMsyntax.Coq_truncop_int, 
              LLVMsyntax.Coq_typ_int sz1, a, LLVMsyntax.Coq_typ_int sz2),
           Coq_rhs_ext_trunc
             (LLVMsyntax.Coq_truncop_int, 
              LLVMsyntax.Coq_typ_int sz1_0, b, LLVMsyntax.Coq_typ_int sz2_0),
           Coq_rhs_ext_select (c, LLVMsyntax.Coq_typ_int sz1_1, a_0, b_0),
           Coq_rhs_ext_trunc
             (LLVMsyntax.Coq_truncop_int, 
              LLVMsyntax.Coq_typ_int sz1_2, Coq_value_ext_id z'_ext_0, LLVMsyntax.Coq_typ_int sz2_1)
             when (sz1 = sz1_0 && sz1 = sz1_1 && sz1 = sz1_2 &&
                 sz2 = sz2_0 && sz2 = sz2_1 && a = a_0 && b = b_0 &&
                 z'_ext = z'_ext_0) ->
           (sz1, sz2, a, b, c)
         | _, _, _, _ -> failwith "select_trunc: pattern matching failed"
       in
       let infrule = Coq_rule_select_trunc (z_ext, x_ext, y_ext, z'_ext, sz1, sz2, a, b, c) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SelectAdd ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let (_, _, z', _) = getVar 4 args in
     let block_prev_opt = getBlock 5 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Optimized x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (z'_ext, z'_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z' insn_hint in
       let (sz1, a, b, c, cond) =
         match x_rhs, y_rhs, z'_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz1, a, b),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz1_0, a_0, c),
           Coq_rhs_ext_select (cond, LLVMsyntax.Coq_typ_int sz1_1, b_0, c_0),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz1_2, a_1, Coq_value_ext_id z'_ext_0)
             when (sz1 = sz1_0 && sz1 = sz1_1 && sz1 = sz1_2 &&
                   z'_ext = z'_ext_0) ->
           (sz1, a, b, c, cond)
         | _, _, _, _ -> failwith "select_add: pattern matching failed"
       in
       let infrule = Coq_rule_select_add (z_ext, x_ext, y_ext, z'_ext, sz1, a, b, c, cond) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SelectConstGt ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, b, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (z1_ext, z1_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (b_ext, b_rhs) = get_rhs_from_insn_hint ParseHints.Original b insn_hint in
       let (b1_ext, b1_rhs) = get_rhs_from_insn_hint ParseHints.Optimized b insn_hint in
       let (sz1, x, c1, c2) =
         match b_rhs, z_rhs, b1_rhs, z1_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_sgt, LLVMsyntax.Coq_typ_int sz1, 
                             x, 
                             Coq_value_ext_const 
                               (LLVMsyntax.Coq_const_int (sz1_2, c1))),
           Coq_rhs_ext_select (Coq_value_ext_id b_ext_2, LLVMsyntax.Coq_typ_int sz1_3,
                               x_2, 
                               Coq_value_ext_const 
                                 (LLVMsyntax.Coq_const_int (sz1_4, c2))),
           Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_slt, LLVMsyntax.Coq_typ_int sz1_5,
                             x_3, 
                             Coq_value_ext_const 
                               (LLVMsyntax.Coq_const_int (sz1_6, c2_2))),
           Coq_rhs_ext_select (Coq_value_ext_id b_ext_3, LLVMsyntax.Coq_typ_int sz1_7,
                               Coq_value_ext_const 
                                 (LLVMsyntax.Coq_const_int (sz1_8, c2_3)),
                               x_4)
             when (sz1 = sz1_2 && sz1 = sz1_3 && sz1 = sz1_4 && sz1 = sz1_5 &&
                 sz1 = sz1_6 && sz1 = sz1_7 && sz1 = sz1_8 &&
                 z_ext = z1_ext && 
                 b_ext = b1_ext && b_ext = b_ext_2 && b_ext = b_ext_3) ->
           (sz1, x, c1, c2)
         | _, _, _, _ -> failwith "select_const_gt: pattern matching failed"
       in
       let infrule = Coq_rule_select_const_gt (z_ext, b_ext, sz1, x, c1, c2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.InboundRemove2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, x, x_typ) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let x_val = var2val x x_typ in
       let x_val_ext = add_ntag_value x_val in
       let (typ, align, v) = get_dereference_from_insn_hint ParseHints.Original x_val_ext insn_hint in
       let (pt,pa,t,a,idx,u,v) =
         match x_rhs, y_rhs with
         | Coq_rhs_ext_gep (false,t,a,idx,u),
           Coq_rhs_ext_gep (true,t_0,a_0,idx_0,u_0)
             when t = t_0 && u = u_0 -> 
           (typ,align,t,a,idx,u,v)
         | _ -> failwith "inbound_remove2: pattern matching failed"
       in
       let infrule = Coq_rule_inbound_remove2 (x_ext, y_ext, pt, pa, t, a, idx, u ,v) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.OrXor ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       List.fold_left
       (fun acc (z_ext,z_rhs) ->
         match y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz1, a, b),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1_0, a_0, Coq_value_ext_id y_ext_0)
             when (sz1 = sz1_0 && y_ext = y_ext_0) ->
           acc @ [Coq_rule_or_xor (z_ext, y_ext, sz1, a, b)]
         | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.OrCommutative ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x_ext, y_ext) =
         match z_rhs with
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz, x_ext, y_ext) ->
             (sz, x_ext, y_ext)
         | _ -> failwith "or_commutative: pattern matching failed"
       in
       let infrule = Coq_rule_or_commutative (z_ext, sz, x_ext, y_ext) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.TruncOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, k, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (k_ext, k_rhs) = get_rhs_from_insn_hint ParseHints.Optimized k insn_hint in
       let (sz1, y) =
         match k_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, y, _),
           Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ne, LLVMsyntax.Coq_typ_int sz1_2,
                             Coq_value_ext_id k_ext_2, _)
             when (sz1 = sz1_2 && k_ext = k_ext_2) ->
           (sz1, y)
         | _, _ -> failwith "trunc_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_trunc_onebit (z_ext, k_ext, sz1, y) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (x, y) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ne, _, x, y) ->
           (x, y)
         | _ -> failwith "cmp_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_onebit (z_ext, x, y) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpEq ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, Coq_value_ext_id y_ext_0, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, a, b) 
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_eq: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_eq (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpUlt ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, _, Coq_value_ext_id y_ext_0, b),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, a, _)
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_ult: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_ult (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.ShiftUndef ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_shl, sz1, _, a) ->
           (sz1, a)
         | _ -> failwith "shift_undef: pattern matching failed"
       in
       let infrule = Coq_rule_shift_undef (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndSame ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, _, a) ->
           (sz1, a)
         | _ -> failwith "and_same: pattern matching failed"
       in
       let infrule = Coq_rule_and_same (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndZero ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, a, _) ->
           (sz1, a)
         | _ -> failwith "and_zero: pattern matching failed"
       in
       let infrule = Coq_rule_and_zero (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndMone ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, a, _) ->
           (sz1, a)
         | _ -> failwith "and_mone: pattern matching failed"
       in
       let infrule = Coq_rule_and_mone (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AddMask ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let (_, _, y', _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (y'_ext, y'_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y' insn_hint in
       let (sz1, x, c1, c2) =
         match y_rhs, y'_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, x, 
                            Coq_value_ext_const 
                              (LLVMsyntax.Coq_const_int (sz1_0, c2))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_add, sz1_1, _, 
                            Coq_value_ext_const 
                              (LLVMsyntax.Coq_const_int (sz1_2, c1))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1_3, 
                            Coq_value_ext_id y'_ext_0, 
                            Coq_value_ext_const 
                              (LLVMsyntax.Coq_const_int (sz1_4, c2_0))) 
             when sz1 = sz1_0 && sz1 = sz1_1 && sz1 = sz1_2 && sz1 = sz1_3 &&
                  sz1 = sz1_4 && y'_ext = y'_ext_0 ->
           (sz1, x, c1, c2)
         | _ -> failwith "add_mask: pattern matching failed"
       in
       let infrule = Coq_rule_add_mask (z_ext, y_ext, y'_ext, sz1, x, c1, c2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndUndef ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, a, _) ->
           (sz1, a)
         | _ -> failwith "and_undef: pattern matching failed"
       in
       let infrule = Coq_rule_and_undef (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndNot ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       List.fold_left
         (fun acc (z_ext,z_rhs) ->
           match z_rhs,y_rhs with
           | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, _, Coq_value_ext_id y_ext_0),
             Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz1_1, x, _)
               when sz1 = sz1_1 && y_ext = y_ext_0 ->
             acc @ [Coq_rule_and_not (z_ext, y_ext, sz1, x)]
           | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndCommutative ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x_ext, y_ext) =
         match z_rhs with
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz, x_ext, y_ext) ->
             (sz, x_ext, y_ext)
         | _ -> failwith "and_commutative: pattern matching failed"
       in
       let infrule = Coq_rule_and_commutative (z_ext, sz, x_ext, y_ext) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndOr ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let rights = get_rhses_from_insn_hint ParseHints.Original y insn_hint in
       let rights2 = get_rhses_from_insn_hint ParseHints.Original z insn_hint in

       List.fold_left
         (fun acc2 (z_ext, z_rhs) ->
           List.fold_left
             (fun acc (y_ext, y_rhs) ->
               match z_rhs,y_rhs with
               | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1, Coq_value_ext_id y_ext_0, x),
             Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1_1, _, a)
               when sz1 = sz1_1 && y_ext = y_ext_0 ->
                 acc @ [Coq_rule_and_or (z_ext, y_ext, sz1, x, a)]
               | _ -> acc)
             acc2 rights
         )
         [] rights2
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndDemorgan ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let (_, _, z', _) = getVar 4 args in
     let block_prev_opt = getBlock 5 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Optimized x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (z'_ext, z'_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z' insn_hint in
       let (sz, a, b) =
         match x_rhs, y_rhs, z'_rhs, z_rhs with
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz, a, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz_0, b, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz_1, _, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz_2, Coq_value_ext_id z'_ext_0, _)
             when sz = sz_0 && sz = sz_1 && sz = sz_2 && z'_ext = z'_ext_0 ->
               (sz, a, b)
         | _ -> failwith "and_demorgan: pattern matching failed"
       in
       let infrule = Coq_rule_and_demorgan (z_ext, x_ext, y_ext, z'_ext, sz, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.AndNotOr ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original y insn_hint in
       let rights2 = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       List.fold_left
         (fun acc2 (z_ext,z_rhs) ->
           List.fold_left
             (fun acc (y_ext,y_rhs) ->
               match x_rhs,y_rhs,z_rhs with
               | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz1, b, _),
             Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1_1, Coq_value_ext_id x_ext_0, a),
             Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1_2, Coq_value_ext_id y_ext_0, _)
               when sz1 = sz1_1 && sz1 = sz1_2 && x_ext = x_ext_0 && y_ext = y_ext_0 ->
                 acc @ [Coq_rule_and_not_or (z_ext, x_ext, y_ext, sz1, a, b)]
               | _ -> acc)
             acc2 rights)
         [] rights2
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.OrUndef ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1, a, _) ->
           (sz1, a)
         | _ -> failwith "or_undef: pattern matching failed"
       in
       let infrule = Coq_rule_or_undef (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.OrSame ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1, _, a) ->
           (sz1, a)
         | _ -> failwith "or_same: pattern matching failed"
       in
       let infrule = Coq_rule_or_same (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.OrZero ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1, a, _) ->
           (sz1, a)
         | _ -> failwith "or_zero: pattern matching failed"
       in
       let infrule = Coq_rule_or_zero (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.OrMone ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1, a, _) ->
           (sz1, a)
         | _ -> failwith "or_mone: pattern matching failed"
       in
       let infrule = Coq_rule_or_mone (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.OrNot ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       List.fold_left
         (fun acc (z_ext,z_rhs) ->
           match z_rhs,y_rhs with
           | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1, _, Coq_value_ext_id y_ext_0),
             Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz1_1, x, _)
               when sz1 = sz1_1 && y_ext = y_ext_0 ->
             acc @ [Coq_rule_or_not (z_ext, y_ext, sz1, x)]
           | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.OrAnd ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let rights = get_rhses_from_insn_hint ParseHints.Original y insn_hint in
       let rights2 = get_rhses_from_insn_hint ParseHints.Original z insn_hint in

       List.fold_left
         (fun acc2 (z_ext, z_rhs) ->
           List.fold_left
             (fun acc (y_ext, y_rhs) ->
               match z_rhs,y_rhs with
               | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, sz1, Coq_value_ext_id y_ext_0, x),
             Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, sz1_1, _, a)
               when sz1 = sz1_1 && y_ext = y_ext_0 ->
                 acc @ [Coq_rule_or_and (z_ext, y_ext, sz1, x, a)]
               | _ -> acc)
             acc2 rights
         )
         [] rights2
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.XorZero ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz1, a, _) ->
           (sz1, a)
         | _ -> failwith "xor_zero: pattern matching failed"
       in
       let infrule = Coq_rule_xor_zero (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.XorSame ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz1, a) =
         match z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz1, _, a) ->
           (sz1, a)
         | _ -> failwith "xor_same: pattern matching failed"
       in
       let infrule = Coq_rule_xor_same (z_ext, sz1, a) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.XorCommutative ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (sz, x_ext, y_ext) =
         match z_rhs with
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz, x_ext, y_ext) ->
             (sz, x_ext, y_ext)
         | _ -> failwith "xor_commutative: pattern matching failed"
       in
       let infrule = Coq_rule_xor_commutative (z_ext, sz, x_ext, y_ext) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.XorNot ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let rights = get_rhses_from_insn_hint ParseHints.Original z insn_hint in
       List.fold_left
         (fun acc (z_ext,z_rhs) ->
           match z_rhs,y_rhs with
           | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz1, _, Coq_value_ext_id y_ext_0),
             Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, sz1_1, x, _)
               when sz1 = sz1_1 && y_ext = y_ext_0 ->
             acc @ [Coq_rule_xor_not (z_ext, y_ext, sz1, x)]
           | _ -> acc)
         [] rights
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.ZextTruncAnd ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let (_, _, x, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (a, sz1, sz2, c) =
         match x_rhs, y_rhs, z_rhs with
         | Coq_rhs_ext_trunc 
             (LLVMsyntax.Coq_truncop_int, 
              LLVMsyntax.Coq_typ_int sz1, 
              a, 
              LLVMsyntax.Coq_typ_int sz2),
           Coq_rhs_ext_bop 
             (LLVMsyntax.Coq_bop_and, 
              sz2_1, 
              Coq_value_ext_id x_ext_1, 
              Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz2_2, c))),
           Coq_rhs_ext_ext 
             (LLVMsyntax.Coq_extop_z, 
              LLVMsyntax.Coq_typ_int sz2_3, 
              Coq_value_ext_id y_ext_1, 
              LLVMsyntax.Coq_typ_int sz1_1)
           when sz1 = sz1_1 && sz2 = sz2_1 && sz2 = sz2_2 && sz2 = sz2_3 &&
                x_ext = x_ext_1 && y_ext = y_ext_1 ->
           (a, sz1, sz2, c)
         | _ -> failwith "zext_trunc_and: pattern matching failed"
       in
       let infrule = Coq_rule_zext_trunc_and (z_ext, y_ext, x_ext, a, sz1, sz2, c) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.ZextTruncAndXor ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let (_, _, x, _) = getVar 3 args in
     let (_, _, w, _) = getVar 4 args in
     let (_, _, w', _) = getVar 5 args in
     let block_prev_opt = getBlock 6 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Optimized x insn_hint in
       let (w_ext, w_rhs) = get_rhs_from_insn_hint ParseHints.Optimized w insn_hint in
       let (w'_ext, w'_rhs) = get_rhs_from_insn_hint ParseHints.Optimized w' insn_hint in
       let (a, sz1, sz2, c) =
         match x_rhs, y_rhs, w_rhs, w'_rhs, z_rhs with
         | Coq_rhs_ext_trunc 
             (LLVMsyntax.Coq_truncop_int, 
              LLVMsyntax.Coq_typ_int sz1, 
              a, 
              LLVMsyntax.Coq_typ_int sz2),
           Coq_rhs_ext_bop 
             (LLVMsyntax.Coq_bop_and, 
              sz2_1, 
              Coq_value_ext_id x_ext_1, 
              Coq_value_ext_const (LLVMsyntax.Coq_const_int (sz2_2, c))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor,sz2_3,Coq_value_ext_id y_ext_1,_),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and,sz1_1,_,_),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor,sz1_2,Coq_value_ext_id w'_ext_1,_)

           when sz1 = sz1_1 && sz1 = sz1_2 && 
                sz2 = sz2_1 && sz2 = sz2_2 && sz2 = sz2_3 &&
                x_ext = x_ext_1 && y_ext = y_ext_1 && w'_ext = w'_ext_1 ->
           (a, sz1, sz2, c)
         | _ -> failwith "zext_trunc_and_xor: pattern matching failed"
       in
       let infrule = Coq_rule_zext_trunc_and_xor (z_ext, y_ext, x_ext, w_ext, w'_ext, a, sz1, sz2, c) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.ZextXor ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let (_, _, y', _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (y'_ext, y'_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y' insn_hint in
       let (a, s) =
         match y_rhs, y'_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, a, _),
           Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_z, _, _, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, s, Coq_value_ext_id y'_ext_1, _)
           when y'_ext = y'_ext_1 ->
           (a, s)
         | _ -> failwith "zext_xor: pattern matching failed"
       in
       let infrule = Coq_rule_zext_xor (z_ext, y_ext, y'_ext, a, s) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SextTrunc ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let (_, _, y', _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (y'_ext, y'_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y' insn_hint in
       let (a, s1, s2, n) =
         match y_rhs, y'_rhs, z_rhs with
         | Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_shl, _, _, Coq_value_ext_const (LLVMsyntax.Coq_const_int (_, n))),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_ashr, _, Coq_value_ext_id y'_ext_1, _)
           when y'_ext = y'_ext_1 ->
           (a, s1, s2, n)
         | _ -> failwith "sext_trunc: pattern matching failed"
       in
       let infrule = Coq_rule_sext_trunc (z_ext, y_ext, y'_ext, a, s1, s2, n) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.TruncTrunc ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2, s3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s3)
           when s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2, s3)
         | _ -> failwith "trunc_trunc: pattern matching failed"
       in
       let infrule = Coq_rule_trunc_trunc (z_ext, y_ext, a, s1, s2, s3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.TruncZext1 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s1_1)
           when s1 = s1_1 && s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2)
         | _ -> failwith "trunc_zext1: pattern matching failed"
       in
       let infrule = Coq_rule_trunc_zext1 (z_ext, y_ext, a, s1, s2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.TruncZext2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2, s3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s3)
           when s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2, s3)
         | _ -> failwith "trunc_zext2: pattern matching failed"
       in
       let infrule = Coq_rule_trunc_zext2 (z_ext, y_ext, a, s1, s2, s3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.TruncZext3 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2, s3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s3)
           when s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2, s3)
         | _ -> failwith "trunc_zext3: pattern matching failed"
       in
       let infrule = Coq_rule_trunc_zext3 (z_ext, y_ext, a, s1, s2, s3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.TruncSext1 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_s, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s1_1)
           when s1 = s1_1 && s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2)
         | _ -> failwith "trunc_sext1: pattern matching failed"
       in
       let infrule = Coq_rule_trunc_sext1 (z_ext, y_ext, a, s1, s2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.TruncSext2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2, s3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_s, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s3)
           when s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2, s3)
         | _ -> failwith "trunc_sext2: pattern matching failed"
       in
       let infrule = Coq_rule_trunc_sext2 (z_ext, y_ext, a, s1, s2, s3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.TruncSext3 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2, s3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_s, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_int, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s3)
           when s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2, s3)
         | _ -> failwith "trunc_sext3: pattern matching failed"
       in
       let infrule = Coq_rule_trunc_sext3 (z_ext, y_ext, a, s1, s2, s3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.ZextZext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2, s3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s3)
           when s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2, s3)
         | _ -> failwith "zext_zext: pattern matching failed"
       in
       let infrule = Coq_rule_zext_zext (z_ext, y_ext, a, s1, s2, s3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SextZext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2, s3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_z, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_s, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s3)
           when s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2, s3)
         | _ -> failwith "sext_zext: pattern matching failed"
       in
       let infrule = Coq_rule_sext_zext (z_ext, y_ext, a, s1, s2, s3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SextSext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, s1, s2, s3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_s, LLVMsyntax.Coq_typ_int s1, a, LLVMsyntax.Coq_typ_int s2),
           Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_s, LLVMsyntax.Coq_typ_int s2_1, Coq_value_ext_id y_ext_1, LLVMsyntax.Coq_typ_int s3)
           when s2 = s2_1 && y_ext = y_ext_1 ->
           (a, s1, s2, s3)
         | _ -> failwith "sext_sext: pattern matching failed"
       in
       let infrule = Coq_rule_sext_sext (z_ext, y_ext, a, s1, s2, s3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.FptouiFpext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, t1, t2, t3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_fp, t1, a, t2),
           Coq_rhs_ext_cast (LLVMsyntax.Coq_castop_fptoui, _, Coq_value_ext_id y_ext_1, t3)
           when y_ext = y_ext_1 ->
           (a, t1, t2, t3)
         | _ -> failwith "fptoui_fpext: pattern matching failed"
       in
       let infrule = Coq_rule_fptoui_fpext (z_ext, y_ext, a, t1, t2, t3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.FptosiFpext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, t1, t2, t3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_fp, t1, a, t2),
           Coq_rhs_ext_cast (LLVMsyntax.Coq_castop_fptosi, _, Coq_value_ext_id y_ext_1, t3)
           when y_ext = y_ext_1 ->
           (a, t1, t2, t3)
         | _ -> failwith "fptosi_fpext: pattern matching failed"
       in
       let infrule = Coq_rule_fptosi_fpext (z_ext, y_ext, a, t1, t2, t3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.UitofpZext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, t1, t2, t3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_z, t1, a, t2),
           Coq_rhs_ext_cast (LLVMsyntax.Coq_castop_uitofp, _, Coq_value_ext_id y_ext_1, t3)
           when y_ext = y_ext_1 ->
           (a, t1, t2, t3)
         | _ -> failwith "uitofp_zext: pattern matching failed"
       in
       let infrule = Coq_rule_uitofp_zext (z_ext, y_ext, a, t1, t2, t3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.SitofpSext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, t1, t2, t3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_s, t1, a, t2),
           Coq_rhs_ext_cast (LLVMsyntax.Coq_castop_sitofp, _, Coq_value_ext_id y_ext_1, t3)
           when y_ext = y_ext_1 ->
           (a, t1, t2, t3)
         | _ -> failwith "sitofp_sext: pattern matching failed"
       in
       let infrule = Coq_rule_sitofp_sext (z_ext, y_ext, a, t1, t2, t3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.FptruncFptrunc ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, t1, t2, t3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_fp, t1, a, t2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_fp, _, Coq_value_ext_id y_ext_1, t3)
           when y_ext = y_ext_1 ->
           (a, t1, t2, t3)
         | _ -> failwith "fptrunc_fptrunc: pattern matching failed"
       in
       let infrule = Coq_rule_fptrunc_fptrunc (z_ext, y_ext, a, t1, t2, t3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.FptruncFpext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, t1, t2) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_fp, t1, a, t2),
           Coq_rhs_ext_trunc (LLVMsyntax.Coq_truncop_fp, _, Coq_value_ext_id y_ext_1, _)
           when y_ext = y_ext_1 ->
           (a, t1, t2)
         | _ -> failwith "fptrunc_fpext: pattern matching failed"
       in
       let infrule = Coq_rule_fptrunc_fpext (z_ext, y_ext, a, t1, t2) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.FpextFpext ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (a, t1, t2, t3) =
         match y_rhs, z_rhs with
         | Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_fp, t1, a, t2),
           Coq_rhs_ext_ext (LLVMsyntax.Coq_extop_fp, _, Coq_value_ext_id y_ext_1, t3)
           when y_ext = y_ext_1 ->
           (a, t1, t2, t3)
         | _ -> failwith "fpext_fpext: pattern matching failed"
       in
       let infrule = Coq_rule_fpext_fpext (z_ext, y_ext, a, t1, t2, t3) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapUlt ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ult, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_ult: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_ult (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapUgt ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ugt, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_ugt: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_ugt (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapUle ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ule, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_ule: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_ule (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapUge ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_uge, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_uge: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_uge (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapSlt ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_slt, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_slt: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_slt (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapSgt ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_sgt, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_sgt: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_sgt (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapSle ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_sle, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_sle: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_sle (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapSge ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_sge, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_sge: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_sge (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapEq ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_eq, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_eq: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_eq (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSwapNe ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let block_prev_opt = getBlock 2 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (a, b, t) =
         match z_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ne, t, a, b)
           -> (a, b, t)
         | _ -> failwith "cmp_swap_ne: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_swap_ne (z_ext, a, b, t) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSltOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, _, Coq_value_ext_id y_ext_0, a),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, b, _)
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_slt_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_slt_onebit (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSgtOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, _, Coq_value_ext_id y_ext_0, b),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, a, _)
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_sgt_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_sgt_onebit (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpUgtOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_and, _, Coq_value_ext_id y_ext_0, a),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, b, _)
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_ugt_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_ugt_onebit (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpUleOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, _, Coq_value_ext_id y_ext_0, b),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, a, _)
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_ule_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_ule_onebit (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpUgeOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, _, Coq_value_ext_id y_ext_0, a),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, b, _)
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_uge_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_uge_onebit (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSleOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, _, Coq_value_ext_id y_ext_0, a),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, b, _)
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_sle_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_sle_onebit (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpSgeOnebit ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Optimized z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Optimized y insn_hint in
       let (a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_or, _, Coq_value_ext_id y_ext_0, b),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, _, a, _)
           when y_ext = y_ext_0 ->
           (a, b)
         | _ -> failwith "cmp_sge_onebit: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_sge_onebit (z_ext, y_ext, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpEqSub ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (s, a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_eq, _, Coq_value_ext_id y_ext_0, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, s, a, b)
           when y_ext = y_ext_0 ->
           (s, a, b)
         | _ -> failwith "cmp_eq_sub: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_eq_sub (z_ext, y_ext, s, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpNeSub ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (s, a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ne, _, Coq_value_ext_id y_ext_0, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_sub, s, a, b)
           when y_ext = y_ext_0 ->
           (s, a, b)
         | _ -> failwith "cmp_ne_sub: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_ne_sub (z_ext, y_ext, s, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpEqSrem ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (s, a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_eq, _, Coq_value_ext_id y_ext_0, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_srem, s, a, b)
           when y_ext = y_ext_0 ->
           (s, a, b)
         | _ -> failwith "cmp_eq_srem: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_eq_srem (z_ext, y_ext, s, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpEqSrem2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (s, a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_eq, _, _, Coq_value_ext_id y_ext_0),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_srem, s, a, b)
           when y_ext = y_ext_0 ->
           (s, a, b)
         | _ -> failwith "cmp_eq_srem2: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_eq_srem2 (z_ext, y_ext, s, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpNeSrem ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (s, a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ne, _, Coq_value_ext_id y_ext_0, _),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_srem, s, a, b)
           when y_ext = y_ext_0 ->
           (s, a, b)
         | _ -> failwith "cmp_ne_srem: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_ne_srem (z_ext, y_ext, s, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpNeSrem2 ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, y, _) = getVar 2 args in
     let block_prev_opt = getBlock 3 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (s, a, b) =
         match z_rhs, y_rhs with
         | Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ne, _, _, Coq_value_ext_id y_ext_0),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_srem, s, a, b)
           when y_ext = y_ext_0 ->
           (s, a, b)
         | _ -> failwith "cmp_ne_srem2: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_ne_srem2 (z_ext, y_ext, s, a, b) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpEqXor ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (s, a, b, c) =
         match x_rhs, y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, s, a, c),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, s_0, b, _),
           Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_eq, (LLVMsyntax.Coq_typ_int s_1), Coq_value_ext_id x_ext_0, Coq_value_ext_id y_ext_0)
           when s = s_0 && s = s_1 && x_ext = x_ext_0 && y_ext = y_ext_0 ->
           (s, a, b, c)
         | _ -> failwith "cmp_eq_xor: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_eq_xor (z_ext, x_ext, y_ext, s, a, b, c) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

  | ParseHints.CmpNeXor ->
     let args = List.nth raw_hint.ParseHints.rhint_args 0 in
     let pos = getPos 0 args in
     let (_, _, z, _) = getVar 1 args in
     let (_, _, x, _) = getVar 2 args in
     let (_, _, y, _) = getVar 3 args in
     let block_prev_opt = getBlock 4 args in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint ParseHints.Original z insn_hint in
       let (x_ext, x_rhs) = get_rhs_from_insn_hint ParseHints.Original x insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint ParseHints.Original y insn_hint in
       let (s, a, b, c) =
         match x_rhs, y_rhs, z_rhs with
         | Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, s, a, c),
           Coq_rhs_ext_bop (LLVMsyntax.Coq_bop_xor, s_0, b, _),
           Coq_rhs_ext_icmp (LLVMsyntax.Coq_cond_ne, (LLVMsyntax.Coq_typ_int s_1), Coq_value_ext_id x_ext_0, Coq_value_ext_id y_ext_0)
           when s = s_0 && s = s_1 && x_ext = x_ext_0 && y_ext = y_ext_0 ->
           (s, a, b, c)
         | _ -> failwith "cmp_ne_xor: pattern matching failed"
       in
       let infrule = Coq_rule_cmp_ne_xor (z_ext, x_ext, y_ext, s, a, b, c) in
       [infrule]
     in
     let fdef_hint = add_inference pos block_prev_opt
                                   make_infrules
                                   lfdef lnoop rfdef rnoop left_m right_m
                                   fdef_hint
     in
     fdef_hint

(* NOTE: Add here to add a new rule *)
