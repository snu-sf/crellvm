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
open HintParser_t

let is_propagating (raw_hint:HintParser_t.command) =
  match raw_hint with 
  | HintParser_t.Propagate _ -> true
  | _ -> false
(*  match raw_hint.ParseHints.rhint_type with
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
*)
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

let propagate_micro 
     (raw_hint : HintParser_t.command) 
     (lfdef : LLVMsyntax.fdef) 
     (lnoop : noop_t)
     (rfdef : LLVMsyntax.fdef) 
     (rnoop : noop_t) 
     (left_m : LLVMsyntax.coq_module)
     (right_m : LLVMsyntax.coq_module)
     (fdef_hint : fdef_hint_t)
     dom_tree 
     : fdef_hint_t =
  match raw_hint with
  | HintParser_t.Propagate (options:HintParser_t.propagate) ->
     let (elt : PropagateHints.invariant_elt_t), (fdef : LLVMsyntax.fdef), (block_prev_opt : string option) = 
       match options.propagate with 
       | HintParser_t.Instr instr_args ->
	 (*let (lhspos, lhslr, lhs, lhstyp) = getVar 0 args in*)
	 let lhsvar : HintParser_t.variable = instr_args.lhs in
	 let (lhs) = (lhsvar.name) in
	 (*let (rhspos, rhslr, rhs, rhstyp) = getVar 1 args in*)
	 let rhspos : HintParser_t.position = instr_args.rhs in
	     
	 (*let tpos = getPos 2 args in*)
	 (*let block_prev_opt = getBlock 3 args in*)
	 let block_prev_opt : string option = None in

	 let (lhsfdef, lhsnoop) =
	   (lfdef, lnoop)
	   (*match lhslr with 
	   | ParseHints.Original -> (lfdef, lnoop)
	   | ParseHints.Optimized -> (rfdef, rnoop)*)
	 in
	 let (rhsfdef, rhsnoop) =
	   (lfdef, lnoop)
	   (*match rhslr with
	   | ParseHints.Original -> (lfdef, lnoop)
	   | ParseHints.Optimized -> (rfdef, rnoop)*)
	 in
	 let rhs_bb : string = rhspos.block_index in
	 let rhs_block =
	   match LLVMinfra.lookupBlockViaLabelFromFdef rhsfdef rhs_bb with
	   | Some block -> block
	   | None -> 
	     (*(match LLVMinfra.lookupBlockViaIDFromFdef rhsfdef rhs with
	     | Some block -> snd block
	     | None -> *)
	       try 
		 (match rhsfdef with
		   Syntax_base.LLVMsyntax_base.Coq_fdef_intro (_,blks) -> 
		     snd (List.nth blks (int_of_string rhs_bb))
		 )
	       with Failure "int_of_string" -> 
		 failwith "propagate_micro instr_propagate rhs_block (juneyoung lee)"
	     (*)*)
	 in
	 let rhs_insn =
	   match rhspos.instr_type with
	   | HintParser_t.Command idx ->
	     let rhsnoop = get_noop_by_bb rhs_bb rhsnoop in
	     let orig_idx = get_orig_idx rhsnoop idx in
	     let cmds = match rhs_block with Syntax_base.LLVMsyntax_base.Coq_stmts_intro (_,cmds,_) -> cmds in
	     Syntax_base.LLVMsyntax_base.Coq_insn_cmd (List.nth cmds orig_idx)
	   | _ ->
	     (*
	     (match LLVMinfra.lookupInsnViaIDFromFdef rhsfdef rhs with
	     | Some insn -> insn
	     | None -> 
	     *)
	     failwith "propagate_micro instr2_propagate rhs_insn (juneyoung lee)"
	     (*)*)
	 in         
	 let rhs_phivars =
	   let LLVMsyntax.Coq_stmts_intro (phinodes, _, _) = rhs_block in
	   List.map (fun (LLVMsyntax.Coq_insn_phi (phivar, _, _)) -> phivar) phinodes
	 in
	 (make_eq_insn lhs rhs_insn rhs_phivars block_prev_opt), lfdef, block_prev_opt
       
       | HintParser_t.Eq eq_args ->
         let v1 : HintParser_t.value = eq_args.lhs in
	 let v2 : HintParser_t.value = eq_args.rhs in
	 let llvm_v1 = PropagateHints.convert_to_LLVMvalue v1 lfdef in
	 let llvm_v2 = PropagateHints.convert_to_LLVMvalue v2 lfdef in
	 let block_prev_opt : string option = None (*getBlock 4 args *) in
	 (make_eq_reg llvm_v1 llvm_v2), lfdef, block_prev_opt
     in
     let propagate_from : HintParser_t.position = options.propagate_from in
     let propagate_to : HintParser_t.position = options.propagate_to in
     let fdef_hint =
       propagate
         ~block_prev_opt:block_prev_opt
         propagate_from propagate_to
         (tag_lr (*lhslr // juneyoung lee : we assume that all propagate commands are applied to Source*) HintParser_t.Source elt)
         fdef fdef_hint dom_tree
     in
     fdef_hint

  | HintParser_t.AddAssoc (options:HintParser_t.add_assoc) ->
     (*
     y = x + 1       y = x + 1
     z = y + 2  ==>  z = x + 3
     "lhs" = z
     "rhs" = y
     *)
     let pos = options.position in
     let lhsvar : HintParser_t.variable = options.lhs (*getVar 1 args*) in
     let rhsvar : HintParser_t.variable = options.rhs (*getVar 2 args*) in
     let z = lhsvar.name in
     let y = rhsvar.name in
     let block_prev_opt : string option = None(*getBlock 3 args*) in

     let make_infrules insn_hint =
       let (z_ext, z_rhs) = get_rhs_from_insn_hint HintParser_t.Source z insn_hint in
       let (y_ext, y_rhs) = get_rhs_from_insn_hint HintParser_t.Source y insn_hint in
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

  | HintParser_t.RemoveMaydiff (options : HintParser_t.remove_maydiff) ->
     let pos = options.position in
     let targetvar = options.variable in
     let id = targetvar.name in
     let block_prev_opt : string option = None (*getBlock 2 args*) in
     let make_infrules insn_hint =
       let lefts = get_rhses_from_insn_hint HintParser_t.Source (*ParseHints.Original*) id insn_hint in
       let rights = get_rhses_from_insn_hint HintParser_t.Target (*ParseHints.Optimized*) id insn_hint in
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

(* NOTE: Add here to add a new rule *)
