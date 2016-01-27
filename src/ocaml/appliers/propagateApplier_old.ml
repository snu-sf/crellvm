(********************************************)
(* applying propagate command to invariants *)
(********************************************)

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
open CoreHint_t


let apply
     (options : CoreHint_t.propagate) 
     (lfdef : LLVMsyntax.fdef) 
     (lnoop : noop_t)
     (rfdef : LLVMsyntax.fdef) 
     (rnoop : noop_t) 
     (left_m : LLVMsyntax.coq_module)
     (right_m : LLVMsyntax.coq_module)
     (fdef_hint : fdef_hint_t)
     dom_tree 
     : fdef_hint_t = 

  let (elt : PropagateHints.invariant_elt_t), (fdef : LLVMsyntax.fdef), (block_prev_opt : string option) = 
       match options.propagate with 
       | CoreHint_t.Instr instr_args ->
	 (*let (lhspos, lhslr, lhs, lhstyp) = getVar 0 args in*)
	 let lhsvar : CoreHint_t.variable = instr_args.lhs in
	 let (lhs) = (lhsvar.name) in
	 (*let (rhspos, rhslr, rhs, rhstyp) = getVar 1 args in*)
	 let rhspos : CoreHint_t.position = instr_args.rhs in
	     
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
	 let rhs_bb : string = rhspos.block_name in
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
	   match rhspos.instr_index with
	   | CoreHint_t.Command idx ->
	     let rhsnoop = get_noop_by_bb rhs_bb rhsnoop in
	     let orig_idx = Utility.get_orig_idx rhsnoop idx in
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
       
       | CoreHint_t.Eq eq_args ->
         let v1 : CoreHint_t.value = eq_args.lhs in
	 let v2 : CoreHint_t.value = eq_args.rhs in
	 let llvm_v1 = PropagateHints.convert_to_LLVMvalue v1 lfdef in
	 let llvm_v2 = PropagateHints.convert_to_LLVMvalue v2 lfdef in
	 let block_prev_opt : string option = None (*getBlock 4 args *) in
	 (make_eq_reg llvm_v1 llvm_v2), lfdef, block_prev_opt
     in
     let propagate_from : CoreHint_t.position = options.propagate_from in
     let propagate_to : CoreHint_t.position = options.propagate_to in
     let fdef_hint =
       propagate
         ~block_prev_opt:block_prev_opt
         propagate_from propagate_to
         (tag_lr (*lhslr // juneyoung lee : we assume that all propagate commands are applied to Source*) CoreHint_t.Source elt)
         fdef fdef_hint dom_tree
     in
     fdef_hint


