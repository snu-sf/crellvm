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
open HintParser_t


let apply
     (options : HintParser_t.add_assoc) 
     (lfdef : LLVMsyntax.fdef) 
     (lnoop : noop_t)
     (rfdef : LLVMsyntax.fdef) 
     (rnoop : noop_t) 
     (left_m : LLVMsyntax.coq_module)
     (right_m : LLVMsyntax.coq_module)
     (fdef_hint : fdef_hint_t)
     dom_tree 
     : fdef_hint_t = 

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


