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
     (options : CoreHint_t.remove_maydiff) 
     (lfdef : LLVMsyntax.fdef) 
     (lnoop : noop_t)
     (rfdef : LLVMsyntax.fdef) 
     (rnoop : noop_t) 
     (left_m : LLVMsyntax.coq_module)
     (right_m : LLVMsyntax.coq_module)
     (fdef_hint : fdef_hint_t)
     dom_tree 
     : fdef_hint_t = 

     let pos = options.position in
     let targetvar = options.variable in
     let id = targetvar.name in
     let block_prev_opt : string option = None (*getBlock 2 args*) in
     let make_infrules insn_hint =
       let lefts = get_rhses_from_insn_hint CoreHint_t.Source (*ParseHints.Original*) id insn_hint in
       let rights = get_rhses_from_insn_hint CoreHint_t.Target (*ParseHints.Optimized*) id insn_hint in
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

