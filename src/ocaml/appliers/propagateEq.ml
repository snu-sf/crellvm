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
open CommandArg


let getInvariant
    (eq_args : CoreHint_t.propagate_eq)
    (args : CommandArg.microhint_args)
    : (PropagateHints.invariant_elt_t * LLVMsyntax.fdef * string option) =

  let v1 : CoreHint_t.value = eq_args.lhs in
  let v2 : CoreHint_t.value = eq_args.rhs in
  let llvm_v1 = PropagateHints.convert_to_LLVMvalue v1 args.lfdef in
  let llvm_v2 = PropagateHints.convert_to_LLVMvalue v2 args.lfdef in
  let block_prev_opt : string option = None (*getBlock 4 args *) in
  (make_eq_reg llvm_v1 llvm_v2), args.lfdef, block_prev_opt

